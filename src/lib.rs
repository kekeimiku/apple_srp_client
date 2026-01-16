use core::{fmt, marker::PhantomData};
use std::sync::LazyLock;

use digest::{Digest, Output};
use num_bigint::BigUint;
use subtle::ConstantTimeEq;

#[derive(Debug)]
pub enum SrpAuthError {
    IllegalParameter(&'static str),
    BadRecordMac(&'static str),
}

impl fmt::Display for SrpAuthError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SrpAuthError::IllegalParameter(param) => {
                write!(f, "illegal_parameter: bad '{param}' value")
            }
            SrpAuthError::BadRecordMac(param) => {
                write!(f, "bad_record_mac: incorrect '{param}'  proof")
            }
        }
    }
}

pub struct SrpGroup {
    pub n: BigUint,
    pub g: BigUint,
}

pub static G_2048: LazyLock<SrpGroup> = LazyLock::new(|| SrpGroup {
    n: BigUint::from_bytes_be(include_bytes!("2048.bin")),
    g: BigUint::from_bytes_be(&[2]),
});

pub fn compute_u<D: Digest>(a_pub: &[u8], b_pub: &[u8]) -> BigUint {
    let mut u = D::new();
    u.update(a_pub);
    u.update(b_pub);
    BigUint::from_bytes_be(&u.finalize())
}

pub fn compute_k<D: Digest>(params: &SrpGroup) -> BigUint {
    let n = params.n.to_bytes_be();
    let g_bytes = params.g.to_bytes_be();
    let mut buf = vec![0u8; n.len()];
    let l = n.len() - g_bytes.len();
    buf[l..].copy_from_slice(&g_bytes);

    let mut d = D::new();
    d.update(&n);
    d.update(&buf);
    BigUint::from_bytes_be(d.finalize().as_slice())
}

pub fn compute_m1<D: Digest>(
    a_pub: &[u8],
    b_pub: &[u8],
    key: &[u8],
    username: &[u8],
    salt: &[u8],
    params: &SrpGroup,
) -> Output<D> {
    let n = params.n.to_bytes_be();
    let g_bytes = params.g.to_bytes_be();

    let mut g = vec![0; n.len() - g_bytes.len()];
    g.extend_from_slice(&g_bytes);

    let mut g_hash = D::digest(&g);
    let n_hash = D::digest(&n);

    for i in 0..g_hash.len() {
        g_hash[i] ^= n_hash[i];
    }

    let mut d = D::new();
    d.update(&g_hash);
    d.update(D::digest(username));
    d.update(salt);
    d.update(a_pub);
    d.update(b_pub);
    d.update(key);
    d.finalize()
}

pub fn compute_m2<D: Digest>(a_pub: &[u8], m1: &Output<D>, key: &[u8]) -> Output<D> {
    let mut d = D::new();
    d.update(a_pub);
    d.update(m1);
    d.update(key);
    d.finalize()
}

pub struct SrpClient<'a, D: Digest> {
    params: &'a SrpGroup,
    d: PhantomData<D>,
}

pub struct SrpClientVerifier<D: Digest> {
    m1: Output<D>,
    m2: Output<D>,
    key: Vec<u8>,
}

impl<'a, D: Digest> SrpClient<'a, D> {
    pub fn new(params: &'a SrpGroup) -> Self {
        Self {
            params,
            d: PhantomData,
        }
    }

    pub fn compute_a_pub(&self, a: &BigUint) -> BigUint {
        self.params.g.modpow(a, &self.params.n)
    }

    pub fn compute_identity_hash(username: &[u8], password: &[u8]) -> Output<D> {
        let mut d = D::new();
        d.update(username);
        d.update(b":");
        d.update(password);
        d.finalize()
    }

    pub fn compute_x(identity_hash: &[u8], salt: &[u8]) -> BigUint {
        let mut x = D::new();
        x.update(salt);
        x.update(identity_hash);
        BigUint::from_bytes_be(&x.finalize())
    }

    pub fn compute_premaster_secret(
        &self,
        b_pub: &BigUint,
        k: &BigUint,
        x: &BigUint,
        a: &BigUint,
        u: &BigUint,
    ) -> BigUint {
        let base = (k * (self.params.g.modpow(x, &self.params.n))) % &self.params.n;
        let base = ((&self.params.n + b_pub) - &base) % &self.params.n;
        let exp = (u * x) + a;
        base.modpow(&exp, &self.params.n)
    }

    pub fn compute_v(&self, x: &BigUint) -> BigUint {
        self.params.g.modpow(x, &self.params.n)
    }

    pub fn compute_verifier(&self, username: &[u8], password: &[u8], salt: &[u8]) -> Vec<u8> {
        let identity_hash = Self::compute_identity_hash(username, password);
        let x = Self::compute_x(identity_hash.as_slice(), salt);
        self.compute_v(&x).to_bytes_be()
    }

    pub fn compute_public_ephemeral(&self, a: &[u8]) -> Vec<u8> {
        self.compute_a_pub(&BigUint::from_bytes_be(a)).to_bytes_be()
    }

    pub fn process_reply(
        &self,
        a: &[u8],
        username: &[u8],
        password: &[u8],
        salt: &[u8],
        b_pub: &[u8],
    ) -> Result<SrpClientVerifier<D>, SrpAuthError> {
        let a = BigUint::from_bytes_be(a);
        let a_pub = self.compute_a_pub(&a);
        let b_pub = BigUint::from_bytes_be(b_pub);

        if &b_pub % &self.params.n == BigUint::default() {
            return Err(SrpAuthError::IllegalParameter("b_pub"));
        }

        let u = compute_u::<D>(&a_pub.to_bytes_be(), &b_pub.to_bytes_be());
        let k = compute_k::<D>(self.params);
        let identity_hash = Self::compute_identity_hash(&[], password);
        let x = Self::compute_x(identity_hash.as_slice(), salt);

        let key = self.compute_premaster_secret(&b_pub, &k, &x, &a, &u);
        let key = D::digest(key.to_bytes_be());

        let m1 = compute_m1::<D>(
            &a_pub.to_bytes_be(),
            &b_pub.to_bytes_be(),
            &key,
            username,
            salt,
            self.params,
        );

        let m2 = compute_m2::<D>(&a_pub.to_bytes_be(), &m1, &key);

        Ok(SrpClientVerifier {
            m1,
            m2,
            key: key.to_vec(),
        })
    }
}

impl<D: Digest> SrpClientVerifier<D> {
    pub fn key(&self) -> &[u8] {
        &self.key
    }

    pub fn proof(&self) -> &[u8] {
        self.m1.as_slice()
    }

    pub fn verify_server(&self, reply: &[u8]) -> Result<(), SrpAuthError> {
        if self.m2.ct_eq(reply).unwrap_u8() != 1 {
            Err(SrpAuthError::BadRecordMac("server"))
        } else {
            Ok(())
        }
    }
}
