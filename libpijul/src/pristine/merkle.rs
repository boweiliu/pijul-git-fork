use super::Base32;
use curve25519_dalek::constants::ED25519_BASEPOINT_POINT;

#[doc(hidden)]
#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Merkle {
    Ed25519(curve25519_dalek::edwards::EdwardsPoint),
}

#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum MerkleAlgorithm {
    Ed25519 = 1,
}

impl std::fmt::Debug for Merkle {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "{:?}", self.to_base32())
    }
}

impl Merkle {
    pub fn zero() -> Self {
        Merkle::Ed25519(ED25519_BASEPOINT_POINT)
    }
    pub fn next(&self, h: &super::Hash) -> Self {
        match self {
            Merkle::Ed25519(ref h0) => {
                let scalar = match *h {
                    super::Hash::Blake3(h) => {
                        curve25519_dalek::scalar::Scalar::from_bytes_mod_order(h)
                    }
                    _ => unreachable!(),
                };
                Merkle::Ed25519(h0 * scalar)
            }
        }
    }
    pub fn to_bytes(&self) -> [u8; 32] {
        match *self {
            Merkle::Ed25519(ref e) => e.compress().to_bytes(),
        }
    }
}

impl super::Base32 for Merkle {
    fn to_base32(&self) -> String {
        match *self {
            Merkle::Ed25519(ref s) => {
                let mut hash = [0; 33];
                (&mut hash[..32]).clone_from_slice(s.compress().as_bytes());
                hash[32] = MerkleAlgorithm::Ed25519 as u8;
                data_encoding::BASE32_NOPAD.encode(&hash)
            }
        }
    }

    /// Parses a base-32 string into a `Merkle`.
    fn from_base32(s: &[u8]) -> Option<Self> {
        let bytes = if let Ok(b) = data_encoding::BASE32_NOPAD.decode(s) {
            b
        } else {
            return None;
        };
        if bytes.len() == 33 && *bytes.last().unwrap() == MerkleAlgorithm::Ed25519 as u8 {
            curve25519_dalek::edwards::CompressedEdwardsY::from_slice(&bytes[..32])
                .decompress()
                .map(Merkle::Ed25519)
        } else {
            None
        }
    }
}

impl std::str::FromStr for Merkle {
    type Err = crate::Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(b) = Self::from_base32(s.as_bytes()) {
            Ok(b)
        } else {
            Err(crate::Error::ParseError { s: s.to_string() })
        }
    }
}
