use super::Base32;
use byteorder::{ByteOrder, LittleEndian};

#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash, Serialize, Deserialize)]
#[doc(hidden)]
pub struct ChangeId(pub u64);

impl std::fmt::Debug for ChangeId {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "ChangeId({})", self.to_base32())
    }
}

impl ChangeId {
    pub const ROOT: ChangeId = ChangeId(0);
    pub fn is_root(&self) -> bool {
        *self == ChangeId::ROOT
    }
}

impl super::Base32 for ChangeId {
    fn to_base32(&self) -> String {
        let mut b = [0; 8];
        LittleEndian::write_u64(&mut b, self.0);
        data_encoding::BASE32_NOPAD.encode(&b)
    }
    fn from_base32(b: &[u8]) -> Option<Self> {
        let mut dec = [0; 8];
        let len = if let Ok(len) = data_encoding::BASE32_NOPAD.decode_len(b.len()) {
            len
        } else {
            return None;
        };
        if len > 8 {
            return None;
        }
        if data_encoding::BASE32_NOPAD
            .decode_mut(b, &mut dec[..len])
            .is_ok()
        {
            Some(ChangeId(LittleEndian::read_u64(&dec)))
        } else {
            None
        }
    }
}
