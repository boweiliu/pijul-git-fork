pub const MAX_LENGTH: usize = 255;

/// A string of length at most 255, with a more compact on-disk
/// encoding.
#[repr(packed)]
pub struct SmallString {
    pub len: u8,
    pub str: [u8; MAX_LENGTH],
}

/// A borrowed version of `SmallStr`.
#[derive(Clone, Copy)]
pub struct SmallStr<'a> {
    pub p: *const u8,
    pub marker: std::marker::PhantomData<&'a ()>,
}

impl Clone for SmallString {
    fn clone(&self) -> Self {
        Self::from_str(self.as_str())
    }
}

impl std::fmt::Debug for SmallString {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.as_small_str().fmt(fmt)
    }
}

impl<'a> PartialEq for SmallStr<'a> {
    fn eq(&self, x: &SmallStr) -> bool {
        self.as_str().eq(x.as_str())
    }
}

#[test]
fn eq() {
    let s0 = SmallString::from_str("blabla");
    let s1 = SmallString::from_str("blabla");
    assert_eq!(s0, s1);

    assert_eq!(s0, s1);

    assert_eq!(s0.as_small_str(), s1.as_small_str());
    assert_eq!(s0.as_small_str(), s0.as_small_str());
    assert_eq!(s1.as_small_str(), s1.as_small_str());
}

#[test]
fn debug() {
    let s = SmallString::from_str("blabla");
    assert_eq!(format!("{:?}", s), "\"blabla\"");
    assert_eq!(format!("{:?}", s.as_small_str()), "\"blabla\"");
}

impl<'a> Eq for SmallStr<'a> {}

impl PartialEq for SmallString {
    fn eq(&self, x: &SmallString) -> bool {
        self.as_str().eq(x.as_str())
    }
}
impl Eq for SmallString {}
/*
impl<'a> std::hash::Hash for SmallStr<'a> {
fn hash<H: std::hash::Hasher>(&self, x: &mut H) {
self.as_str().hash(x)
}
}
*/
impl std::hash::Hash for SmallString {
    fn hash<H: std::hash::Hasher>(&self, x: &mut H) {
        self.as_str().hash(x)
    }
}

impl<'a> PartialOrd for SmallStr<'a> {
    fn partial_cmp(&self, x: &SmallStr) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(x.as_str())
    }
}
impl<'a> Ord for SmallStr<'a> {
    fn cmp(&self, x: &SmallStr) -> std::cmp::Ordering {
        self.as_str().cmp(x.as_str())
    }
}

impl PartialOrd for SmallString {
    fn partial_cmp(&self, x: &SmallString) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(x.as_str())
    }
}
impl Ord for SmallString {
    fn cmp(&self, x: &SmallString) -> std::cmp::Ordering {
        self.as_str().cmp(x.as_str())
    }
}

#[test]
fn ord() {
    let s0 = SmallString::from_str("1234");
    let s1 = SmallString::from_str("5678");
    assert!(s0.as_small_str() < s1.as_small_str());
    assert!(s0 < s1);
    assert_eq!(s0.cmp(&s1), std::cmp::Ordering::Less);
}

impl<'a> std::fmt::Debug for SmallStr<'a> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.as_str().fmt(fmt)
    }
}

impl Default for SmallString {
    fn default() -> Self {
        Self {
            len: 0,
            str: [0; MAX_LENGTH],
        }
    }
}

impl SmallString {
    pub fn new() -> Self {
        Self::default()
    }
    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("blah!");
    /// assert_eq!(s.len(), s.as_str().len());
    /// ```
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("blah");
    /// s.clear();
    /// assert_eq!(s.as_str(), "");
    /// assert!(s.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn from_str(s: &str) -> Self {
        let mut b = SmallString {
            len: s.len() as u8,
            str: [0; MAX_LENGTH],
        };
        b.clone_from_str(s);
        b
    }
    pub fn clone_from_str(&mut self, s: &str) {
        self.len = s.len() as u8;
        (&mut self.str[..s.len()]).copy_from_slice(s.as_bytes());
    }

    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("blah");
    /// s.clear();
    /// assert!(s.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.len = 0;
    }
    pub fn push_str(&mut self, s: &str) {
        let l = self.len as usize;
        assert!(l + s.len() <= 0xff);
        (&mut self.str[l..l + s.len()]).copy_from_slice(s.as_bytes());
        self.len += s.len() as u8;
    }

    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("blah");
    /// let s_ = s.as_small_str();
    /// let s2_ = s_;
    /// let s3_ = s_.clone();
    /// assert_eq!(s_, s2_);
    /// assert_eq!(s_, s3_);
    /// ```
    pub fn as_small_str(&self) -> SmallStr {
        SmallStr {
            p: self as *const SmallString as *const u8,
            marker: std::marker::PhantomData,
        }
    }

    pub fn as_str(&self) -> &str {
        self.as_small_str().as_str()
    }

    pub fn as_bytes(&self) -> &[u8] {
        self.as_small_str().as_bytes()
    }
}

impl SmallStr<'static> {
    pub const EMPTY: SmallStr<'static> = SmallStr {
        p: [0].as_ptr(),
        marker: std::marker::PhantomData,
    };
}

impl<'a> SmallStr<'a> {
    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("");
    /// assert!(s.as_small_str().is_empty());
    /// s.push_str("blah");
    /// assert!(!s.as_small_str().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// ```ignore
    /// use libpijul::small_string::*;
    /// let mut s = SmallString::from_str("blah");
    /// assert_eq!(s.as_small_str().len(), "blah".len())
    /// ```
    pub fn len(&self) -> usize {
        unsafe { (*self.p) as usize }
    }

    pub fn as_str(&self) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    pub fn as_bytes(&self) -> &'a [u8] {
        unsafe { std::slice::from_raw_parts(self.p.offset(1), *self.p as usize) }
    }

    pub fn to_owned(&self) -> SmallString {
        SmallString::from_str(self.as_str())
    }
}

/// Faster than running doc tests.
#[test]
fn all_doc_tests() {
    {
        let s = SmallString::from_str("blah!");
        assert_eq!(s.len(), s.as_str().len());
    }
    {
        let mut s = SmallString::from_str("blah");
        s.clear();
        assert_eq!(s.as_str(), "");
        assert!(s.is_empty());
    }
    {
        let mut s = SmallString::from_str("blah");
        s.clear();
        assert!(s.is_empty());
    }
    {
        let s = SmallString::from_str("blah");
        let s_ = s.as_small_str();
        let s2_ = s_;
        let s3_ = s_.clone();
        assert_eq!(s_, s2_);
        assert_eq!(s_, s3_);
    }
    {
        let mut s = SmallString::from_str("");
        assert!(s.as_small_str().is_empty());
        s.push_str("blah");
        assert!(!s.as_small_str().is_empty());
    }
    {
        let s = SmallString::from_str("blah");
        assert_eq!(s.as_small_str().len(), "blah".len())
    }
}

/// An internal "unsafe" version of a [`small_string::SmallStr`], used
/// to circumvent the absence of associated type constructors in Rust
/// (else this would be borrow on a table).
#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct UnsafeSmallStr(*const u8);

impl std::fmt::Debug for UnsafeSmallStr {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe { self.to_small_str().fmt(fmt) }
    }
}

impl UnsafeSmallStr {
    pub fn from_small_str(u: SmallStr) -> UnsafeSmallStr {
        UnsafeSmallStr(u.p)
    }
    pub unsafe fn to_small_str<'a>(&self) -> SmallStr<'a> {
        SmallStr {
            p: self.0,
            marker: std::marker::PhantomData,
        }
    }
}

impl sanakirja::Representable for UnsafeSmallStr {
    fn alignment() -> sanakirja::Alignment {
        sanakirja::Alignment::B1
    }
    fn onpage_size(&self) -> u16 {
        unsafe {
            let len = (*self.0) as u16;
            1 + len
        }
    }
    unsafe fn write_value(&self, p: *mut u8) {
        std::ptr::copy(self.0, p, self.onpage_size() as usize)
    }
    unsafe fn read_value(p: *const u8) -> Self {
        UnsafeSmallStr(p)
    }
    unsafe fn cmp_value<T>(&self, _: &T, x: Self) -> std::cmp::Ordering {
        let a = UnsafeSmallStr(self.0).to_small_str();
        let b = x.to_small_str();
        a.as_str().cmp(b.as_str())
    }
    type PageOffsets = std::iter::Empty<u64>;
    fn page_offsets(&self) -> Self::PageOffsets {
        std::iter::empty()
    }
}
