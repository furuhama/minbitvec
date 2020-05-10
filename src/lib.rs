pub struct BitVec {
    data: Vec<bool>,
    pos: usize,
}

impl BitVec {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    pub fn push(&mut self, e: bool) {
        self.data.push(e)
    }
}

impl Default for BitVec {
    fn default() -> Self {
        Self {
            data: Vec::new(),
            pos: 0,
        }
    }
}

impl Iterator for BitVec {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos + 1 <= self.len() {
            let ret = Some(self.data[self.pos]);

            self.pos += 1;

            ret
        } else {
            None
        }
    }
}

pub trait ReadAs<T> {
    fn read_as(&self) -> T;
}

// BitVec::from converts unsigned integers into boolean vector.
// A bit order will be reversed at that time.
//
// examples:
//   1u8 -> 00000001
//   BitVec::from::<u8>(1u8) -> vec![true, false, false, false, false, false, false, false]
//
macro_rules! bitvec_from {
    ($ty:ty) => {
        impl From<$ty> for BitVec {
            fn from(i: $ty) -> Self {
                let size = std::mem::size_of::<$ty>() * 8;

                let mut bv = Self::with_capacity(size);
                let mut i = i.clone();

                for _ in 1..=size {
                    bv.push(i & 1 == 1);
                    i >>= 1;
                }

                bv
            }
        }
    };
}

macro_rules! bitvec_read_as {
    ($ty:ty) => {
        impl ReadAs<$ty> for BitVec {
            fn read_as(&self) -> $ty {
                let size = std::mem::size_of::<$ty>() * 8;
                let mut ret = 0 as $ty;
                for i in 1..=size {
                    let idx = size - i;
                    if let Some(e) = self.data.get(idx) {
                        if *e {
                            ret |= 1;
                        }
                    }

                    if i != size {
                        ret <<= 1;
                    }
                }
                ret
            }
        }
    };
}

bitvec_from!(u8);
bitvec_from!(u16);
bitvec_from!(u32);
bitvec_from!(u64);
bitvec_from!(usize);

bitvec_read_as!(u8);
bitvec_read_as!(u16);
bitvec_read_as!(u32);
bitvec_read_as!(u64);
bitvec_read_as!(usize);

#[cfg(test)]
mod tests {
    use crate::{BitVec, ReadAs};

    #[test]
    fn test_with_capacity() {
        assert_eq!(BitVec::with_capacity(10).data.capacity(), 10);
    }

    #[test]
    fn test_capacity() {
        assert_eq!(BitVec::with_capacity(10).capacity(), 10);
    }

    #[test]
    fn test_len() {
        assert_eq!(BitVec::from(1u8).len(), 8);
        assert_eq!(BitVec::from(1u16).len(), 16);
        assert_eq!(BitVec::from(1u32).len(), 32);
        assert_eq!(BitVec::from(1u64).len(), 64);
    }

    macro_rules! from_test {
        ($ty:ty) => {
            let size = std::mem::size_of::<$ty>() * 8;

            let bv = BitVec::from(0 as $ty);
            let vec = vec![false; size];
            assert_eq!(bv.data, vec);

            let bv = BitVec::from(1 as $ty);
            let mut vec = vec![false; size];
            vec[0] = true;
            assert_eq!(bv.data, vec);
        };
    }

    #[test]
    fn test_from_u8() {
        from_test!(u8);
    }

    #[test]
    fn test_from_u16() {
        from_test!(u16);
    }

    #[test]
    fn test_from_u32() {
        from_test!(u32);
    }

    #[test]
    fn test_from_u64() {
        from_test!(u64);
    }

    #[test]
    fn test_from_usize() {
        from_test!(usize);
    }

    #[test]
    fn test_next() {
        let mut bv = BitVec::from(1usize);

        for i in 1..=64 {
            if i == 1 {
                assert!(bv.next().unwrap());
            } else {
                assert!(!bv.next().unwrap());
            }
        }

        assert_eq!(bv.next(), None);
        assert_eq!(bv.next(), None);
    }

    macro_rules! read_as_test {
        ($ty:ty) => {
            let size = std::mem::size_of::<$ty>() * 8;
            let val = 1 as $ty;
            let bv = BitVec::from(val);
            let mut orig_vec = vec![false; size];
            for i in 0..size {
                if bv.data[i] {
                    orig_vec[i] = true;
                }
            }

            let n: $ty = bv.read_as();
            assert_eq!(n, val);
            assert_eq!(bv.data, orig_vec);
        };
    }

    #[test]
    fn test_read_as_u8() {
        read_as_test!(u8);
    }

    #[test]
    fn test_read_as_u16() {
        read_as_test!(u16);
    }

    #[test]
    fn test_read_as_u32() {
        read_as_test!(u32);
    }

    #[test]
    fn test_read_as_u64() {
        read_as_test!(u64);
    }
}
