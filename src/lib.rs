pub struct BitVec {
    data: Vec<bool>,
    pos: usize,
}

#[allow(dead_code)]
impl BitVec {
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            pos: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
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

macro_rules! bitvec_from {
    ($ty:ty) => {
        impl From<$ty> for BitVec {
            fn from(i: $ty) -> Self {
                let size = std::mem::size_of::<$ty>() * 8;
                let mut vec = Vec::with_capacity(size);
                let mut i = i.clone();
                for _ in 1..=size {
                    vec.push(i & 1 == 1);
                    i >>= 1;
                }

                Self { data: vec, pos: 0 }
            }
        }
    };
}

bitvec_from!(u8);
bitvec_from!(u16);
bitvec_from!(u32);
bitvec_from!(u64);
bitvec_from!(usize);

#[cfg(test)]
mod tests {
    use super::BitVec;

    macro_rules! bitvec_from_test {
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
    fn test_u8() {
        bitvec_from_test!(u8);
    }

    #[test]
    fn test_u16() {
        bitvec_from_test!(u16);
    }

    #[test]
    fn test_u32() {
        bitvec_from_test!(u32);
    }

    #[test]
    fn test_u64() {
        bitvec_from_test!(u64);
    }

    #[test]
    fn test_usize() {
        bitvec_from_test!(usize);
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
}
