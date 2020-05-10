## minbitvec

Minimal bit vector library for Rust

## Usage

```rust
let i = 7 as u8; // 00000111 as bits
let bv = BitVec::from(i);
assert_eq!(bv.data, vec![true, true, true, false, false, false, false, false]);

let v: u8 = bv.read_as();
assert_eq!(i, v);
```
