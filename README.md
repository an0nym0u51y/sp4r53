[![img](https://img.shields.io/crates/l/sp4r53.svg)](https://github.com/r3v2d0g/sp4r53/blob/main/LICENSE.txt) [![img](https://img.shields.io/crates/v/sp4r53.svg)](https://crates.io/crates/sp4r53) [![img](https://docs.rs/sp4r53/badge.svg)](https://docs.rs/sp4r53)

A sparse Merkle tree implementation that only recomputes its branches&rsquo; hashes when asked.


# Example

```rust
use sp4r53::{blake3, Proof, Tree};

let foo = blake3::hash(b"foo");
let bar = blake3::hash(b"bar");
let baz = blake3::hash(b"baz");

let mut tree = Tree::new();

tree.insert(foo);
tree.insert(bar);
tree.insert(baz);
assert_eq!(tree.is_valid(), false);

let root = tree.flush();
assert_eq!(tree.is_valid(), true);
assert_eq!(tree.root(), Some(root));

let proof = tree.proove(&[foo, baz]).unwrap();
assert_eq!(proof.verify(root), true);

let encoded = proof.as_bytes();
let decoded = Proof::from_bytes(&encoded).unwrap();
assert_eq!(decoded, proof);

tree.remove(bar);

let root = tree.flush();
assert_eq!(proof.verify(root), false);
```


# About


## License

> This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0. If a copy of the MPL was not distributed with this file, You can obtain one at <http://mozilla.org/MPL/2.0/>.
