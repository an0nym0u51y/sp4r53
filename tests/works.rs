/**************************************************************************************************
 *                                                                                                *
 * This Source Code Form is subject to the terms of the Mozilla Public                            *
 * License, v. 2.0. If a copy of the MPL was not distributed with this                            *
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.                                       *
 *                                                                                                *
 **************************************************************************************************/

// =========================================== Include ========================================== \\

use sp4r53::*;

// =========================================== #[test] ========================================== \\

#[test]
fn works() {
    let mut tree = Tree::new();
    let mut hashes = [
        blake3::hash(b"foo"),
        blake3::hash(b"bar"),
        blake3::hash(b"baz"),
        blake3::hash(b"foobar"),
        blake3::hash(b"foobaz"),
    ];

    for hash in &hashes {
        assert!(tree.insert(*hash));
    }

    for hash in &hashes {
        assert!(tree.contains(*hash));
    }

    tree.flush();

    let proof = Proof::new(&tree, &hashes[0..3]).unwrap();

    dbg!(&tree);
    dbg!(&proof);

    assert!(proof.verify(tree.root().unwrap()));

    let buf = proof.as_bytes();
    dbg!(buf.len());

    let proof2 = Proof::from_bytes(&buf).unwrap();
    dbg!(&proof2);

    assert!(proof2.verify(tree.root().unwrap()));
}
