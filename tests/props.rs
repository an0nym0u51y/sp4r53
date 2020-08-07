/**************************************************************************************************
 *                                                                                                *
 * This Source Code Form is subject to the terms of the Mozilla Public                            *
 * License, v. 2.0. If a copy of the MPL was not distributed with this                            *
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.                                       *
 *                                                                                                *
 **************************************************************************************************/

// =========================================== Imports ========================================== \\

use proptest::strategy::{Strategy, ValueTree};
use proptest::test_runner::{TestCaseError, TestRunner};
use proptest::{array, collection, prop_assert};
use sp4r53::{Proof, Tree};

// =========================================== #[test] ========================================== \\

#[test]
fn prop_works() -> Result<(), TestCaseError> {
    let mut runner = TestRunner::default();
    let hash = array::uniform32(u8::MIN..=u8::MAX).prop_map_into::<blake3::Hash>();
    let leaves = collection::vec(hash, 0..16384)
        .new_tree(&mut runner)
        .unwrap();

    let mut tree = Tree::default();
    let leaves = leaves.current();

    for leaf in leaves.iter().copied() {
        tree.insert(leaf);
        prop_assert!(tree.contains(leaf));
        prop_assert!(!tree.is_valid());

        tree.flush();
        prop_assert!(tree.is_valid());
    }

    assert_eq!(tree.leaves(), leaves.len());

    let proof_leaves = (0..leaves.len()).new_tree(&mut runner).unwrap().current();
    let proof = Proof::new(&tree, &leaves[0..proof_leaves]).unwrap();
    prop_assert!(proof.verify(tree.root().unwrap()));

    let proof_bytes = proof.as_bytes();
    dbg!(proof_leaves, &proof_bytes.len());

    let proof = Proof::from_bytes(&proof_bytes).unwrap();
    prop_assert!(proof.verify(tree.root().unwrap()));

    for leaf in leaves.iter().copied() {
        prop_assert!(tree.contains(leaf));
        prop_assert!(tree.remove(leaf));
        prop_assert!(!tree.contains(leaf));
        prop_assert!(!tree.is_valid());

        tree.flush();
        prop_assert!(tree.is_valid());
    }

    Ok(())
}
