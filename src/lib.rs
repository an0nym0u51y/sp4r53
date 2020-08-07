/**************************************************************************************************
 *                                                                                                *
 * This Source Code Form is subject to the terms of the Mozilla Public                            *
 * License, v. 2.0. If a copy of the MPL was not distributed with this                            *
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.                                       *
 *                                                                                                *
 **************************************************************************************************/

// =========================================== Imports ========================================== \\

use blake3::{Hash, Hasher};
use core::convert::TryFrom;
use core::iter::FromIterator;
use core::ops::{Index, IndexMut};
use core::{cmp, mem};
use ethnum::U256;

#[cfg(feature = "thiserror")]
use thiserror::Error;

// ========================================== Constants ========================================= \\

const ROOT_HEIGHT: u8 = 255;

const MASK_TAG_RIGHT: u8 = (1 << 4) - 1;
const MASK_TAG_LEFT: u8 = MASK_TAG_RIGHT << 4;

const EMPTY_TAG: u8 = 0;
const BRANCH_TAG: u8 = 1;
const HASH_TAG: u8 = 2;
const LEAF_TAG: u8 = 3;

// ============================================ Types =========================================== \\

#[derive(Default, Debug)]
pub struct Tree {
    root: Branch,
    leaves: usize,
}

#[derive(Debug)]
pub struct Proof {
    root: ProofBranch,
}

#[derive(Debug)]
#[cfg_attr(feature = "thiserror", derive(Error))]
pub enum Error {
    #[cfg_attr(feature = "thiserror", error("invalid branch tag"))]
    InvalidTag,
    #[cfg_attr(feature = "thiserror", error("invalid tree (`flush()` must be called)"))]
    InvalidTree,
    #[cfg_attr(feature = "thiserror", error("missing node or leaf hash"))]
    MissingHash,
    #[cfg_attr(feature = "thiserror", error("missing branch height"))]
    MissingHeight,
    #[cfg_attr(feature = "thiserror", error("missing required leaf"))]
    MissingLeaf,
    #[cfg_attr(feature = "thiserror", error("missing branch tag"))]
    MissingTag,
}

#[derive(Debug)]
enum Node {
    Branch(Box<Branch>),
    Leaf(Box<Leaf>),
    Empty,
}

#[derive(Debug)]
enum ProofNode {
    Branch(Box<ProofBranch>),
    Hash(Box<Hash>),
    Leaf(Box<Leaf>),
    Empty,
}

#[derive(Debug)]
struct Branch {
    height: u8,
    hash: Option<Hash>,
    left: Node,
    right: Node,
}

#[derive(Debug)]
struct ProofBranch {
    height: u8,
    left: ProofNode,
    right: ProofNode,
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Debug)]
struct Leaf(U256);

#[derive(Copy, Clone, Debug)]
enum Direction {
    Left,
    Right,
}

// ========================================== impl Tree ========================================= \\

impl Tree {
    // ==================================== Constructors ==================================== \\

    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    // ======================================== Read ======================================== \\

    #[inline]
    pub fn root(&self) -> Option<Hash> {
        self.root.hash
    }

    #[inline]
    pub fn leaves(&self) -> usize {
        self.leaves
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.root.hash.is_some()
    }

    #[inline]
    pub fn contains(&self, hash: Hash) -> bool {
        self.root.contains(Leaf::from(hash))
    }

    // ===================================== Read+Write ===================================== \\

    pub fn insert(&mut self, hash: Hash) -> bool {
        let leaf = Box::<Leaf>::from(hash);
        let inserted = self.root.insert(leaf);

        if inserted {
            self.leaves += 1;
        }

        inserted
    }

    pub fn remove(&mut self, hash: Hash) -> bool {
        let leaf = Leaf::from(hash);
        let removed = self.root.remove(leaf);

        if removed {
            self.leaves -= 1;
        }

        removed
    }

    #[inline]
    pub fn flush(&mut self) -> Hash {
        if self.root.left.is_empty() && self.root.right.is_empty() {
            self.root.hash = Some(Hash::from([0; 32]));
            self.root.hash.unwrap()
        } else {
            self.root.flush()
        }
    }
}

// ========================================= impl Proof ========================================= \\

impl Proof {
    // ==================================== Constructors ==================================== \\

    pub fn new(tree: &Tree, hashes: &[Hash]) -> Result<Self, Error> {
        if !tree.is_valid() {
            return Err(Error::InvalidTree);
        }

        if hashes.len() > tree.leaves() {
            return Err(Error::MissingLeaf);
        }

        let mut leaves = Vec::from_iter(hashes.iter().copied().map(Leaf::from));
        leaves.sort_unstable();

        Ok(Proof {
            root: ProofBranch::include(&tree.root, &leaves)?,
        })
    }

    pub fn from_bytes(buf: &[u8]) -> Result<Self, Error> {
        Ok(Proof {
            root: ProofBranch::from_bytes(buf)?.0,
        })
    }

    // ======================================== Read ======================================== \\

    fn nodes(&self) -> (usize, usize) {
        fn nodes(branch: &ProofBranch, branches: &mut usize, hashes: &mut usize) {
            match &branch.left {
                ProofNode::Branch(branch) => {
                    *branches += 1;
                    nodes(branch, branches, hashes);
                }
                ProofNode::Hash(_) | ProofNode::Leaf(_) => *hashes += 1,
                ProofNode::Empty => (),
            }

            match &branch.right {
                ProofNode::Branch(branch) => {
                    *branches += 1;
                    nodes(branch, branches, hashes);
                }
                ProofNode::Hash(_) | ProofNode::Leaf(_) => *hashes += 1,
                ProofNode::Empty => (),
            }
        }

        let (mut branches, mut hashes) = (1, 0);
        nodes(&self.root, &mut branches, &mut hashes);

        (branches, hashes)
    }

    pub fn as_bytes(&self) -> Vec<u8> {
        let (branches, hashes) = self.nodes();
        let mut buf = vec![0; 2 * branches + hashes * 32];

        self.root.as_bytes(&mut buf);
        buf
    }

    pub fn verify(&self, root: Hash) -> bool {
        self.root.hash() == root
    }
}

// ========================================== impl Node ========================================= \\

impl Node {
    // ======================================== Read ======================================== \\

    #[inline]
    fn is_empty(&self) -> bool {
        if let Node::Empty = self {
            true
        } else {
            false
        }
    }

    #[inline]
    fn as_branch_mut(&mut self) -> Option<&mut Branch> {
        if let Node::Branch(branch) = self {
            Some(branch)
        } else {
            None
        }
    }

    // ===================================== Read+Write ===================================== \\

    #[inline]
    fn take(&mut self) -> Self {
        mem::take(self)
    }

    #[inline]
    fn flush(&mut self) -> Option<Hash> {
        match self {
            Node::Branch(branch) => Some(branch.flush()),
            Node::Leaf(leaf) => Some(leaf.hash()),
            Node::Empty => None,
        }
    }

    // ======================================== Write ======================================= \\

    #[inline]
    fn clear(&mut self) {
        mem::take(self);
    }
}

// ======================================= impl ProofNode ======================================= \\

impl ProofNode {
    // ==================================== Constructors ==================================== \\

    fn include(source: &Node, leaves: &[Leaf]) -> Result<Self, Error> {
        match source {
            Node::Branch(branch) if leaves.is_empty() => Ok(branch.hash.unwrap().into()),
            Node::Branch(branch) => Ok(ProofBranch::include(branch, leaves)?.into()),

            Node::Leaf(leaf) if leaves.is_empty() => Ok(leaf.hash().into()),
            Node::Leaf(_) if leaves.len() > 1 => Err(Error::MissingLeaf),
            Node::Leaf(leaf) if **leaf != leaves[0] => Err(Error::MissingLeaf),
            Node::Leaf(leaf) => Ok(leaf.into()),

            Node::Empty if !leaves.is_empty() => Err(Error::MissingLeaf),
            Node::Empty => Ok(ProofNode::Empty),
        }
    }

    // ======================================== Read ======================================== \\

    fn hash(&self) -> Option<Hash> {
        match self {
            ProofNode::Branch(branch) => Some(branch.hash()),
            ProofNode::Hash(hash) => Some(**hash),
            ProofNode::Leaf(leaf) => Some(leaf.hash()),
            ProofNode::Empty => None,
        }
    }
}

// ========================================= impl Branch ======================================== \\

impl Branch {
    // ======================================== Read ======================================== \\

    fn contains(&self, leaf: Leaf) -> bool {
        let dir = leaf[self.height];
        match &self[dir] {
            Node::Branch(branch) => branch.contains(leaf),
            Node::Leaf(child) => **child == leaf,
            Node::Empty => false,
        }
    }

    // ===================================== Read+Write ===================================== \\

    fn fork(&mut self, dir: Direction, fork_height: u8) -> &mut Self {
        self.hash.take();

        let mut branch = Box::<Self>::default();
        branch.height = fork_height;

        match mem::take(&mut self[dir]) {
            Node::Leaf(leaf) => {
                let dir = leaf[branch.height];
                branch[dir] = leaf.into();
            }
            node => branch[dir] = node,
        }

        self[dir] = branch.into();
        self[dir].as_branch_mut().unwrap()
    }

    fn insert(&mut self, leaf: Box<Leaf>) -> bool {
        let height = self.height;
        let dir = leaf[height];
        match &mut self[dir] {
            Node::Branch(branch) => {
                let inserted = match leaf.next_change(height) {
                    Some(height) if height <= branch.height => branch.insert(leaf),
                    Some(height) => return self.fork(dir, height).insert(leaf),
                    None => branch.insert(leaf),
                };

                if inserted {
                    self.hash.take();
                }

                inserted
            }

            Node::Leaf(child) if child == &leaf => false,

            Node::Leaf(child) => {
                let branch = match (leaf.next_change(height), child.next_change(height)) {
                    (Some(height), None) | (None, Some(height)) => self.fork(dir, height),
                    (Some(leaf), Some(child)) => self.fork(dir, cmp::max(leaf, child)),
                    (None, None) => unreachable!(),
                };

                branch.insert(leaf)
            }

            node @ Node::Empty => {
                *node = leaf.into();
                self.hash.take();

                true
            }
        }
    }

    fn remove(&mut self, leaf: Leaf) -> bool {
        let dir = leaf[self.height];
        match &mut self[dir] {
            Node::Branch(branch) => {
                if !branch.remove(leaf) {
                    return false;
                }

                match (branch.left.is_empty(), branch.right.is_empty()) {
                    (true, true) => self[dir].clear(),
                    (true, false) => {
                        let node = branch.right.take();
                        self[dir] = node;
                    }
                    (false, true) => {
                        let node = branch.left.take();
                        self[dir] = node;
                    }
                    (false, false) => (),
                }

                self.hash.take();
                true
            }

            Node::Leaf(child) if **child == leaf => {
                self[dir].take();
                self.hash.take();

                true
            }

            Node::Leaf(_) | Node::Empty => false,
        }
    }

    fn flush(&mut self) -> Hash {
        if let Some(hash) = self.hash {
            return hash;
        }

        let left = self.left.flush();
        let right = self.right.flush();

        match (left, right) {
            (Some(hash), None) | (None, Some(hash)) => {
                self.hash = Some(hash);
                hash
            }
            (Some(left), Some(right)) => {
                let mut hasher = Hasher::new();
                hasher.update(&left.as_bytes()[..]);
                hasher.update(&right.as_bytes()[..]);

                let hash = hasher.finalize();
                self.hash = Some(hash);

                hash
            }
            (None, None) => {
                dbg!(&self);
                unreachable!()
            },
        }
    }
}

// ====================================== impl ProofBranch ====================================== \\

impl ProofBranch {
    // ==================================== Constructors ==================================== \\

    fn include(source: &Branch, leaves: &[Leaf]) -> Result<Self, Error> {
        let mut dest = ProofBranch {
            height: source.height,
            left: ProofNode::Empty,
            right: ProofNode::Empty,
        };

        let (left, right) = if leaves[0][dest.height].is_right() {
            leaves.split_at(0)
        } else {
            let idx = leaves
                .iter()
                .enumerate()
                .rev()
                .find_map(|(idx, leaf)| {
                    if leaf[dest.height].is_left() {
                        Some(idx)
                    } else {
                        None
                    }
                })
                .unwrap();

            leaves.split_at(idx + 1)
        };

        dest.left = ProofNode::include(&source.left, left)?;
        dest.right = ProofNode::include(&source.right, right)?;

        Ok(dest)
    }

    fn from_bytes(buf: &[u8]) -> Result<(Self, &[u8]), Error> {
        let (height, buf) = buf.split_first().ok_or(Error::MissingHeight)?;
        let (tag, buf) = buf.split_first().ok_or(Error::MissingTag)?;

        let mut dest = ProofBranch {
            height: u8::from_le(*height),
            left: ProofNode::Empty,
            right: ProofNode::Empty,
        };

        let buf = match (tag & MASK_TAG_LEFT) >> 4 {
            BRANCH_TAG => {
                let (branch, buf) = ProofBranch::from_bytes(buf)?;
                dest.left = branch.into();
                buf
            }
            HASH_TAG => {
                dest.left =
                    Hash::from(<[u8; 32]>::try_from(buf.get(0..32).ok_or(Error::MissingHash)?).unwrap()).into();
                &buf[32..]
            }
            LEAF_TAG => {
                dest.left = Leaf(U256::from_le_bytes(
                    <[u8; 32]>::try_from(buf.get(0..32).ok_or(Error::MissingHash)?).unwrap(),
                ))
                .into();
                &buf[32..]
            }
            EMPTY_TAG => buf,
            _ => return Err(Error::InvalidTag),
        };

        let buf = match tag & MASK_TAG_RIGHT {
            BRANCH_TAG => {
                let (branch, buf) = ProofBranch::from_bytes(buf)?;
                dest.right = branch.into();
                buf
            }
            HASH_TAG => {
                dest.right =
                    Hash::from(<[u8; 32]>::try_from(buf.get(0..32).ok_or(Error::MissingHash)?).unwrap()).into();
                &buf[32..]
            }
            LEAF_TAG => {
                dest.right = Leaf(U256::from_le_bytes(
                    <[u8; 32]>::try_from(buf.get(0..32).ok_or(Error::MissingHash)?).unwrap(),
                ))
                .into();
                &buf[32..]
            }
            EMPTY_TAG => buf,
            _ => return Err(Error::InvalidTag),
        };

        Ok((dest, buf))
    }

    // ======================================== Read ======================================== \\

    fn as_bytes<'buf>(&self, buf: &'buf mut [u8]) -> &'buf mut [u8] {
        let (height, buf) = buf.split_first_mut().unwrap();
        let (tag, buf) = buf.split_first_mut().unwrap();

        *height = self.height.to_le();

        let buf = match &self.left {
            ProofNode::Branch(branch) => {
                *tag |= BRANCH_TAG << 4;
                branch.as_bytes(&mut buf[..])
            }
            ProofNode::Hash(hash) => {
                *tag |= HASH_TAG << 4;
                buf[..32].copy_from_slice(hash.as_bytes());
                &mut buf[32..]
            }
            ProofNode::Leaf(leaf) => {
                *tag |= LEAF_TAG << 4;
                buf[..32].copy_from_slice(leaf.hash().as_bytes());
                &mut buf[32..]
            }
            ProofNode::Empty => buf,
        };

        match &self.right {
            ProofNode::Branch(branch) => {
                *tag |= BRANCH_TAG;
                branch.as_bytes(&mut buf[..])
            }
            ProofNode::Hash(hash) => {
                *tag |= HASH_TAG;
                buf[..32].copy_from_slice(hash.as_bytes());
                &mut buf[32..]
            }
            ProofNode::Leaf(leaf) => {
                *tag |= LEAF_TAG;
                buf[..32].copy_from_slice(leaf.hash().as_bytes());
                &mut buf[32..]
            }
            ProofNode::Empty => buf,
        }
    }

    fn hash(&self) -> Hash {
        match (self.left.hash(), self.right.hash()) {
            (Some(hash), None) | (None, Some(hash)) => hash,
            (Some(left), Some(right)) => {
                let mut hasher = Hasher::new();
                hasher.update(&left.as_bytes()[..]);
                hasher.update(&right.as_bytes()[..]);

                hasher.finalize()
            }
            (None, None) => unreachable!(),
        }
    }
}

// ========================================== impl Leaf ========================================= \\

impl Leaf {
    // ======================================== Read ======================================== \\

    fn hash(&self) -> Hash {
        Hash::from(self.0.to_le_bytes())
    }

    fn next_change(&self, height: u8) -> Option<u8> {
        let mask = (U256::new(1) << height) - 1;
        let height = match &self[height] {
            Direction::Left => (self.0 & mask).leading_zeros(),
            Direction::Right => (self.0 | !mask).leading_ones(),
        };

        if height == 256 {
            None
        } else {
            Some(255 - height as u8)
        }
    }
}

// ======================================= impl Direction ======================================= \\

impl Direction {
    // ======================================== Read ======================================== \\

    #[inline]
    fn is_left(&self) -> bool {
        if let Direction::Left = self {
            true
        } else {
            false
        }
    }

    #[inline]
    fn is_right(&self) -> bool {
        if let Direction::Right = self {
            true
        } else {
            false
        }
    }
}

// ======================================== impl Default ======================================== \\

impl Default for Node {
    #[inline]
    fn default() -> Self {
        Node::Empty
    }
}

impl Default for Branch {
    fn default() -> Self {
        Branch {
            height: ROOT_HEIGHT,
            hash: None,
            left: Node::Empty,
            right: Node::Empty,
        }
    }
}

// ========================================== impl From ========================================= \\

impl From<Box<Branch>> for Node {
    #[inline]
    fn from(branch: Box<Branch>) -> Self {
        Node::Branch(branch)
    }
}

impl From<Box<Leaf>> for Node {
    #[inline]
    fn from(leaf: Box<Leaf>) -> Self {
        Node::Leaf(leaf)
    }
}

impl From<ProofBranch> for ProofNode {
    #[inline]
    fn from(branch: ProofBranch) -> Self {
        ProofNode::Branch(branch.into())
    }
}

impl From<Hash> for ProofNode {
    #[inline]
    fn from(hash: Hash) -> Self {
        ProofNode::Hash(hash.into())
    }
}

impl From<Leaf> for ProofNode {
    #[inline]
    fn from(leaf: Leaf) -> Self {
        ProofNode::Leaf(leaf.into())
    }
}

impl From<&Box<Leaf>> for ProofNode {
    #[inline]
    fn from(leaf: &Box<Leaf>) -> Self {
        ProofNode::Leaf(leaf.clone())
    }
}

impl From<Hash> for Leaf {
    #[inline]
    fn from(hash: Hash) -> Self {
        Leaf(U256::from_le_bytes(hash.into()))
    }
}

impl From<Hash> for Box<Leaf> {
    #[inline]
    fn from(hash: Hash) -> Self {
        Leaf::from(hash).into()
    }
}

// ====================================== impl Index{,Mut} ====================================== \\

impl Index<Direction> for Branch {
    type Output = Node;

    #[inline]
    fn index(&self, dir: Direction) -> &Node {
        match dir {
            Direction::Left => &self.left,
            Direction::Right => &self.right,
        }
    }
}

impl IndexMut<Direction> for Branch {
    #[inline]
    fn index_mut(&mut self, dir: Direction) -> &mut Node {
        match dir {
            Direction::Left => &mut self.left,
            Direction::Right => &mut self.right,
        }
    }
}

impl Index<u8> for Leaf {
    type Output = Direction;

    #[inline]
    fn index(&self, height: u8) -> &Direction {
        if self.0 & (U256::new(1) << height) == U256::ZERO {
            &Direction::Left
        } else {
            &Direction::Right
        }
    }
}
