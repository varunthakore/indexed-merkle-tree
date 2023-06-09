use neptune::poseidon::PoseidonConstants;
use pasta_curves::arithmetic::FieldExt;
use pasta_curves::group::ff::{PrimeField, PrimeFieldBits};

use crate::hash::vanilla::hash;
use neptune::Arity;
use std::marker::PhantomData;

use std::collections::HashMap;
use generic_array::typenum::{U2, U3};
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::Strength;

use crypto_bigint::{U256, Encoding, CheckedAdd, CheckedSub};



pub struct Leaf<F: PrimeField + PrimeFieldBits, A: Arity<F>> {
    pub value: F,
    pub next_value: F,
    pub next_index: F,
    pub _arity: PhantomData<A>    
}

impl<F: PrimeField + PrimeFieldBits, A: Arity<F>> Default for Leaf<F,A> {
    fn default() -> Self {
        Self { value: F::zero(), 
            next_value: F::zero(), 
            next_index: F::zero(), 
            _arity: PhantomData }
    }
}

impl<F: PrimeField + PrimeFieldBits, A: Arity<F>> Clone for Leaf<F,A> {
    fn clone(&self) -> Self {
        Leaf { value: self.value.clone(), 
            next_value: self.next_value.clone(), 
            next_index: self.next_index.clone(), 
            _arity: PhantomData }
    }
}

impl<F, A> Leaf<F, A>
where
    F: PrimeField + PrimeFieldBits + FieldExt,
    A: Arity<F>
{
    pub fn leaf_to_vec(&self) -> Vec<F> {
        let mut input: Vec<F> = vec![];
        input.push(self.value);
        input.push(self.next_value);
        input.push(self.next_index);

        assert_eq!(input.len(), 3);
        input
    }

    pub fn hash_leaf(&self, p: &PoseidonConstants<F, A>) -> F {
        let input = self.leaf_to_vec();
        hash::<F, A>(input, p)
    }
}

pub struct IndexTree<F: PrimeField + PrimeFieldBits + FieldExt, const N: usize> {
    pub root: F,
    pub hash_db: HashMap<String, (F,F)>,
    pub leaf_hash_params: PoseidonConstants<F, U3>,
    pub node_hash_params: PoseidonConstants<F, U2>
}

impl<F: PrimeField + PrimeFieldBits + FieldExt, const N: usize> Clone for IndexTree<F, N> {
    fn clone(&self) -> Self {
        IndexTree { root: self.root.clone(), 
                    hash_db: self.hash_db.clone(), 
                    leaf_hash_params: self.leaf_hash_params.clone(), 
                    node_hash_params: self.node_hash_params.clone()
        }
    }
}

impl<F: PrimeField + PrimeFieldBits + FieldExt, const N: usize> IndexTree<F, N> {
    
    // Create a new tree. `empty_leaf_val` is the default value for leaf of empty tree. 
    pub fn new(
        empty_leaf_val: Leaf<F, U3>,
        depth: usize,
    ) -> IndexTree<F, N> {
        assert!(depth > 0);
        let mut hash_db = HashMap::<String, (F, F)>::new();
        let leaf_hash_params = Sponge::<F, U3>::api_constants(Strength::Standard);
        let node_hash_params = Sponge::<F, U2>::api_constants(Strength::Standard);
        let mut cur_hash = Leaf::<F, U3>::hash_leaf(&empty_leaf_val, &leaf_hash_params);
        for _ in 0..depth {
            let val = (cur_hash.clone(), cur_hash.clone());
            cur_hash = hash(vec![cur_hash.clone(), cur_hash.clone()], &node_hash_params);
            hash_db.insert(format!("{:?}",cur_hash.clone()), val);
        }
        Self {
            root: cur_hash,
            hash_db: hash_db,
            leaf_hash_params: leaf_hash_params,
            node_hash_params: node_hash_params
        }
    }

    pub fn insert_vanilla(
        &mut self,
        mut low_leaf_idx: Vec<bool>, // from root to leaf
        mut low_leaf: Leaf<F, U3>,
        new_val: F,
        next_insertion_idx: F,
    ) {
        // Check that leaf at next_insertion_index is empty
        let next_leaf_idx = idx_to_bits(N, next_insertion_idx);
        // let tree_copy = self.clone();
        let empty_path = self.get_siblings_path(next_leaf_idx.clone());
        assert!(empty_path.is_member_vanilla(next_leaf_idx.clone(), &Leaf::default(), self.root));

        // Check that low leaf is memeber
        let low_leaf_path = self.get_siblings_path(low_leaf_idx.clone());
        assert!(low_leaf_path.is_member_vanilla(low_leaf_idx.clone(), &low_leaf, self.root));

        // Range check low leaf against new value
        assert!(new_val < low_leaf.next_value || low_leaf.next_value == F::zero());
        assert!(new_val > low_leaf.value);

        // Update new leaf pointers
        let new_leaf = Leaf {
            value: new_val,
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<U3>
        };
        // Update low leaf pointers
        low_leaf.next_index = next_insertion_idx;
        low_leaf.next_value = new_leaf.value;
        
        // Insert new low leaf into tree
        let mut low_leaf_siblings = low_leaf_path.siblings;
        low_leaf_idx.reverse(); // Reverse since path was from root to leaf but I am going leaf to root
        let mut cur_low_leaf_hash = Leaf::<F, U3>::hash_leaf(&low_leaf, &self.leaf_hash_params);
        for d in low_leaf_idx {
            let sibling = low_leaf_siblings.pop().unwrap();
            let (l, r) = if d == false {
                // leaf falls on the left side
                (cur_low_leaf_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_low_leaf_hash)
            };
            let val = (l, r);
            cur_low_leaf_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
            self.hash_db.insert(format!("{:?}",cur_low_leaf_hash.clone()), val);
        }
        self.root = cur_low_leaf_hash;

        // Insert new leaf into tree
        let mut new_leaf_idx = idx_to_bits(N, next_insertion_idx); // from root to leaf
        let mut new_leaf_siblings = self.get_siblings_path(new_leaf_idx.clone()).siblings;
        new_leaf_idx.reverse(); // from leaf to root
        let mut cur_new_leaf_hash = Leaf::<F, U3>::hash_leaf(&new_leaf, &self.leaf_hash_params);
        for d in new_leaf_idx {
            let sibling = new_leaf_siblings.pop().unwrap();
            let (l, r) = if d == false {
                // leaf falls on the left side
                (cur_new_leaf_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_new_leaf_hash)
            };
            let val = (l, r);
            cur_new_leaf_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
            self.hash_db.insert(format!("{:?}",cur_new_leaf_hash.clone()), val);
        }
        self.root = cur_new_leaf_hash;

    }

    // Get siblings given leaf index index
    pub fn get_siblings_path(
        &self,
        idx_in_bits: Vec<bool>, // root to leaf
    ) -> Path<F, N> {
        let mut cur_node = self.root;
        let mut siblings = Vec::<F>::new();


        let mut children;
        for d in idx_in_bits {
            children = self.hash_db.get(&format!("{:?}",cur_node.clone())).unwrap();
            if d == false {
                // leaf falls on the left side
                cur_node = children.0;
                siblings.push(children.1);

            } else {
                // leaf falls on the right side
                cur_node = children.1;
                siblings.push(children.0);

            }
        }

        Path{ 
            siblings: siblings, // siblings from root to leaf
            leaf_hash_params: &self.leaf_hash_params,
            node_hash_params: &self.node_hash_params
        }
    }
}

pub fn idx_to_bits<F: PrimeField + PrimeFieldBits>(depth: usize, idx: F) -> Vec<bool> {
    let mut path: Vec<bool> = vec![];
    for d in idx.to_le_bits() {
        if path.len() >= depth {
            break;
        }
        
        if d==true {
            path.push(true)
        } else {
            path.push(false)
        }
    }

    while path.len() != depth {
        path.push(false);
    }

    path.reverse();
    path // path is from root to leaf

}


pub struct Path<'a, F, const N: usize>
where
	F: PrimeField + PrimeFieldBits + FieldExt,
{
	pub siblings: Vec<F>, // siblings from root to leaf
    pub leaf_hash_params: &'a PoseidonConstants<F, U3>,
    pub node_hash_params: &'a PoseidonConstants<F, U2>
}

impl<'a, F: PrimeField + PrimeFieldBits + FieldExt, const N: usize> Path<'a, F, N> {
    pub fn compute_root(
        &self,
        mut idx_in_bits: Vec<bool>,
        val: &Leaf<F, U3>,
    ) -> F {
        assert_eq!(self.siblings.len(), N);
        idx_in_bits.reverse(); // from leaf to root

        let mut cur_hash = Leaf::<F, U3>::hash_leaf(val, &self.leaf_hash_params);

        for (i, sibling) in self.siblings.clone().into_iter().rev().enumerate() {
            let (l, r) = if idx_in_bits[i] == false {
                // leaf falls on the left side
                (cur_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_hash)
            };
            cur_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
        }
        cur_hash

    }

    // Check that Leaf is present in the tree
    pub fn is_member_vanilla(
        &self,
        idx_in_bits: Vec<bool>, // from root to leaf
        leaf: &Leaf<F, U3>,
        root: F
    ) -> bool {
        let computed_root = self.compute_root(idx_in_bits, &leaf);
        computed_root == root
    }

    // Check that there is no Leaf with value = new_value in the tree
    pub fn is_non_member_vanilla(
        &self,
        low_leaf: &Leaf<F, U3>,
        low_leaf_idx: Vec<bool>, // from root to leaf
        new_value: F,
        root: F
    ) -> bool {
        // Check that low leaf is memeber, self is siblings path for low_leaf
        assert!(self.is_member_vanilla(low_leaf_idx.clone(), &low_leaf, root));
        
        // Range check low leaf against new value
        if low_leaf.next_index == F::zero() {
            return low_leaf.value < new_value // the low leaf is at the very end, so the new_value must be higher than all values in the tree
        } 
        else {
            return low_leaf.value < new_value && low_leaf.next_value > new_value    
        }
        
    }
}

// Outputs true if in1 < in2, otherwise false 
pub fn is_less_vanilla<'a, F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + FieldExt>(
    in1: F,
    in2: F,
) -> bool {
    let in1_u256 = U256::from_le_bytes(F::to_repr(&in1));
    let in2_u256 = U256::from_le_bytes(F::to_repr(&in2));
    
    let diff = U256::checked_sub(&U256::checked_add(&in1_u256, &(U256::from(1u64)<<255)).unwrap(), &in2_u256).unwrap();
    let diff_bytes = diff.to_le_bytes();

    let diff_bits: Vec<bool> = diff_bytes
        .map(|value| {
            let mut bits = [false; 8];
            for i in 0..8 {
                bits[i] = (value >> i) & 1 == 1;
            }
            bits
        })
        .concat()
    ;
    assert_eq!(diff_bits.len(), 256);
    !diff_bits[255]
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::marker::PhantomData;

    use pasta_curves::group::ff::Field;

    use pasta_curves::pallas::Base as Fp;
    use generic_array::typenum::U12;
    use neptune::sponge::vanilla::{Sponge, SpongeTrait};
    use neptune::Strength;

    use crate::tree::indextree::IndexTree;

    use super::Leaf;

    #[test]
    fn test_hash_leaf() {
        let mut rng = rand::thread_rng();
        let leaf = Leaf {
            value: Fp::random(&mut rng),
            next_value: Fp::random(&mut rng),
            next_index: Fp::random(&mut rng),
            _arity: PhantomData
        };
        let p = Sponge::<Fp, U12>::api_constants(Strength::Standard);
        let hash_leaf = Leaf::hash_leaf(&leaf, &p);
        println!("hash value is {:?}", hash_leaf);
    }

    #[test]
    fn test_insert() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT> = IndexTree::new(empty_leaf.clone(), HEIGHT);
        println!("root is {:?}", tree.root);

        let low_leaf_idx = idx_to_bits(HEIGHT, Fp::zero()); // from root to leaf
        let low_leaf = empty_leaf.clone();
        let new_value = Fp::random(&mut rng);
        let next_insertion_index = Fp::one();
        let next_leaf_idx = idx_to_bits(HEIGHT, next_insertion_index);

        let new_leaf = Leaf {
            value: new_value,
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<U3>   
        };

        // Insert new value at next_insertion_index
        tree.insert_vanilla(low_leaf_idx.clone(), low_leaf, new_value.clone(), next_insertion_index);
        println!("root is {:?}", tree.root);
        
        // Check that new leaf is inseted at next_insertion_index
        let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
        assert!(inserted_path.is_member_vanilla(next_leaf_idx.clone(), &new_leaf.clone(), tree.root));
        
    }

    #[test]
    fn test_non_member() {
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT> = IndexTree::new(empty_leaf.clone(), HEIGHT);
        println!("root is {:?}", tree.root);

        let low_leaf_idx = idx_to_bits(HEIGHT, Fp::zero()); // from root to leaf
        let low_leaf = empty_leaf.clone();
        let new_value = Fp::from(20 as u64);
        let next_insertion_index = Fp::one();
        let next_leaf_idx = idx_to_bits(HEIGHT, next_insertion_index);

        // Check that new_value is_non_member
        let low_leaf_path = tree.get_siblings_path(low_leaf_idx.clone());
        assert!(low_leaf_path.is_non_member_vanilla(&low_leaf, low_leaf_idx.clone(), new_value, tree.root));

        let new_leaf = Leaf {
            value: new_value,
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<U3>   
        };

        // Insert new_value at next_insertion_index
        tree.insert_vanilla(low_leaf_idx.clone(), low_leaf.clone(), new_value.clone(), next_insertion_index);
        println!("root is {:?}", tree.root);
        
        // Check that new leaf is inseted at next_insertion_index
        let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
        assert!(inserted_path.is_member_vanilla(next_leaf_idx.clone(), &new_leaf.clone(), tree.root));

        // Checking value = 20 for is_non_member should fail 
        let new_low_leaf = Leaf {
            value: low_leaf.value,
            next_value: new_leaf.value,
            next_index: next_insertion_index,
            _arity: PhantomData::<U3>
        };
        let new_low_leaf_path = tree.get_siblings_path(low_leaf_idx.clone());
        assert!(!new_low_leaf_path.is_non_member_vanilla(&new_low_leaf, low_leaf_idx.clone(), Fp::from(20 as u64), tree.root));

        // Checking value = 40 for is_non_member should pass
        assert!(inserted_path.is_non_member_vanilla(&new_leaf, next_leaf_idx, Fp::from(40 as u64), tree.root));  

    }

    #[test]
    fn test_less() {
        let in1 = Fp::from(100 as u64);
        let in2 = Fp::from(30 as u64);

        println!("in1 < in2 {}", is_less_vanilla(in1, in2))
    } 
}