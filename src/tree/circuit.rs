use std::marker::PhantomData;

use pasta_curves::{
    group::ff::{PrimeField, PrimeFieldBits},
    arithmetic::FieldExt,
};

use neptune::Strength;
use neptune::sponge::{
    vanilla::{Sponge, SpongeTrait},
};
use generic_array::typenum::{U2, U3};

use bellperson::{ConstraintSystem, SynthesisError, gadgets::num::AllocatedNum};
use bellperson::gadgets::boolean::{Boolean, AllocatedBit};
use bellperson::Namespace;
use crypto_bigint::{U256, CheckedSub, Encoding, CheckedAdd, CheckedMul};

use bellperson_nonnative::util::num::Num;
use bellperson_nonnative::mp::bignat::BigNat;
use num_bigint::BigInt;
use num_bigint::Sign::Plus;

use crate::{hash::circuit::hash_circuit, tree::indextree::{Path, Leaf, idx_to_bits}};

use super::indextree::IndexTree;


// adapted from https://github.com/iden3/circomlib/blob/cff5ab6288b55ef23602221694a6a38a0239dcc0/circuits/comparators.circom#L89
// Outputs true if in1 < in2, otherwise false 
pub fn is_less<F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + FieldExt, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    in1: AllocatedNum<F>,
    in2: AllocatedNum<F>,
) -> Result<Boolean, SynthesisError>
{
    let in1_big = BigNat::from_num(&mut cs.namespace(|| "in1 bignat"), Num::from(in1.clone()), 128, 2)?;
    let in2_big = BigNat::from_num(&mut cs.namespace(|| "in2 bignat"), Num::from(in2.clone()), 128, 2)?;

    let exp255 = BigNat::alloc_from_nat(&mut cs.namespace(|| "exp255 bignat"), || Ok(BigInt::from_bytes_le(Plus, &(U256::from(1u64)<<255).to_le_bytes())), 128, 2)?;

    let diff = BigNat::sub(&BigNat::add::<CS>(&in1_big, &exp255)?, &mut cs.namespace(|| "sub"), &in2_big)?;

    let diff_exp = U256::checked_sub(
        &U256::checked_add(&U256::from_le_bytes(F::to_repr(&in1.get_value().unwrap())), &(U256::from(1u64)<<255)).unwrap(), 
        &U256::from_le_bytes(F::to_repr(&in2.get_value().unwrap()))
    ).unwrap().to_le_bytes();

    let diff_exp_big = BigNat::alloc_from_nat(&mut cs.namespace(|| "expected diff in bignat"), || Ok(BigInt::from_bytes_le(Plus, &diff_exp)), 128, 2)?;
    BigNat::equal(&diff, &mut cs.namespace(|| "check equal"), &diff_exp_big)?;

    let diff_exp_bits: Vec<bool> = diff_exp
        .map(|value| {
            let mut bits = [false; 8];
            for i in 0..8 {
                bits[i] = (value >> i) & 1 == 1;
            }
            bits
        })
        .concat()
    ;
    assert_eq!(diff_exp_bits.len(), 256);

    // Allocate all bits
    let diff_bits_var: Vec<AllocatedBit> = (0..256)
        .map(|i| {
            AllocatedBit::alloc(
                cs.namespace(|| format!("bit {i}")),
                {
                    let r = if diff_exp_bits[i] {
                        true
                    } else {
                        false
                    };
                    Some(r)
                },
            )
        })
        .collect::<Result<_, _>>()?;

    assert_eq!(diff_bits_var.len(), 256);
    
    let mut lc1 = U256::from(0u64);
    let mut e2 = U256::from(1u64);

    for (i, v) in diff_bits_var.iter().enumerate() {
        lc1 = U256::checked_add(&lc1, &U256::from(v.get_value().unwrap() as u64).checked_mul(&e2).unwrap()).unwrap();
        if i==255 {
            break;
        }
        e2 = U256::checked_add(&e2, &e2).unwrap();
    }

    let lc1_big = BigNat::alloc_from_nat(&mut cs.namespace(|| "lc1 bignat"), || Ok(BigInt::from_bytes_le(Plus, &lc1.to_le_bytes())), 128, 2)?;
    BigNat::equal(&lc1_big, &mut cs.namespace(|| "final equal"), &diff_exp_big)?;


    Ok(Boolean::from(diff_bits_var[255].clone()).not())

}


pub fn is_member<F: PrimeField + PrimeFieldBits + FieldExt, const N: usize, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    root_var: AllocatedNum<F>,
    val_var: Vec<AllocatedNum<F>>,
    mut idx_var: Vec<AllocatedBit>,
    siblings_var: Vec<AllocatedNum<F>>
) -> Result<Boolean, SynthesisError> {

    assert_eq!(val_var.len(), 3);
    assert_eq!(idx_var.len(), N);
    assert_eq!(idx_var.len(), siblings_var.len());
        
    let node_hash_params = Sponge::<F, U2>::api_constants(Strength::Standard);
    let leaf_hash_params = Sponge::<F, U3>::api_constants(Strength::Standard);
    let mut cur_hash_var = hash_circuit(&mut cs.namespace(|| "hash num -1 :"), val_var, &leaf_hash_params)?;

    idx_var.reverse(); // Going from leaf to root

    for (i, sibling) in siblings_var.clone().into_iter().rev().enumerate() {

        let (lc, rc) = AllocatedNum::conditionally_reverse(&mut cs.namespace(|| format!("rev num {} :", i)), &cur_hash_var, &sibling, &Boolean::from(idx_var[i].clone()))?;
        cur_hash_var = hash_circuit(&mut cs.namespace(|| format!("hash num {} :", i)), vec![lc, rc], &node_hash_params)?;

    }

    let is_valid = AllocatedBit::alloc(cs.namespace(|| "is member"),Some(root_var.get_value() == cur_hash_var.get_value()))?;

    Ok(Boolean::from(is_valid))
}

pub fn is_non_member<F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + FieldExt, const N: usize, CS: ConstraintSystem<F>>(
    mut cs: &mut CS,
    root_var: AllocatedNum<F>,
    low_leaf_var: Vec<AllocatedNum<F>>,
    low_leaf_idx_var: Vec<AllocatedBit>,
    low_leaf_siblings_var: Vec<AllocatedNum<F>>,
    new_value: AllocatedNum<F>
) -> Result<Boolean, SynthesisError> {

    assert_eq!(low_leaf_var.len(), 3);
    assert_eq!(low_leaf_idx_var.len(), N);
    assert_eq!(low_leaf_idx_var.len(), low_leaf_siblings_var.len());

    // Hash low_leaf_var and check that low_leaf_var is_member
    let is_member = Boolean::from(is_member::<F, N, CS>(&mut cs, root_var.clone(), low_leaf_var.clone(), low_leaf_idx_var.clone(), low_leaf_siblings_var.clone())?);
    Boolean::enforce_equal(&mut cs, &is_member, &Boolean::constant(true))?;

    let out: Boolean; 

    if low_leaf_var[2].get_value().unwrap()==F::zero() { // the low leaf is at the very end, so the new_value must be higher than all values in the tree
        // low_leaf.value < new_value 
        out = is_less(cs, low_leaf_var[0].clone(), new_value.clone())?;
    } else {
        // low_leaf.value < new_value && new_value < low_leaf.next_value
        let cond1 = is_less(cs, low_leaf_var[0].clone(), new_value.clone())?;
        let cond2 = is_less(&mut cs, new_value.clone(), low_leaf_var[1].clone())?;

        out = Boolean::and(&mut cs,&cond1, &cond2)?;
    };

    let low_leaf_siblings_path: Path<F, N> = Path {
        siblings: low_leaf_siblings_var.clone().iter().map(|s| s.get_value().unwrap()).collect::<Vec<_>>(),
        leaf_hash_params: Sponge::<F, U3>::api_constants(Strength::Standard),
        node_hash_params: Sponge::<F, U2>::api_constants(Strength::Standard)
    };

    let exp_out = low_leaf_siblings_path.is_non_member_vanilla(
        &Leaf { value: low_leaf_var[0].get_value().unwrap(), next_value: low_leaf_var[1].get_value().unwrap(), next_index: low_leaf_var[2].get_value().unwrap(), _arity: PhantomData::<U3>}, 
        low_leaf_idx_var.clone().iter().map(|s| s.get_value().unwrap()).collect::<Vec<_>>(), 
        new_value.get_value().unwrap(), 
        root_var.get_value().unwrap()
    );

    let exp_out_var = AllocatedBit::alloc(cs.namespace(|| "exp out"), Some(exp_out))?;

    Boolean::enforce_equal(cs, &out.clone(), &Boolean::from(exp_out_var))?;
    
    Ok(out)

}


pub fn insert<F: PrimeField<Repr = [u8; 32]> + PrimeFieldBits + FieldExt, const N: usize, CS: ConstraintSystem<F>>(
    mut cs: &mut CS,
    mut tree: IndexTree<F, N>,
    mut low_leaf_var: Vec<AllocatedNum<F>>,
    low_leaf_idx_var: Vec<AllocatedBit>,
    new_val: AllocatedNum<F>,
    next_insertion_idx: AllocatedNum<F>
) -> Result<(), SynthesisError>
{
    assert_eq!(low_leaf_var.len(), 3);
    assert_eq!(low_leaf_idx_var.len(), N);

    let root_var = AllocatedNum::alloc(cs.namespace(|| "root"), || Ok(tree.root))?;

    // Check that leaf at next_insertion_index is empty
    let next_insetion_idx_bits = idx_to_bits(N, next_insertion_idx.get_value().unwrap())
        .into_iter()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("next idx {}", i)),Some(b)))
        .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()?
    ;
    let next_insertion_index_siblings = tree.get_siblings_path(idx_to_bits(N, next_insertion_idx.get_value().unwrap())).siblings
        .into_iter()
        .enumerate()
        .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("next sibling {}", i)),|| Ok(s)))
        .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?
    ;
    let empty_leaf_var = vec![AllocatedNum::alloc(cs.namespace(|| "empty leaf"), || Ok(F::zero())).unwrap(); 3];
    let check_empty = is_member::<F, N, CS>(
        &mut cs, 
        root_var.clone(), 
        empty_leaf_var, 
        next_insetion_idx_bits, 
        next_insertion_index_siblings)?
    ;
    Boolean::enforce_equal(&mut cs, &check_empty, &Boolean::constant(true))?;

    // Check that low leaf is member
    let low_leaf_path = tree.get_siblings_path(low_leaf_idx_var.clone().into_iter().map(|v|
        if v.get_value().unwrap() {
            true
        }
        else {
            false
        }
    ).collect());
    let low_leaf_siblings: Vec<AllocatedNum<F>> = low_leaf_path.clone().siblings
        .into_iter()
        .enumerate()
        .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("low leaf sibling {}", i)),|| Ok(s)))
        .collect::<Result<Vec<AllocatedNum<F>>, SynthesisError>>()?
    ;
    let check_low_leaf_member = is_member::<F, N, Namespace<'_, F, <CS as ConstraintSystem<F>>::Root>>(
        &mut cs.namespace(|| "check low leaf member"), 
        root_var, 
        low_leaf_var.clone(), 
        low_leaf_idx_var.clone(), 
        low_leaf_siblings)?
    ;
    Boolean::enforce_equal(&mut cs.namespace(|| "check low leaf true"), &check_low_leaf_member, &Boolean::constant(true))?;

    // Range check low leaf against new value
    let check_less = is_less(&mut cs, new_val.clone(), low_leaf_var[1].clone())?;
    let check_zero = Boolean::from(AllocatedBit::alloc(cs.namespace(|| "is zero"),Some(low_leaf_var[1].get_value().unwrap() == F::zero()))?);
    let check_range1 = Boolean::not(&Boolean::and(&mut cs,
        &Boolean::not(&check_less),
        &Boolean::not(&check_zero)
    )?)
    ;
    Boolean::enforce_equal(&mut cs.namespace(|| "check range 1 equal"), &check_range1, &Boolean::constant(true))?;
    let check_range2 = is_less(&mut cs.namespace(|| "check range 2"), low_leaf_var[0].clone(), new_val.clone())?;
    Boolean::enforce_equal(&mut cs.namespace(|| "check range 2 equal"), &check_range2, &Boolean::constant(true))?;

    // Update new leaf pointers
    let new_leaf_var = vec![new_val.clone(), low_leaf_var[1].clone(), low_leaf_var[2].clone()];

    // Update low leaf pointers
    low_leaf_var[1] = new_val.clone();
    low_leaf_var[2] = next_insertion_idx.clone();

    // Insert new low leaf into tree
    let mut low_leaf_siblings = low_leaf_path.siblings;
    let mut low_leaf_idx: Vec<bool> = low_leaf_idx_var.into_iter().map(|b| b.get_value().unwrap()).collect();
    low_leaf_idx.reverse(); // Reverse since path was from root to leaf but I am going leaf to root
    let mut cur_low_leaf_hash = hash_circuit(&mut cs.namespace(|| "low leaf hash"), low_leaf_var, &tree.leaf_hash_params)?.get_value().unwrap();
    for (i, d) in low_leaf_idx.iter().enumerate() {
        let sibling = low_leaf_siblings.pop().unwrap();
        let (l, r) = if *d == false {
            // leaf falls on the left side
            (cur_low_leaf_hash, sibling)
        } else {
            // leaf falls on the right side
            (sibling, cur_low_leaf_hash)
        };
        let val = (l, r);
        let l_var = AllocatedNum::alloc(cs.namespace(|| format!("left var {}", i)),|| Ok(l))?;
        let r_var = AllocatedNum::alloc(cs.namespace(|| format!("right var {}", i)),|| Ok(r))?;
        cur_low_leaf_hash = hash_circuit(&mut cs.namespace(|| format!("low node hash {}", i)), vec![l_var, r_var], &tree.node_hash_params)?.get_value().unwrap();
        tree.hash_db.insert(format!("{:?}",cur_low_leaf_hash.clone()), val);
    }
    tree.root = cur_low_leaf_hash;

    // Insert new leaf into tree
    let mut new_leaf_idx = idx_to_bits(N, next_insertion_idx.get_value().unwrap()); // from root to leaf
    let mut new_leaf_siblings = tree.get_siblings_path(new_leaf_idx.clone()).siblings;
    new_leaf_idx.reverse(); // from leaf to root
    let mut cur_new_leaf_hash = hash_circuit(&mut cs.namespace(|| "new leaf hash"), new_leaf_var, &tree.leaf_hash_params)?.get_value().unwrap();
    for (i,d) in new_leaf_idx.iter().enumerate() {
        let sibling = new_leaf_siblings.pop().unwrap();
        let (l, r) = if *d == false {
            // leaf falls on the left side
            (cur_new_leaf_hash, sibling)
        } else {
            // leaf falls on the right side
            (sibling, cur_new_leaf_hash)
        };
        let val = (l, r);
        let l_var = AllocatedNum::alloc(cs.namespace(|| format!("new left var {}", i)),|| Ok(l))?;
        let r_var = AllocatedNum::alloc(cs.namespace(|| format!("new right var {}", i)),|| Ok(r))?;
        cur_new_leaf_hash = hash_circuit(&mut cs.namespace(|| format!("new node hash {}", i)), vec![l_var, r_var], &tree.node_hash_params)?.get_value().unwrap();

        tree.hash_db.insert(format!("{:?}",cur_new_leaf_hash.clone()), val);
    }
    tree.root = cur_new_leaf_hash;

    Ok(())

}

#[cfg(test)]
mod tests {
    use super::*;
    use bellperson::{ConstraintSystem, SynthesisError, gadgets::num::AllocatedNum};
    use generic_array::typenum::U3;
    use pasta_curves::Fp;
    use crate::tree::indextree::{IndexTree, idx_to_bits, Leaf};
    use bellperson::util_cs::test_cs::TestConstraintSystem;
    use std::marker::PhantomData;
    use pasta_curves::group::ff::Field;

    
    #[test] 
    fn test_insert_circuit() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let tree: IndexTree<Fp, HEIGHT> = IndexTree::new(empty_leaf.clone(), HEIGHT);
        println!("root is {:?}", tree.root);

        let low_leaf_idx = idx_to_bits(HEIGHT, Fp::zero()); // from root to leaf
        let low_leaf = empty_leaf.clone();
        let new_value = Fp::random(&mut rng);
        let next_insertion_index = Fp::one();
        
        let mut cs = TestConstraintSystem::<Fp>::new();
        let low_leaf_vec = Leaf::leaf_to_vec(&low_leaf); // low_leaf_vec = [value, next_value, next_index]
        let low_leaf_var: Vec<AllocatedNum<Fp>> = low_leaf_vec
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("low leaf vec {}", i)), || Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;
        let low_leaf_idx_var: Vec<AllocatedBit> = low_leaf_idx
            .into_iter()
            .enumerate()
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("low leaf idx {}", i)),Some(b)))
            .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
            .unwrap()
        ;
        let new_val_var = AllocatedNum::alloc(cs.namespace(|| "new value"),|| Ok(new_value)).unwrap();
        let next_insertion_idx = AllocatedNum::alloc(cs.namespace(|| "next insertion index"),|| Ok(next_insertion_index)).unwrap();
        insert(&mut cs, tree.clone(), low_leaf_var, low_leaf_idx_var, new_val_var, next_insertion_idx).unwrap();
        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    
    }
 
    #[test]
    fn test_member_circuit() {
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

        // Insert new_value at next_insertion_index
        tree.insert_vanilla(low_leaf_idx.clone(), low_leaf.clone(), new_value.clone(), next_insertion_index);
        
        // Check that new leaf is inseted at next_insertion_index
        let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
        assert!(inserted_path.is_member_vanilla(next_leaf_idx.clone(), &new_leaf.clone(), tree.root));

        let mut cs = TestConstraintSystem::<Fp>::new();

        // Allocating all variables
        let root_var: AllocatedNum<Fp> = AllocatedNum::alloc_input(cs.namespace(|| "root"), || Ok(tree.root)).unwrap();
        
        let val_vec = Leaf::leaf_to_vec(&new_leaf); // val_vec = [value, next_value, next_index]
        let val_var: Vec<AllocatedNum<Fp>> = val_vec
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("leaf vec {}", i)), || Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;
        
        let siblings_var: Vec<AllocatedNum<Fp>> = inserted_path.siblings
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("sibling {}", i)),|| Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;

        let idx_var: Vec<AllocatedBit> = next_leaf_idx
            .into_iter()
            .enumerate()
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("idx {}", i)),Some(b)))
            .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
            .unwrap()
        ;
        
        // Check new_leaf is_member
        let is_valid = Boolean::from(is_member::<Fp, HEIGHT, TestConstraintSystem<Fp>>(&mut cs, root_var, val_var, idx_var, siblings_var).unwrap());
        Boolean::enforce_equal(&mut cs, &is_valid, &Boolean::constant(true)).unwrap();

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
        
    } 

    #[test]
    fn test_non_mem_circuit() {
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT> = IndexTree::new(empty_leaf.clone(), HEIGHT);
        println!("root is {:?}", tree.root);

        let low_leaf_idx = idx_to_bits(HEIGHT, Fp::zero()); // from root to leaf
        let low_leaf = empty_leaf.clone();
        let new_value = Fp::from(20 as u64);
        let next_insertion_index = Fp::one();
        let next_leaf_idx = idx_to_bits(HEIGHT, next_insertion_index);

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

        let mut cs = TestConstraintSystem::<Fp>::new();

        // Allocating all variables
        let root_var: AllocatedNum<Fp> = AllocatedNum::alloc_input(cs.namespace(|| "root"), || Ok(tree.root)).unwrap();
        
        let val_vec = Leaf::leaf_to_vec(&new_leaf); // val_vec = [value, next_value, next_index]
        let val_var: Vec<AllocatedNum<Fp>> = val_vec
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("leaf vec {}", i)), || Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;
        
        let siblings_var: Vec<AllocatedNum<Fp>> = inserted_path.siblings
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("sibling {}", i)),|| Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;

        let idx_var: Vec<AllocatedBit> = next_leaf_idx
            .into_iter()
            .enumerate()
            .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("idx {}", i)),Some(b)))
            .collect::<Result<Vec<AllocatedBit>, SynthesisError>>()
            .unwrap()
        ;
        let non_member = Fp::from(30u64);
        let alloc_non_member = AllocatedNum::alloc(cs.namespace(|| "non member"),|| Ok(non_member)).unwrap();
        // Check new_leaf is_non_member
        let is_non_member = is_non_member::<Fp, HEIGHT, TestConstraintSystem<Fp>>(
            &mut cs, root_var, val_var, 
            idx_var, siblings_var, 
            alloc_non_member);
        println!("is_non_member {:?}", is_non_member.unwrap().get_value());
        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_less_circuit() {
        let mut rng = rand::thread_rng();
        let in1 = Fp::random(&mut rng);
        let in2 = Fp::random(&mut rng);
        let mut cs = TestConstraintSystem::<Fp>::new();


        let in1_var: AllocatedNum<Fp> = AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();

        let in2_var: AllocatedNum<Fp> = AllocatedNum::alloc(cs.namespace(|| "in2"), || Ok(in2)).unwrap();

        println!("{:?} < {:?} {:?}", in1, in2, is_less(&mut cs, in1_var, in2_var).unwrap().get_value().unwrap());

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());
    } 

}