use pasta_curves::{
    group::ff::PrimeField,
};
use neptune::{
    Arity,
    circuit2::Elt, 
    poseidon::PoseidonConstants
};

use bellperson::{ConstraintSystem, SynthesisError, gadgets::num::AllocatedNum};

use neptune::sponge::{
    api::{SpongeAPI,IOPattern,SpongeOp},
    vanilla::{SpongeTrait,Mode},
    circuit::SpongeCircuit
};

pub fn hash_circuit<F: PrimeField, A: Arity<F>, CS: ConstraintSystem<F>>(cs: &mut CS, input: Vec<AllocatedNum<F>>, p: &PoseidonConstants<F, A>) -> Result<AllocatedNum<F>, SynthesisError> {

    let mut sponge = SpongeCircuit::<F, A, _>::new_with_constants(p, Mode::Simplex);
    
    let mut ns = cs.namespace(|| "ns");
    
    let val_var: Vec<Elt<F>> = input
        .clone()
        .into_iter()
        //.enumerate()
        .map(|s| Elt::Allocated(s))
        .collect()
    ;
    assert_eq!(val_var.len(),input.len());

    let acc = &mut ns;
    let parameter = IOPattern(vec![SpongeOp::Absorb(input.len() as u32), SpongeOp::Squeeze(1)]);

    sponge.start(parameter, None, acc);


    SpongeAPI::absorb(
        &mut sponge,
        input.len() as u32,
        val_var.as_slice(),
        acc,
    );

    let calc_node = SpongeAPI::squeeze(&mut sponge, 1, acc);

    assert_eq!(calc_node.len(),1);

    sponge.finish(acc).unwrap();

    calc_node[0].ensure_allocated(acc, true)
    
}


#[cfg(test)]
mod tests {
    use super::*;
    use pasta_curves::pallas::Base as Fp;
    use generic_array::typenum::{U2, U12};
    use bellperson::{util_cs::test_cs::TestConstraintSystem};
    use neptune::Strength;
    use neptune::sponge::vanilla::Sponge;
    use crate::hash::vanilla::hash;

    #[test]
    fn test_leaf_hash() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let inp = vec![Fp::from(123); 12];


        let inp_alloc: Vec<AllocatedNum<Fp>> = inp
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("val {}",i)),|| Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;

        let p = Sponge::<Fp, U12>::api_constants(Strength::Standard);
        let leaf_hash_out = hash_circuit::<Fp, U12, _>(&mut cs, inp_alloc, &p).unwrap();

        let exp_hash_out = hash::<Fp, U12>(inp.clone(), &p);  
        let exp_hash_out_var = AllocatedNum::alloc(cs.namespace(|| "hash node"), || Ok(exp_hash_out)).unwrap();

        cs.enforce(
            || "node = calc_node", 
            |lc| lc + leaf_hash_out.get_variable(), 
            |lc| lc + TestConstraintSystem::<Fp>::one(), 
            |lc| lc + exp_hash_out_var.get_variable()
        );

        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());

    }

    #[test]
    fn test_node_hash() {
        let mut cs = TestConstraintSystem::<Fp>::new();

        let inp = vec![
            Fp::from(1),
            Fp::from(2),
        ];

        let inp_alloc: Vec<AllocatedNum<Fp>> = inp
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, s)| AllocatedNum::alloc(cs.namespace(|| format!("val {}",i)),|| Ok(s)))
            .collect::<Result<Vec<AllocatedNum<Fp>>, SynthesisError>>()
            .unwrap()
        ;

        let p = Sponge::<Fp, U2>::api_constants(Strength::Standard);
        let node_hash_out = hash_circuit::<Fp, U2, _>(&mut cs, inp_alloc, &p).unwrap();

        let exp_hash_out = hash::<Fp, U2>(inp.clone(), &p);  
        let exp_hash_out_var = AllocatedNum::alloc(cs.namespace(|| "hash node"), || Ok(exp_hash_out)).unwrap();

        cs.enforce(
            || "node = calc_node", 
            |lc| lc + node_hash_out.get_variable(), 
            |lc| lc + TestConstraintSystem::<Fp>::one(), 
            |lc| lc + exp_hash_out_var.get_variable()
        );


        println!("the number of inputs are {:?}", cs.num_inputs());
        println!("the number of constraints are {}", cs.num_constraints());

        assert!(cs.is_satisfied());

    }
}