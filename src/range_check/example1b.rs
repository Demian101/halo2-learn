use std::marker::PhantomData;
use ff::{Field, PrimeField};
use halo2_proofs::{
  circuit::{
    floor_planner::V1,
    AssignedCell, 
    Layouter,
    Value,
  },
  plonk::{
    Advice,
    Assigned, 
    Circuit, 
    Column, 
    ConstraintSystem,
    Constraints, 
    Error,  
    Expression, 
    Selector, 
  },
  poly::Rotation, 
};

#[derive(Clone)]
struct MyConfig<F: PrimeField, const RANGE: usize> {
    advice_column: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>,
}

// By convention(按照惯例) the Config gets a `configure` and `assign` method, 
// which are delegated to by the configure() and synthesize() method of the Circuit.
impl<F: PrimeField, const RANGE: usize> MyConfig<F, RANGE> {}

#[derive(Default)] 
struct MyCircuit<F: PrimeField, const RANGE: usize> {
    assigned_value: Value<Assigned<F>>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const RANGE: usize> Circuit<F> for MyCircuit<F, RANGE> {
    type Config = MyConfig<F, RANGE>;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default() // should fill all the Witness Values with None/Unknown.
    }

    // define the constraints, mutate the provided ConstraintSystem, and output the resulting FrameType
    fn configure(cs: &mut ConstraintSystem<F>) -> Self::Config {
        let advice_column = cs.advice_column();
        let q_range_check = cs.selector();

        cs.create_gate("range check", |virtual_cells| {
            let q = virtual_cells.query_selector(q_range_check);
            let value = virtual_cells.query_advice(advice_column, Rotation::cur());

            // Given a range R and a value v, returns the expression
            // (v) * (1 - v) * (2 - v) * ... * (R - 1 - v)
            let rc_polynomial = (1..RANGE).fold(value.clone(), |expr, i| {
                expr * (Expression::Constant(F::from(i as u64)) - value.clone())
            });

            Constraints::with_selector(q, [("range check", rc_polynomial)])
        });

        // The "FrameType"
        Self::Config {
            q_range_check,
            advice_column,
            _marker: PhantomData,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>, // layouter is our 'write buffer' for the circuit
    ) -> Result<(), Error> {

        layouter.assign_region(
            || "Assign value", // the name of the region
            |mut region| {
                let offset = 0;

                // Enable q_range_check. Remember that q_range_check is a label, a Selector.  Calling its enable
                // - calls region.enable_selector(_,q_range_check,offset)  which
                // - calls enable_selector on the region's RegionLayouter which
                // - calls enable_selector on its "CS" (actually an Assignment<F> (a trait), and whatever impls that
                // does the work, for example for MockProver the enable_selector function does some checks and then sets
                //   self.selectors[selector.0][row] = true;
                config.q_range_check.enable(&mut region, offset)?;

                // Similarly after indirection calls assign_advice in e.g. the MockProver, which
                // takes a Value-producing to() and does something like
                // CellValue::Assigned(to().into_field().evaluate().assign()?);
                region.assign_advice(
                    || "value",
                    config.advice_column,
                    offset,
                    || self.assigned_value,
                )
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[test]
    fn test_range_check_1() {
        let k = 4; //2^k rows
        const RANGE: usize = 8; // 3-bit value
        let testvalue: u64 = 22;

        // Successful cases
        for i in 0..RANGE {
            let circuit = MyCircuit::<Fp, RANGE> {
                assigned_value: Value::known(Fp::from(i as u64).into()),
                _marker: PhantomData,
            };

            // The MockProver arguments are log_2(nrows), the circuit (with advice already assigned), and the instance variables.
            // The MockProver will need to internally supply a Layouter for the constraint system to be actually written.

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // Out-of-range `value = 8`
        {
            let circuit = MyCircuit::<Fp, RANGE> {
                assigned_value: Value::known(Fp::from(testvalue).into()),
                _marker: PhantomData,
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "range check").into(), 0, "range check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "Assign value").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x16".to_string())]
                }])
            );
        }
    }
}
