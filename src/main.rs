use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};

// a     b m s
// x     x 1 0
// x2    x 1 0
// x3    x 0 1
// x3+x  5 0 1
// x3+x+5

trait Ops<F: FieldExt> {
    type Num;
    fn load_private(&self, layouter: impl Layouter<F>, x: Option<F>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<F>, x: F) -> Result<Self::Num, Error>;
    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn add(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

struct MyChip<F: FieldExt> {
    config: MyConfig,
    _maker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for MyChip<F> {
    type Config = MyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

impl<F: FieldExt> Ops<F> for MyChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        v: Option<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(
                        || "private value",
                        config.advice[0],
                        0,
                        || v.ok_or(Error::Synthesis),
                    )
                    .map(Number)
            },
        )
    }

    fn load_constant(&self, mut layouter: impl Layouter<F>, v: F) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter
            .assign_region(
                || "load constant",
                |mut region| {
                    region.assign_advice_from_constant(|| "constant", config.advice[0], 0, v)
                },
            )
            .map(Number)
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter
            .assign_region(
                || "mul",
                |mut region| {
                    config.s_mul.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                    let v = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));
                    region.assign_advice(
                        || "lhs * rhs",
                        config.advice[0],
                        1,
                        || v.ok_or(Error::Synthesis),
                    )
                },
            )
            .map(Number)
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter
            .assign_region(
                || "add",
                |mut region| {
                    config.s_add.enable(&mut region, 0)?;

                    a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                    b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;
                    let v = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));
                    region.assign_advice(
                        || "lhs + rhs",
                        config.advice[0],
                        1,
                        || v.ok_or(Error::Synthesis),
                    )
                },
            )
            .map(Number)
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}

impl<F: FieldExt> MyChip<F> {
    fn new(config: MyConfig) -> Self {
        MyChip {
            config,
            _maker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);

        for adv in advice.iter() {
            meta.enable_equality(*adv);
        }

        let s_mul = meta.selector();
        let s_add = meta.selector();

        meta.create_gate("mul/add", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            let s_add = meta.query_selector(s_add);

            vec![
                s_mul * (lhs.clone() * rhs.clone() - out.clone()),
                s_add * (lhs + rhs - out),
            ]
        });

        MyConfig {
            advice,
            instance,
            s_mul,
            s_add,
        }
    }
}

#[derive(Clone, Debug)]
struct MyConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector,
}

#[derive(Default)]
struct MyCircuit<F: Field> {
    constant: F,
    x: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = MyConfig;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut halo2_proofs::plonk::ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        MyChip::configure(meta, advice, instance, constant)
    }

    // x^3 + x + 5 = 35
    // x2 = x*x
    // x3 = x2*x
    // x3_x = x3 + x
    // x3_x_5 = x3_x + 5
    // x3_x_5 == 35
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl halo2_proofs::circuit::Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let chip = MyChip::<F>::new(config);
        let x = chip.load_private(layouter.namespace(|| "load x"), self.x)?;
        let constant = chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let x2 = chip.mul(layouter.namespace(|| "x2"), x.clone(), x.clone())?;
        let x3 = chip.mul(layouter.namespace(|| "x3"), x2, x.clone())?;
        let x3_x = chip.add(layouter.namespace(|| "x3+x"), x3, x)?;
        let x3_x_5 = chip.add(layouter.namespace(|| "x3+x+5"), x3_x, constant)?;

        chip.expose_public(layouter.namespace(|| "expose_result"), x3_x_5, 0)
    }
}

fn main() {
    let x = Fp::from(3);
    let constant = Fp::from(5);
    let result = Fp::from(35);

    let circuit = MyCircuit {
        constant,
        x: Some(x),
    };

    let public_inputs = vec![result];

    // let prover = MockProver::run(4, &circuit, vec![public_inputs]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));

    // Create the area you want to draw on.
    // Use SVGBackend if you want to render to .svg instead.
    use plotters::prelude::*;
    let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Example Circuit Layout", ("sans-serif", 60))
        .unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        // You can optionally render only a section of the circuit.
        .view_width(0..2)
        .view_height(0..16)
        // You can hide labels, which can be useful with smaller areas.
        .show_labels(false)
        // Render the circuit onto your area!
        // The first argument is the size parameter for the circuit.
        .render(5, &circuit, &root)
        .unwrap();
}
