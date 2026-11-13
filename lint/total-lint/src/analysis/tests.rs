use super::*;
use acir::circuit::PublicInputs;
use acir::circuit::brillig::{BrilligBytecode, BrilligFunctionId};
use acir::circuit::opcodes::{AcirFunctionId, BlockId, BlockType, MemOp};

fn f(v: u128) -> FieldElement {
    FieldElement::from(v)
}

fn neg(v: u128) -> FieldElement {
    -FieldElement::from(v)
}

fn w(i: u32) -> Witness {
    Witness(i)
}

fn expr(
    mul: &[(FieldElement, u32, u32)],
    lin: &[(FieldElement, u32)],
    c: FieldElement,
) -> Expression<FieldElement> {
    Expression {
        mul_terms: mul.iter().map(|(k, a, b)| (*k, w(*a), w(*b))).collect(),
        linear_combinations: lin.iter().map(|(k, x)| (*k, w(*x))).collect(),
        q_c: c,
    }
}

fn range(x: u32, bits: u32) -> Opcode<FieldElement> {
    Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RANGE {
        input: FunctionInput::Witness(w(x)),
        num_bits: bits,
    })
}

fn brillig(
    id: u32,
    inputs: &[u32],
    outputs: &[u32],
    predicate: Expression<FieldElement>,
) -> Opcode<FieldElement> {
    Opcode::BrilligCall {
        id: BrilligFunctionId::new(id),
        inputs: inputs
            .iter()
            .map(|x| BrilligInputs::Single(expr(&[], &[(f(1), *x)], f(0))))
            .collect(),
        outputs: outputs
            .iter()
            .map(|x| BrilligOutputs::Simple(w(*x)))
            .collect(),
        predicate,
    }
}

fn circuit(params: &[u32], opcodes: Vec<Opcode<FieldElement>>) -> Circuit<FieldElement> {
    Circuit {
        function_name: "main".into(),
        opcodes,
        private_parameters: params.iter().map(|x| w(*x)).collect(),
        public_parameters: PublicInputs::default(),
        return_values: PublicInputs::default(),
        assert_messages: vec![],
    }
}

fn program(functions: Vec<Circuit<FieldElement>>, brillig_fns: usize) -> Program<FieldElement> {
    Program {
        functions,
        unconstrained_functions: (0..brillig_fns)
            .map(|i| BrilligBytecode {
                function_name: format!("hint{i}"),
                bytecode: vec![],
            })
            .collect(),
    }
}

/// Run the analysis with every opcode attributed to `origin`.
fn run_with(
    p: &Program<FieldElement>,
    origin: Origin,
    entry: &BTreeMap<u32, EntryParam>,
) -> Analysis {
    let messages = |_: u64| None;
    let origin = move |_: usize, _: usize| origin;
    let directives = directives(p);
    let ctx = Context {
        program: p,
        entry_params: entry,
        messages: &messages,
        origin: &origin,
        directives: &directives,
    };
    analyse(&ctx)
}

fn run(p: &Program<FieldElement>, origin: Origin) -> Analysis {
    run_with(p, origin, &BTreeMap::new())
}

fn classes(a: &Analysis) -> Vec<(Kind, Class)> {
    a.items.iter().map(|i| (i.kind, i.class)).collect()
}

#[test]
fn definition_then_input_assert() {
    // w2 = w0 + w1 (definition); w0 - w1 = 0 (assert on inputs).
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                Opcode::AssertZero(expr(&[], &[(f(1), 2), (neg(1), 0), (neg(1), 1)], f(0))),
                Opcode::AssertZero(expr(&[], &[(f(1), 0), (neg(1), 1)], f(0))),
            ],
        )],
        0,
    );
    let a = run(&p, Origin::User);
    assert_eq!(
        classes(&a),
        vec![
            (Kind::Definition, Class::Definition),
            (Kind::Assert, Class::InputFalsifiable)
        ]
    );
}

#[test]
fn library_provenance_whitelists_only_hint_class() {
    // A RANGE on a hint is whitelisted in the library and unreviewed
    // outside it; a RANGE on an input-derived value stays reported in
    // the library, under its own class.
    let ops = vec![
        brillig(0, &[0], &[2], Expression::one()),
        range(2, 8),
        Opcode::AssertZero(expr(&[], &[(f(1), 3), (neg(1), 0), (neg(1), 1)], f(0))),
        range(3, 8),
    ];
    let p = program(vec![circuit(&[0, 1], ops)], 1);
    let lib = run(&p, Origin::Library);
    assert_eq!(lib.items[1].class, Class::HintLibrary);
    assert_eq!(lib.items[3].class, Class::LibraryInputFalsifiable);
    let user = run(&p, Origin::User);
    assert_eq!(user.items[1].class, Class::HintUnreviewed);
    assert_eq!(user.items[3].class, Class::InputFalsifiable);
    assert!(lib.items[3].class.is_reported() && !lib.items[1].class.is_reported());
}

#[test]
fn typed_entry_range_is_always_reported() {
    let mut entry = BTreeMap::new();
    entry.insert(
        0,
        EntryParam {
            name: "amount".into(),
            ty: "u8".into(),
            width: Some(8),
        },
    );
    entry.insert(
        1,
        EntryParam {
            name: "x".into(),
            ty: "Field".into(),
            width: None,
        },
    );
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![range(0, 8), range(1, 8), range(0, 8)],
        )],
        0,
    );
    // Even when the location would be attributed to the library.
    let a = run_with(&p, Origin::Library, &entry);
    assert_eq!(a.items[0].class, Class::InputFalsifiable);
    assert!(a.items[0].entry_param);
    assert!(a.items[0].label.contains("amount: u8"));
    // A RANGE on a Field parameter is not the typed check.
    assert!(!a.items[1].entry_param);
    assert_eq!(a.items[1].class, Class::LibraryInputFalsifiable);
    // A repeated typed check is still reported, not marked implied.
    assert_eq!(a.items[2].class, Class::InputFalsifiable);
}

#[test]
fn inverse_nonzero_check_is_input_falsifiable() {
    // inv = hint(w0); w0 * inv - 1 = 0 fails at w0 = 0 whatever inv is.
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[], neg(1))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::Library);
    assert_eq!(a.items[1].class, Class::LibraryInputFalsifiable);
    assert!(a.items[1].why.iter().any(|s| s.contains("nonzero check")));
}

#[test]
fn is_zero_gadget_is_hint_class() {
    // inv = hint(x); z = 1 - x*inv (definition); x*z = 0 (hint-class).
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[(f(1), 2)], neg(1))),
                Opcode::AssertZero(expr(&[(f(1), 0, 2)], &[], f(0))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::Library);
    assert_eq!(
        classes(&a)[1..],
        [
            (Kind::Definition, Class::Definition),
            (Kind::Assert, Class::HintLibrary)
        ]
    );
}

#[test]
fn bounds_make_later_checks_implied() {
    // RANGE w0 8, RANGE w1 8, w2 = w0 + 2*w1 (< 2^10), RANGE w2 10 is
    // implied, RANGE w2 9 is not, RANGE w0 16 is implied.
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                range(0, 8),
                range(1, 8),
                Opcode::AssertZero(expr(&[], &[(f(1), 2), (neg(1), 0), (neg(2), 1)], f(0))),
                range(2, 10),
                range(2, 9),
                range(0, 16),
            ],
        )],
        0,
    );
    // Field parameters: their RANGEs are not typed entry checks.
    let field = |n: &str| EntryParam {
        name: n.into(),
        ty: "Field".into(),
        width: None,
    };
    let entry: BTreeMap<u32, EntryParam> = [(0, field("x")), (1, field("y"))].into_iter().collect();
    let a = run_with(&p, Origin::User, &entry);
    let c: Vec<Class> = a.items.iter().map(|i| i.class).collect();
    assert_eq!(
        c,
        vec![
            Class::InputFalsifiable,
            Class::InputFalsifiable,
            Class::Definition,
            Class::Implied,
            Class::InputFalsifiable,
            Class::Implied,
        ]
    );
}

#[test]
fn booleanity_bounds_a_hint() {
    // b = hint; b*b - b = 0; RANGE b 1 is then implied.
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 1, 1)], &[(neg(1), 1)], f(0))),
                range(1, 1),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::User);
    assert_eq!(a.items[1].class, Class::HintUnreviewed);
    assert_eq!(a.items[2].class, Class::Implied);
}

#[test]
fn constant_zero_predicates_neutralise() {
    let callee = circuit(&[0], vec![]);
    let msm = Opcode::BlackBoxFuncCall(BlackBoxFuncCall::MultiScalarMul {
        points: vec![
            FunctionInput::Witness(w(0)),
            FunctionInput::Witness(w(0)),
            FunctionInput::Constant(f(0)),
        ],
        scalars: vec![FunctionInput::Witness(w(0)), FunctionInput::Constant(f(0))],
        predicate: FunctionInput::Constant(f(0)),
        outputs: (w(5), w(6)),
    });
    let msm_live = Opcode::BlackBoxFuncCall(BlackBoxFuncCall::MultiScalarMul {
        points: vec![
            FunctionInput::Witness(w(0)),
            FunctionInput::Witness(w(0)),
            FunctionInput::Constant(f(0)),
        ],
        scalars: vec![FunctionInput::Witness(w(0)), FunctionInput::Constant(f(0))],
        predicate: FunctionInput::Witness(w(0)),
        outputs: (w(7), w(8)),
    });
    let main = circuit(
        &[0],
        vec![
            brillig(0, &[0], &[1], Expression::zero()),
            Opcode::Call {
                id: AcirFunctionId::new(1),
                inputs: vec![w(0)],
                outputs: vec![],
                predicate: Expression::zero(),
            },
            msm,
            msm_live,
        ],
    );
    let p = program(vec![main, callee], 1);
    let a = run(&p, Origin::User);
    let main_items: Vec<&Item> = a.items.iter().filter(|i| i.function == 0).collect();
    assert_eq!(main_items[0].class, Class::Neutralised);
    assert_eq!(main_items[1].class, Class::Neutralised);
    assert_eq!(main_items[2].class, Class::Neutralised);
    assert_eq!(main_items[3].class, Class::InputFalsifiable);
    assert_eq!(main_items[3].predicate.as_deref(), Some("w0"));
    assert!(a.brillig_calls[0].predicate_zero);
}

#[test]
fn memory_index_classes() {
    let init = Opcode::MemoryInit {
        block_id: BlockId::new(0),
        init: vec![w(0), w(0), w(0), w(0)],
        block_type: BlockType::Memory,
    };
    let read = |idx: u32, val: u32| Opcode::MemoryOp {
        block_id: BlockId::new(0),
        op: MemOp::read_at_mem_index(w(idx), w(val)),
    };
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                init,
                read(1, 10),
                // w2 = 3: constant index inside the block.
                Opcode::AssertZero(expr(&[], &[(f(1), 2)], neg(3))),
                read(2, 11),
                // w3 = 9: constant index outside the block.
                Opcode::AssertZero(expr(&[], &[(f(1), 3)], neg(9))),
                read(3, 12),
                // w1 bounded to 2 bits: in bounds whenever that RANGE passes.
                range(1, 2),
                read(1, 13),
                // Hint index.
                brillig(0, &[0], &[4], Expression::one()),
                read(4, 14),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::User);
    let mem: Vec<Class> = a
        .items
        .iter()
        .filter(|i| i.kind == Kind::MemoryRead)
        .map(|i| i.class)
        .collect();
    assert_eq!(
        mem,
        vec![
            Class::InputFalsifiable,
            Class::Neutralised,
            Class::InputFalsifiable,
            Class::Implied,
            Class::HintUnreviewed,
        ]
    );
}

#[test]
fn flattened_branch_assert_is_noted_not_separated() {
    // c*y - 3*c = 0: an assert(y == 3) under `if c`.
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![Opcode::AssertZero(expr(
                &[(f(1), 0, 1)],
                &[(neg(3), 1)],
                f(0),
            ))],
        )],
        0,
    );
    let a = run(&p, Origin::User);
    assert_eq!(a.items[0].class, Class::InputFalsifiable);
    assert!(
        a.items[0]
            .why
            .iter()
            .any(|s| s.contains("every term contains w1") && s.contains("does not separate"))
    );
}

#[test]
fn conditional_solve_and_unsolvable() {
    // w0*w2 - w1 = 0 solves w2 only when w0 != 0.
    // w3 + w4 = 0 has two unassigned witnesses.
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                Opcode::AssertZero(expr(&[(f(1), 0, 2)], &[(neg(1), 1)], f(0))),
                Opcode::AssertZero(expr(&[], &[(f(1), 3), (f(1), 4)], f(0))),
            ],
        )],
        0,
    );
    let a = run(&p, Origin::User);
    assert_eq!(
        classes(&a),
        vec![
            (Kind::ConditionalSolve, Class::InputFalsifiable),
            (Kind::Unsolvable, Class::Unsolvable)
        ]
    );
}

#[test]
fn solve_with_coefficient_forced_nonzero_is_a_definition() {
    // w0*w1 - 1 = 0 forces w0 != 0; then w0*w2 - w1 = 0 always solves w2.
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[], neg(1))),
                Opcode::AssertZero(expr(&[(f(1), 0, 2)], &[(neg(1), 1)], f(0))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::User);
    assert_eq!(a.items[2].kind, Kind::Definition);
}

#[test]
fn call_outputs_carry_callee_hint_taint() {
    // Function 1 returns a Brillig output; function 0 asserts on it.
    let mut callee = circuit(&[0], vec![brillig(0, &[0], &[1], Expression::one())]);
    callee.return_values = PublicInputs([w(1)].into_iter().collect());
    let main = circuit(
        &[0],
        vec![
            Opcode::Call {
                id: AcirFunctionId::new(1),
                inputs: vec![w(0)],
                outputs: vec![w(1)],
                predicate: Expression::one(),
            },
            Opcode::AssertZero(expr(&[], &[(f(1), 1), (neg(1), 0)], f(0))),
        ],
    );
    let p = program(vec![main, callee], 1);
    let a = run(&p, Origin::User);
    let main_items: Vec<&Item> = a.items.iter().filter(|i| i.function == 0).collect();
    assert_eq!(main_items[0].class, Class::Definition);
    assert_eq!(main_items[1].class, Class::HintUnreviewed);
    assert_eq!(a.acir_calls.len(), 1);
}

#[test]
fn constant_range_inputs() {
    let rc = |v: u128, bits: u32| {
        Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RANGE {
            input: FunctionInput::Constant(f(v)),
            num_bits: bits,
        })
    };
    let p = program(vec![circuit(&[], vec![rc(200, 8), rc(300, 8)])], 0);
    let a = run(&p, Origin::User);
    assert_eq!(a.items[0].class, Class::Neutralised);
    assert_eq!(a.items[1].class, Class::InputFalsifiable);
}

#[test]
fn logic_ops_check_input_width() {
    let and = |l: u32, r: u32, out: u32| {
        Opcode::BlackBoxFuncCall(BlackBoxFuncCall::AND {
            lhs: FunctionInput::Witness(w(l)),
            rhs: FunctionInput::Witness(w(r)),
            num_bits: 8,
            output: w(out),
        })
    };
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                and(0, 1, 2),
                range(0, 8),
                range(1, 8),
                and(0, 1, 3),
                range(3, 8),
            ],
        )],
        0,
    );
    let a = run(&p, Origin::User);
    let c: Vec<Class> = a.items.iter().map(|i| i.class).collect();
    assert_eq!(c[0], Class::InputFalsifiable);
    assert_eq!(c[3], Class::Implied);
    // The AND output is below 2^8 by construction.
    assert_eq!(c[4], Class::Implied);
}

#[test]
fn brillig_call_slots_record_nonzero_facts() {
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[], neg(1))),
                brillig(1, &[0, 1], &[2], Expression::one()),
            ],
        )],
        2,
    );
    let a = run(&p, Origin::User);
    assert_eq!(a.brillig_calls[0].slot_nonzero, vec![false]);
    assert_eq!(a.brillig_calls[1].slot_nonzero, vec![true, true]);
}

#[test]
fn inequality_with_constant_is_input_falsifiable() {
    // inv = hint(w0 - 5); (w0 - 5)*inv - 1 = 0 fails at w0 = 5 whatever inv is.
    let p = program(
        vec![circuit(
            &[0],
            vec![
                brillig(0, &[0], &[1], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[(neg(5), 1)], neg(1))),
                // The same shape with a hint-derived cofactor stays hint-class.
                brillig(0, &[0], &[2], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 2, 1)], &[(neg(5), 1)], neg(1))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::Library);
    assert_eq!(a.items[1].class, Class::LibraryInputFalsifiable);
    assert!(
        a.items[1]
            .why
            .iter()
            .any(|s| s.contains("linear form in w0"))
    );
    assert_eq!(a.items[3].class, Class::HintLibrary);
    assert!(a.items[3].why.iter().any(|s| s.contains("nonzero check")));
}

fn ecdsa(
    input: FunctionInput<FieldElement>,
    predicate: FunctionInput<FieldElement>,
    out: u32,
) -> Opcode<FieldElement> {
    Opcode::BlackBoxFuncCall(BlackBoxFuncCall::EcdsaSecp256k1 {
        public_key_x: Box::new([input; 32]),
        public_key_y: Box::new([input; 32]),
        signature: Box::new([input; 64]),
        hashed_message: Box::new([input; 32]),
        predicate,
        output: w(out),
    })
}

#[test]
fn ecdsa_is_backend_defined_not_a_silent_definition() {
    let mut entry = BTreeMap::new();
    entry.insert(
        0,
        EntryParam {
            name: "b".into(),
            ty: "u8".into(),
            width: Some(8),
        },
    );
    entry.insert(
        1,
        EntryParam {
            name: "x".into(),
            ty: "Field".into(),
            width: None,
        },
    );
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                range(0, 8),
                // Byte inputs: holds at witness generation, backend may fail.
                ecdsa(
                    FunctionInput::Witness(w(0)),
                    FunctionInput::Constant(f(1)),
                    5,
                ),
                // Predicate 0: skipped.
                ecdsa(
                    FunctionInput::Witness(w(0)),
                    FunctionInput::Constant(f(0)),
                    6,
                ),
                // Unbounded inputs: the byte-width requirement is input-falsifiable.
                ecdsa(
                    FunctionInput::Witness(w(1)),
                    FunctionInput::Constant(f(1)),
                    7,
                ),
            ],
        )],
        0,
    );
    let a = run_with(&p, Origin::User, &entry);
    assert_eq!(a.items[1].class, Class::BackendDefined);
    assert!(!a.items[1].class.is_reported());
    assert!(a.items[1].why.iter().any(|s| s.contains("backend-defined")));
    assert_eq!(a.items[2].class, Class::Neutralised);
    assert_eq!(a.items[3].class, Class::InputFalsifiable);
    assert!(a.items[3].why.iter().any(|s| s.contains("backend-defined")));
}

fn recagg(proof: u32, predicate: FunctionInput<FieldElement>) -> Opcode<FieldElement> {
    Opcode::BlackBoxFuncCall(BlackBoxFuncCall::RecursiveAggregation {
        verification_key: vec![FunctionInput::Witness(w(proof)); 4],
        proof: vec![FunctionInput::Witness(w(proof)); 4],
        public_inputs: vec![FunctionInput::Witness(w(proof))],
        key_hash: FunctionInput::Witness(w(proof)),
        proof_type: 6,
        predicate,
    })
}

// The ACVM never checks the proof; the backend proves with the predicate
// 0 whatever the proof and cannot prove with it 1 and a bad proof. So the
// opcode is a reported failure source, backend-defined, with its
// predication named.
#[test]
fn recursive_aggregation_is_backend_defined_and_names_its_predicate() {
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                brillig(0, &[1], &[2], Expression::one()),
                // skipped: constant-zero predicate
                recagg(1, FunctionInput::Constant(f(0))),
                // predicated on the runtime flag w0
                recagg(1, FunctionInput::Witness(w(0))),
                // unpredicated
                recagg(1, FunctionInput::Constant(f(1))),
                // proof from a hint (a capsule), predicated
                recagg(2, FunctionInput::Witness(w(0))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::User);
    assert_eq!(a.items[1].class, Class::Neutralised);
    for i in [2, 3] {
        assert_eq!(a.items[i].class, Class::InputFalsifiable);
        assert!(a.items[i].class.is_reported());
        assert!(
            a.items[i]
                .why
                .iter()
                .any(|s| s.starts_with("backend-defined"))
        );
    }
    assert!(
        a.items[2]
            .why
            .iter()
            .any(|s| s.starts_with("predicated on w0"))
    );
    assert!(a.items[3].why.iter().any(|s| s.starts_with("unpredicated")));
    assert_eq!(a.items[4].class, Class::HintUnreviewed);
    assert!(
        a.items[4]
            .why
            .iter()
            .any(|s| s.starts_with("predicated on w0"))
    );
}

#[test]
fn asserted_comparison_is_pinned_even_in_the_library() {
    // assert(a < b) on u64: w5 = hint borrow; w6 = w0 - w1 - 2^64*w5 + 2^64;
    // RANGE 64 w6; then the pin w5 = 0. assert(flag) on a hint-derived
    // flag: w7 = 1 - w5 (definition), w7 = 1.
    let two64 = f(1u128 << 64);
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                brillig(0, &[0, 1], &[5], Expression::one()),
                Opcode::AssertZero(expr(
                    &[],
                    &[(f(1), 6), (neg(1), 0), (f(1), 1), (two64, 5)],
                    -two64,
                )),
                range(6, 64),
                Opcode::AssertZero(expr(&[], &[(f(1), 5)], f(0))),
                Opcode::AssertZero(expr(&[], &[(f(1), 7), (f(1), 5)], neg(1))),
                Opcode::AssertZero(expr(&[], &[(f(1), 7)], neg(1))),
            ],
        )],
        1,
    );
    for origin in [Origin::Library, Origin::User, Origin::Compiler] {
        let a = run(&p, origin);
        assert_eq!(a.items[3].class, Class::HintPinned);
        assert!(a.items[3].class.is_reported());
        assert!(a.items[3].why.iter().any(|s| s.contains("pins w5")));
        assert_eq!(a.items[5].class, Class::HintPinned);
    }
    // In the library the comparison's range check stays whitelisted.
    assert_eq!(run(&p, Origin::Library).items[2].class, Class::HintLibrary);
}

#[test]
fn pin_under_an_input_branch_condition_is_pinned() {
    // if c { assert(a <= b) }: c*w5 - c = 0 with w5 a Brillig output and c
    // a parameter. The same product with a defined witness (the is-zero
    // gadget), a hint-derived condition, or booleanity is not a pin.
    let p = program(
        vec![circuit(
            &[0, 1, 2],
            vec![
                brillig(0, &[0, 1], &[5], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 2, 5)], &[(neg(1), 2)], f(0))),
                // c*w5 = 0
                Opcode::AssertZero(expr(&[(f(1), 2, 5)], &[], f(0))),
                // inv = hint(x); z = 1 - x*inv; x*z = 0
                brillig(0, &[0], &[6], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 0, 6)], &[(f(1), 7)], neg(1))),
                Opcode::AssertZero(expr(&[(f(1), 0, 7)], &[], f(0))),
                // w8 = hint; w8*w5 - w8 = 0: the condition is hint-derived
                brillig(0, &[0], &[8], Expression::one()),
                Opcode::AssertZero(expr(&[(f(1), 8, 5)], &[(neg(1), 8)], f(0))),
                // booleanity of w5
                Opcode::AssertZero(expr(&[(f(1), 5, 5)], &[(neg(1), 5)], f(0))),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::Library);
    assert_eq!(a.items[1].class, Class::HintPinned);
    assert!(
        a.items[1]
            .why
            .iter()
            .any(|s| s.contains("pins w5") && s.contains("whenever w2"))
    );
    assert_eq!(a.items[2].class, Class::HintPinned);
    assert_eq!(a.items[5].class, Class::HintLibrary);
    assert_eq!(a.items[7].class, Class::HintLibrary);
    assert_eq!(a.items[8].class, Class::HintLibrary);
}

#[test]
fn read_into_an_assigned_witness_checks_the_value() {
    // Block of inputs; w2 = 1 is a constant in-bounds index. A read into a
    // fresh witness cannot fail; a read into an assigned one compares the
    // value with the stored element.
    let init = Opcode::MemoryInit {
        block_id: BlockId::new(0),
        init: vec![w(0), w(0)],
        block_type: BlockType::Memory,
    };
    let read = |idx: u32, val: u32| Opcode::MemoryOp {
        block_id: BlockId::new(0),
        op: MemOp::read_at_mem_index(w(idx), w(val)),
    };
    let p = program(
        vec![circuit(
            &[0, 1],
            vec![
                init,
                Opcode::AssertZero(expr(&[], &[(f(1), 2)], neg(1))),
                read(2, 10),
                read(2, 1),
                brillig(0, &[0], &[3], Expression::one()),
                read(2, 3),
            ],
        )],
        1,
    );
    let a = run(&p, Origin::User);
    let mem: Vec<Class> = a
        .items
        .iter()
        .filter(|i| i.kind == Kind::MemoryRead)
        .map(|i| i.class)
        .collect();
    assert_eq!(
        mem,
        vec![
            Class::Neutralised,
            Class::InputFalsifiable,
            Class::HintUnreviewed
        ]
    );
}

/// Run with Brillig function ids mapped to directives, bypassing the
/// bytecode check (compiled fixtures cover that).
fn run_directives(p: &Program<FieldElement>, ds: &[(u32, Directive)]) -> Analysis {
    let messages = |_: u64| None;
    let origin = |_: usize, _: usize| Origin::User;
    let directives: BTreeMap<u32, Directive> = ds.iter().copied().collect();
    let entry = BTreeMap::new();
    let ctx = Context {
        program: p,
        entry_params: &entry,
        messages: &messages,
        origin: &origin,
        directives: &directives,
    };
    analyse(&ctx)
}

fn lin(terms: &[(FieldElement, u32)], c: FieldElement) -> Expression<FieldElement> {
    expr(&[], terms, c)
}

fn call(
    id: u32,
    inputs: Vec<Expression<FieldElement>>,
    outputs: Vec<BrilligOutputs>,
    predicate: Expression<FieldElement>,
) -> Opcode<FieldElement> {
    Opcode::BrilligCall {
        id: BrilligFunctionId::new(id),
        inputs: inputs.into_iter().map(BrilligInputs::Single).collect(),
        outputs,
        predicate,
    }
}

fn simple(ws: &[u32]) -> Vec<BrilligOutputs> {
    ws.iter().map(|x| BrilligOutputs::Simple(w(*x))).collect()
}

/// z = invert(w0 - 5); y = 1 - (w0 - 5)*z; then `pin`.
fn is_zero_ops(
    predicate: Expression<FieldElement>,
    pin: Opcode<FieldElement>,
) -> Vec<Opcode<FieldElement>> {
    vec![
        call(0, vec![lin(&[(f(1), 0)], neg(5))], simple(&[1]), predicate),
        // y = -w0*z + 5*z + 1
        Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[(neg(5), 1), (f(1), 2)], neg(1))),
        pin,
    ]
}

#[test]
fn is_zero_gadget_is_hint_compiler() {
    // (w0 - 5) * y = 0, written as a multiple.
    let pin = Opcode::AssertZero(expr(&[(f(3), 0, 2)], &[(neg(15), 2)], f(0)));
    let p = program(
        vec![circuit(&[0], is_zero_ops(Expression::one(), pin.clone()))],
        1,
    );
    let a = run_directives(&p, &[(0, Directive::Invert)]);
    assert_eq!(a.items[2].class, Class::HintCompiler);
    assert!(a.items[2].why.iter().any(|w| w.contains("is-zero")));
    // Not a directive: the same constraints stay hint-unreviewed.
    assert_eq!(
        run_directives(&p, &[]).items[2].class,
        Class::HintUnreviewed
    );
    // A call that may be skipped (witness predicate) gives no honest value.
    let p = program(
        vec![circuit(&[0, 3], is_zero_ops(lin(&[(f(1), 3)], f(0)), pin))],
        1,
    );
    let a = run_directives(&p, &[(0, Directive::Invert)]);
    assert_eq!(a.items[2].class, Class::HintUnreviewed);
    // x != 5 asserted through the inverse stays input-falsifiable.
    let nonzero = Opcode::AssertZero(expr(&[(f(1), 0, 1)], &[(neg(5), 1)], neg(1)));
    let p = program(
        vec![circuit(
            &[0],
            vec![
                call(
                    0,
                    vec![lin(&[(f(1), 0)], neg(5))],
                    simple(&[1]),
                    Expression::one(),
                ),
                nonzero,
            ],
        )],
        1,
    );
    let a = run_directives(&p, &[(0, Directive::Invert)]);
    assert_eq!(a.items[1].class, Class::InputFalsifiable);
}

/// `x*x - x = 0`.
fn booleanity(x: u32) -> Opcode<FieldElement> {
    Opcode::AssertZero(expr(&[(f(1), x, x)], &[(neg(1), x)], f(0)))
}

#[test]
fn booleanity_is_hint_compiler_only_for_bits_the_circuit_computes() {
    // y = is_zero(w0 - 5) (w2), y' = is_zero(w0 - 7) (w5), h = hint1(w0)
    // (w6, not a directive).
    let mut ops = is_zero_ops(Expression::one(), booleanity(2));
    ops.extend([
        call(
            0,
            vec![lin(&[(f(1), 0)], neg(7))],
            simple(&[4]),
            Expression::one(),
        ),
        Opcode::AssertZero(expr(&[(f(1), 0, 4)], &[(neg(7), 4), (f(1), 5)], neg(1))),
        brillig(1, &[0], &[6], Expression::one()),
        // s = y*h (w7): the hint selected by the flag, as `if x == 5 { h }
        // else { 0 }` lowers.
        Opcode::AssertZero(expr(&[(f(1), 2, 6)], &[(neg(1), 7)], f(0))),
        booleanity(7),
        // The same assertion again: the first one bounds s, so it is
        // implied by an item already reported, and hint-compiler.
        booleanity(7),
        // k = y + y' - 2*y*y' (w8), their exclusive or.
        Opcode::AssertZero(expr(
            &[(neg(2), 2, 5)],
            &[(f(1), 2), (f(1), 5), (neg(1), 8)],
            f(0),
        )),
        booleanity(8),
        // m = y + y' (w9): 2 when both are 1.
        Opcode::AssertZero(lin(&[(f(1), 2), (f(1), 5), (neg(1), 9)], f(0))),
        booleanity(9),
    ]);
    let p = program(vec![circuit(&[0], ops)], 2);
    let a = run_directives(&p, &[(0, Directive::Invert)]);
    let asserts: Vec<(u32, Class)> = a
        .items
        .iter()
        .filter(|i| i.kind == Kind::Assert)
        .map(|i| (i.opcode as u32, i.class))
        .collect();
    use Class::*;
    assert_eq!(
        asserts,
        [
            (2, HintCompiler),
            (7, HintUnreviewed),
            (8, HintCompiler),
            (10, HintCompiler),
            (12, HintUnreviewed),
        ]
    );
    assert!(
        a.items[10]
            .why
            .iter()
            .any(|w| w.contains("every 0/1 value"))
    );
    // Not a directive: the flag's own booleanity is unreviewed too.
    let a = run_directives(&p, &[]);
    assert_eq!(a.items[2].class, HintUnreviewed);
}

/// (q, r) = quotient(w0 + offset, b) with w0 bounded by `bound` bits.
fn quotient_ops(
    b: Expression<FieldElement>,
    rest: Vec<Opcode<FieldElement>>,
) -> Vec<Opcode<FieldElement>> {
    let mut ops = vec![call(
        1,
        vec![lin(&[(f(1), 0)], f(0)), b],
        simple(&[1, 2]),
        Expression::one(),
    )];
    ops.extend(rest);
    ops
}

#[test]
fn integer_quotient_by_a_constant_is_hint_compiler() {
    // Field as u8: q < 2^246, r < 2^8, r = w0 - 256*q.
    let identity = Opcode::AssertZero(lin(&[(f(1), 2), (neg(1), 0), (f(256), 1)], f(0)));
    let ops = quotient_ops(
        lin(&[], f(256)),
        vec![range(1, 246), range(2, 8), identity.clone(), range(1, 8)],
    );
    let p = program(vec![circuit(&[0], ops)], 2);
    let a = run_directives(&p, &[(1, Directive::IntegerQuotient)]);
    assert_eq!(
        classes(&a)[1..],
        [
            (Kind::Range, Class::HintCompiler),
            (Kind::Range, Class::HintCompiler),
            (Kind::Assert, Class::HintCompiler),
            // q of an unbounded Field does not fit 8 bits.
            (Kind::Range, Class::HintUnreviewed),
        ]
    );
    // A witness divisor is not recognised.
    let ops = quotient_ops(lin(&[(f(1), 3)], f(0)), vec![range(2, 8), identity]);
    let p = program(vec![circuit(&[0, 3], ops)], 2);
    let a = run_directives(&p, &[(1, Directive::IntegerQuotient)]);
    assert_eq!(a.items[1].class, Class::HintUnreviewed);
    assert_eq!(a.items[2].class, Class::HintUnreviewed);
}

#[test]
fn quotient_range_uses_the_dividend_bound() {
    // w0 < 2^32: q = w0 / 4 fits 30 bits but not 29.
    let ops = vec![
        range(0, 32),
        call(
            1,
            vec![lin(&[(f(1), 0)], f(0)), lin(&[], f(4))],
            simple(&[1, 2]),
            Expression::one(),
        ),
        range(1, 30),
        range(1, 29),
    ];
    let p = program(vec![circuit(&[0], ops)], 2);
    let a = run_directives(&p, &[(1, Directive::IntegerQuotient)]);
    assert_eq!(a.items[2].class, Class::HintCompiler);
    assert_eq!(a.items[3].class, Class::HintUnreviewed);
}

fn radix_ops(bound: Option<u32>, limbs: u32) -> Vec<Opcode<FieldElement>> {
    let mut ops: Vec<Opcode<FieldElement>> = bound.map(|b| range(0, b)).into_iter().collect();
    let outs: Vec<u32> = (1..=limbs).collect();
    ops.push(call(
        2,
        vec![
            lin(&[(f(1), 0)], f(0)),
            lin(&[], f(limbs as u128)),
            lin(&[], f(256)),
        ],
        vec![BrilligOutputs::Array(outs.iter().map(|x| w(*x)).collect())],
        Expression::one(),
    ));
    ops.extend(outs.iter().map(|x| range(*x, 8)));
    // d0 + 256 d1 + ... - w0 = 0
    let mut terms: Vec<(FieldElement, u32)> = vec![(neg(1), 0)];
    let mut k = FieldElement::one();
    for x in &outs {
        terms.push((k, *x));
        k = k * f(256);
    }
    ops.push(Opcode::AssertZero(lin(&terms, f(0))));
    ops
}

#[test]
fn radix_decomposition_recomposes_only_at_full_width_or_a_bounded_input() {
    let last = |a: &Analysis| a.items.last().unwrap().class;
    // Four bytes of an unbounded Field: the digits are in range, but they
    // do not recompose every input.
    let p = program(vec![circuit(&[0], radix_ops(None, 4))], 3);
    let a = run_directives(&p, &[(2, Directive::ToRadix)]);
    assert!(a.items[1..5].iter().all(|i| i.class == Class::HintCompiler));
    assert_eq!(last(&a), Class::HintUnreviewed);
    // ... of a 32-bit value: total.
    let p = program(vec![circuit(&[0], radix_ops(Some(32), 4))], 3);
    assert_eq!(
        last(&run_directives(&p, &[(2, Directive::ToRadix)])),
        Class::HintCompiler
    );
    // ... of a 33-bit value: not.
    let p = program(vec![circuit(&[0], radix_ops(Some(33), 4))], 3);
    assert_eq!(
        last(&run_directives(&p, &[(2, Directive::ToRadix)])),
        Class::HintUnreviewed
    );
    // 32 bytes hold every Field.
    let p = program(vec![circuit(&[0], radix_ops(None, 32))], 3);
    assert_eq!(
        last(&run_directives(&p, &[(2, Directive::ToRadix)])),
        Class::HintCompiler
    );
}

#[test]
fn truncation_check_after_a_field_to_u8_cast() {
    // The lowering of `x as u8` for a Field x (nargo 1.0.0-rc.3): q, r =
    // quotient(x, 256); t = Q - q with Q = (p - 1) / 256; y = is_zero(t);
    // t*y = 0; r*y = 0 (when q = Q the remainder must be 0).
    let qmax = FieldElement::from_be_bytes_reduce(&{
        let p_minus_1 = (-FieldElement::one()).to_be_bytes();
        // (p - 1) / 256: drop the last byte (p - 1 ends in 0x00).
        let mut v = vec![0u8];
        v.extend_from_slice(&p_minus_1[..p_minus_1.len() - 1]);
        v
    });
    let identity = Opcode::AssertZero(lin(&[(f(1), 2), (neg(1), 0), (f(256), 1)], f(0)));
    let ops = vec![
        call(
            1,
            vec![lin(&[(f(1), 0)], f(0)), lin(&[], f(256))],
            simple(&[1, 2]),
            Expression::one(),
        ),
        range(1, 246),
        range(2, 8),
        identity,
        // t = Q - q
        Opcode::AssertZero(lin(&[(f(1), 3), (f(1), 1)], -qmax)),
        range(3, 246),
        call(
            0,
            vec![lin(&[(neg(1), 1)], qmax)],
            simple(&[4]),
            Expression::one(),
        ),
        // y = 1 - t*z = 1 + q*z - Q*z
        Opcode::AssertZero(expr(&[(neg(1), 1, 4)], &[(qmax, 4), (f(1), 5)], neg(1))),
        // t*y = 0
        Opcode::AssertZero(expr(&[(neg(1), 1, 5)], &[(qmax, 5)], f(0))),
        // r*y = 0
        Opcode::AssertZero(expr(&[(f(1), 2, 5)], &[], f(0))),
        // r*y + y = 0 does not hold when y = 1.
        Opcode::AssertZero(expr(&[(f(1), 2, 5)], &[(f(1), 5)], f(0))),
    ];
    let p = program(vec![circuit(&[0], ops)], 2);
    let a = run_directives(
        &p,
        &[(0, Directive::Invert), (1, Directive::IntegerQuotient)],
    );
    let got: Vec<Class> = a.items.iter().map(|i| i.class).collect();
    use Class::*;
    assert_eq!(
        got,
        [
            Definition,
            HintCompiler,
            HintCompiler,
            HintCompiler,
            Definition,
            HintCompiler,
            Definition,
            Definition,
            HintCompiler,
            HintCompiler,
            HintUnreviewed
        ]
    );
    assert!(
        a.items[9]
            .why
            .iter()
            .any(|w| w.contains("truncation-check"))
    );
}

#[test]
fn user_functions_named_like_directives_are_not_recognised() {
    let mut p = program(vec![circuit(&[0], vec![])], 1);
    p.unconstrained_functions[0].function_name = "directive_invert".into();
    assert!(directives(&p).is_empty());
    assert!(compiler::recognised_bytecode(Directive::Invert).len() == 9);
}
