use super::*;

struct TestRng(u64);

impl TestRng {
    fn next(&mut self, upper: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 as usize % upper
    }
}

fn naive_matrix(circuit: &Circuit, gate_indices: &[usize], support: &[Qubit]) -> UnitaryMatrix {
    let mut matrix = UnitaryMatrix::identity(support.len()).unwrap();
    for &gate_index in gate_indices {
        matrix.apply_gate_left(&circuit.gates[gate_index], support);
    }
    matrix
}

fn assert_matrix_close(actual: &UnitaryMatrix, expected: &UnitaryMatrix) {
    assert_eq!(actual.num_qubits(), expected.num_qubits());
    for (index, (a, b)) in actual
        .as_slice()
        .iter()
        .zip(expected.as_slice())
        .enumerate()
    {
        let delta = Complex64::new(a.re - b.re, a.im - b.im);
        assert!(
            delta.norm_sqr() < 1e-20,
            "matrix entry {index} differs: {a:?} != {b:?}"
        );
    }
}

fn naive_windows(
    circuit: &Circuit,
    max_qubits: usize,
    max_gates: usize,
) -> Vec<(Vec<usize>, Vec<Qubit>)> {
    let mut result = Vec::new();
    for anchor in 0..circuit.gates.len() {
        let mut previous_indices = Vec::new();
        for end in anchor..circuit.gates.len() {
            let mut indices = vec![anchor];
            let mut qubits: Vec<Qubit> = unique_qubits(&circuit.gates[anchor]).to_vec();
            loop {
                let mut changed = false;
                for gate_index in anchor..=end {
                    if indices.binary_search(&gate_index).is_ok() {
                        continue;
                    }
                    let gate_qubits = unique_qubits(&circuit.gates[gate_index]);
                    if gate_qubits
                        .iter()
                        .any(|qubit| qubits.binary_search(qubit).is_ok())
                    {
                        let position = indices.binary_search(&gate_index).unwrap_err();
                        indices.insert(position, gate_index);
                        qubits = union_qubits(&qubits, &gate_qubits);
                        changed = true;
                    }
                }
                if !changed {
                    break;
                }
            }

            if indices.len() > max_gates || qubits.len() > max_qubits {
                break;
            }
            if indices != previous_indices {
                previous_indices = indices.clone();
                result.push((indices.clone(), qubits));
            }
            if indices.len() == max_gates {
                break;
            }
        }
    }
    result.sort_by(|left, right| left.0.cmp(&right.0));
    result
}

#[test]
fn disjoint_prefix_can_be_connected_by_later_gate() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::h(1));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });

    let result = SuperOpt::analyzer(2, 3).run(&circuit).unwrap();
    let window = result
        .subcircuits
        .iter()
        .find(|window| window.gate_indices == [0, 1, 2])
        .unwrap();
    assert_eq!(window.qubits, vec![0, 1]);
    let expected = naive_matrix(&circuit, &[0, 1, 2], &[0, 1]);
    assert_matrix_close(&window.matrix, &expected);
}

#[test]
fn emits_one_window_per_anchor_not_all_combinations() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::s(0));
    circuit.apply(Gate::t(0));

    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    let indices: Vec<_> = result
        .subcircuits
        .iter()
        .map(|window| window.gate_indices.clone())
        .collect();
    assert_eq!(
        indices,
        vec![
            vec![0],
            vec![0, 1],
            vec![1],
            vec![1, 2],
            vec![2],
            vec![2, 3],
            vec![3],
        ]
    );
}

#[test]
fn disconnected_completed_window_is_not_emitted() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(1));

    let result = SuperOpt::analyzer(2, 2).run(&circuit).unwrap();
    assert!(
        !result
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0, 1])
    );
}

#[test]
fn unrelated_gates_are_skipped_until_anchor_reconnects() {
    let mut circuit = Circuit::new(3);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(2));
    circuit.apply(Gate::z(2));
    circuit.apply(Gate::h(0));

    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    assert!(
        result
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0, 3])
    );
}

#[test]
fn bridge_pulls_in_entire_intervening_component() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::h(1));
    circuit.apply(Gate::x(1));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });

    let three_gate = SuperOpt::analyzer(2, 3).run(&circuit).unwrap();
    assert!(
        !three_gate
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0, 1, 3])
    );
    assert!(
        three_gate
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [1, 2, 3])
    );

    let four_gate = SuperOpt::analyzer(2, 4).run(&circuit).unwrap();
    assert!(
        four_gate
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0, 1, 2, 3])
    );
}

#[test]
fn over_width_partial_window_is_dropped() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });
    circuit.apply(Gate::t(0));

    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    assert!(
        result
            .subcircuits
            .iter()
            .all(|window| window.gate_indices.len() == 1)
    );
}

#[test]
fn canonical_cache_reuses_shifted_windows() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::h(1));
    circuit.apply(Gate::x(1));

    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    assert_eq!(result.subcircuits.len(), 6);
    assert_eq!(result.cache_hits, 3);
    assert_eq!(result.cache_misses, 3);
    assert!(Arc::ptr_eq(
        &result.subcircuits[1].matrix,
        &result.subcircuits[4].matrix
    ));
}

fn synthesis_table(max_qubits: usize, max_gates: usize) -> Arc<UnitaryCircuitTable> {
    Arc::new(
        UnitaryCircuitTable::build(SuperOptTableConfig {
            max_qubits,
            max_gates,
            max_entries_per_qubit: 20_000,
        })
        .unwrap(),
    )
}

fn single_qubit_matrix(gates: &[Gate]) -> UnitaryMatrix {
    let mut matrix = UnitaryMatrix::identity(1).unwrap();
    for gate in gates {
        matrix.apply_gate_left(gate, &[0]);
    }
    matrix
}

#[test]
fn qubit_zero_is_the_most_significant_basis_bit() {
    let mut matrix = UnitaryMatrix::identity(2).unwrap();
    matrix.apply_gate_left(&Gate::x(0), &[0, 1]);
    // |00> -> |10>: column 0 maps to row 2.
    assert_eq!(matrix.get(2, 0), Complex64::ONE);
    assert_eq!(matrix.get(0, 0), Complex64::ZERO);
}

#[test]
fn cnot_matrix_matches_truth_table() {
    let mut matrix = UnitaryMatrix::identity(2).unwrap();
    matrix.apply_gate_left(
        &Gate::cnot {
            control: 0,
            target: 1,
        },
        &[0, 1],
    );
    for (input, output) in [(0, 0), (1, 1), (2, 3), (3, 2)] {
        assert_eq!(matrix.get(output, input), Complex64::ONE);
    }
}

#[test]
fn cz_matrix_is_symmetric_in_its_qubits() {
    let mut forward = UnitaryMatrix::identity(2).unwrap();
    forward.apply_gate_left(
        &Gate::cz {
            control: 0,
            target: 1,
        },
        &[0, 1],
    );
    let mut reversed = UnitaryMatrix::identity(2).unwrap();
    reversed.apply_gate_left(
        &Gate::cz {
            control: 1,
            target: 0,
        },
        &[0, 1],
    );
    assert_eq!(forward, reversed);
    assert_eq!(forward.get(3, 3), Complex64::new(-1.0, 0.0));
    assert_eq!(forward.get(0, 0), Complex64::ONE);
}

#[test]
fn ccx_matrix_swaps_the_last_two_basis_states() {
    let mut matrix = UnitaryMatrix::identity(3).unwrap();
    matrix.apply_gate_left(
        &Gate::ccx {
            control1: 0,
            control2: 1,
            target: 2,
        },
        &[0, 1, 2],
    );
    assert_eq!(matrix.get(7, 6), Complex64::ONE);
    assert_eq!(matrix.get(6, 7), Complex64::ONE);
    for basis in 0..6 {
        assert_eq!(matrix.get(basis, basis), Complex64::ONE);
    }
}

#[test]
fn oversized_matrix_request_errors_instead_of_allocating() {
    for num_qubits in [40, 64, 200] {
        assert_eq!(
            UnitaryMatrix::identity(num_qubits).unwrap_err(),
            SuperOptError::MatrixTooLarge { num_qubits }
        );
    }
}

#[test]
fn global_phase_equivalence_accepts_phase_and_rejects_difference() {
    let s = single_qubit_matrix(&[Gate::s(0)]);
    let sdg = single_qubit_matrix(&[Gate::sdg(0)]);
    let rz_half_pi = single_qubit_matrix(&[Gate::rz(std::f64::consts::FRAC_PI_2, 0)]);
    assert!(s.equivalent_up_to_global_phase(&rz_half_pi, IDENTITY_TOLERANCE));
    assert!(!s.equivalent_up_to_global_phase(&sdg, IDENTITY_TOLERANCE));
}

#[test]
fn fingerprint_ignores_global_phase() {
    let x = single_qubit_matrix(&[Gate::x(0)]);
    // Z X Z = -X: same unitary up to a global phase of -1.
    let minus_x = single_qubit_matrix(&[Gate::z(0), Gate::x(0), Gate::z(0)]);
    assert_eq!(unitary_fingerprint(&x), unitary_fingerprint(&minus_x));
}

#[test]
fn fingerprint_distinguishes_s_from_sdg() {
    let s = single_qubit_matrix(&[Gate::s(0)]);
    let sdg = single_qubit_matrix(&[Gate::sdg(0)]);
    assert_ne!(unitary_fingerprint(&s), unitary_fingerprint(&sdg));
}

#[test]
fn fingerprint_buckets_rz_half_pi_with_s() {
    let s = single_qubit_matrix(&[Gate::s(0)]);
    let rz = single_qubit_matrix(&[Gate::rz(std::f64::consts::FRAC_PI_2, 0)]);
    assert_eq!(unitary_fingerprint(&s), unitary_fingerprint(&rz));
}

#[test]
fn library_gate_inverse_pairs() {
    assert!(LibraryGate::S(0).is_inverse_of(LibraryGate::Sdg(0)));
    assert!(LibraryGate::Tdg(1).is_inverse_of(LibraryGate::T(1)));
    assert!(LibraryGate::X(0).is_inverse_of(LibraryGate::X(0)));
    assert!(LibraryGate::Cnot(0, 1).is_inverse_of(LibraryGate::Cnot(0, 1)));
    assert!(LibraryGate::Ccx(0, 1, 2).is_inverse_of(LibraryGate::Ccx(0, 1, 2)));
    assert!(!LibraryGate::S(0).is_inverse_of(LibraryGate::S(0)));
    assert!(!LibraryGate::T(0).is_inverse_of(LibraryGate::Tdg(1)));
    assert!(!LibraryGate::X(0).is_inverse_of(LibraryGate::X(1)));
    assert!(!LibraryGate::Cnot(0, 1).is_inverse_of(LibraryGate::Cnot(1, 0)));
}

#[test]
fn library_gate_disjointness() {
    assert!(LibraryGate::X(0).is_disjoint(LibraryGate::H(1)));
    assert!(!LibraryGate::Cnot(0, 1).is_disjoint(LibraryGate::Cz(1, 2)));
    assert!(LibraryGate::Cnot(0, 1).is_disjoint(LibraryGate::Ccx(2, 3, 4)));
    assert!(!LibraryGate::Ccx(0, 1, 2).is_disjoint(LibraryGate::T(2)));
}

#[test]
fn library_gate_counts_per_width() {
    // 7n singles + n(n-1) cnot + C(n,2) cz. Toffoli is intentionally excluded.
    assert_eq!(library_gates(1).len(), 7);
    assert_eq!(library_gates(2).len(), 17);
    assert_eq!(library_gates(3).len(), 30);
    assert_eq!(library_gates(4).len(), 46);
}

#[test]
fn library_never_enumerates_toffoli() {
    for num_qubits in 1..=4 {
        for gate in library_gates(num_qubits) {
            assert!(
                !matches!(gate.to_gate(), Gate::ccx { .. }),
                "library must not contain Toffoli: {gate:?}"
            );
        }
    }
}

#[test]
fn table_does_not_synthesize_a_toffoli_representative() {
    // A Toffoli's unitary has no Clifford+T representative within the small gate
    // bound and Toffoli itself is not in the library, so it must not be found.
    let table = synthesis_table(3, 5);
    let mut toffoli = UnitaryMatrix::identity(3).unwrap();
    toffoli.apply_gate_left(
        &Gate::ccx {
            control1: 0,
            control2: 1,
            target: 2,
        },
        &[0, 1, 2],
    );
    assert!(table.synthesize(&toffoli).is_none());
}

#[test]
fn one_qubit_depth_one_table_has_eight_distinct_entries() {
    let table = synthesis_table(1, 1);
    // Identity plus X, H, S, Sdg, Z, T, Tdg — all distinct up to phase.
    assert_eq!(table.entry_count(1), 8);
    assert_eq!(table.completed_depth(1), 1);
    assert!(!table.is_saturated(1));
}

#[test]
fn synthesize_returns_empty_circuit_for_identity() {
    let table = synthesis_table(1, 1);
    let identity = UnitaryMatrix::identity(1).unwrap();
    assert!(table.synthesize(&identity).unwrap().is_empty());
}

#[test]
fn synthesize_returns_none_for_unknown_width_or_depth() {
    let table = synthesis_table(1, 1);
    let three_qubit_identity = UnitaryMatrix::identity(3).unwrap();
    assert!(table.synthesize(&three_qubit_identity).is_none());
    // H then T is not reachable within one gate.
    let deep = single_qubit_matrix(&[Gate::h(0), Gate::t(0)]);
    assert!(table.synthesize(&deep).is_none());
}

#[test]
fn hzh_synthesizes_to_x() {
    let table = synthesis_table(1, 1);
    let hzh = single_qubit_matrix(&[Gate::h(0), Gate::z(0), Gate::h(0)]);
    let replacement = table.synthesize(&hzh).unwrap();
    assert_eq!(replacement.len(), 1);
    assert!(matches!(replacement[0], Gate::x(0)));
}

#[test]
fn h_cnot_h_synthesizes_to_cz() {
    let table = synthesis_table(2, 1);
    let mut matrix = UnitaryMatrix::identity(2).unwrap();
    for gate in [
        Gate::h(1),
        Gate::cnot {
            control: 0,
            target: 1,
        },
        Gate::h(1),
    ] {
        matrix.apply_gate_left(&gate, &[0, 1]);
    }
    let replacement = table.synthesize(&matrix).unwrap();
    assert_eq!(replacement.len(), 1);
    assert!(matches!(replacement[0], Gate::cz { .. }));
}

#[test]
fn random_short_library_circuits_never_synthesize_longer() {
    let table = synthesis_table(2, 4);
    assert!(!table.is_saturated(2));
    let gates = library_gates(2);
    let mut rng = TestRng(0x7ab1_e000_c0ff_ee00);
    for _ in 0..200 {
        let length = 1 + rng.next(4);
        let circuit: Vec<_> = (0..length).map(|_| gates[rng.next(gates.len())]).collect();
        let matrix = library_circuit_matrix(2, &circuit).unwrap();
        let replacement = table
            .synthesize(&matrix)
            .expect("depth-4 two-qubit table is complete");
        assert!(replacement.len() <= length);
    }
}

#[test]
fn empty_circuit_produces_empty_result() {
    let result = SuperOpt::analyzer(2, 4).run(&Circuit::new(2)).unwrap();
    assert!(result.subcircuits.is_empty());
    assert!(result.rewrites.is_empty());
    assert!(result.circuit.gates.is_empty());
    assert_eq!(result.cache_hits + result.cache_misses, 0);
}

#[test]
fn gate_wider_than_max_qubits_is_left_alone() {
    let mut circuit = Circuit::new(3);
    circuit.apply(Gate::ccx {
        control1: 0,
        control2: 1,
        target: 2,
    });
    let result = SuperOpt::analyzer(2, 4).run(&circuit).unwrap();
    assert!(result.subcircuits.is_empty());
    assert_eq!(result.circuit.gates.len(), 1);
}

#[test]
fn rz_inverse_pair_is_removed_as_identity() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::rz(0.37, 0));
    circuit.apply(Gate::rz(-0.37, 0));
    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert_eq!(result.removed_subcircuits, vec![vec![0, 1]]);
    assert!(result.circuit.gates.is_empty());
}

#[test]
fn lone_arbitrary_rz_windows_skip_clifford_t_lookup() {
    let table = synthesis_table(1, 0);

    let mut lone = Circuit::new(1);
    lone.apply(Gate::rz(0.37, 0));
    lone.apply(Gate::h(0));
    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(Arc::clone(&table))
        .without_subcircuits()
        .run(&lone)
        .unwrap();
    assert!(result.rewrites.is_empty());
    assert_eq!(result.cache_hits + result.cache_misses, 0);

    // Two arbitrary rotations can cancel, so those windows must still reach
    // the table and find the identity representative.
    let mut cancelling = Circuit::new(1);
    cancelling.apply(Gate::rz(0.37, 0));
    cancelling.apply(Gate::rz(-0.37, 0));
    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(table)
        .without_subcircuits()
        .run(&cancelling)
        .unwrap();
    assert!(result.circuit.gates.is_empty());
    assert_eq!(result.cache_hits + result.cache_misses, 1);
}

#[test]
fn rz_pair_is_rewritten_to_library_gate() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::rz(std::f64::consts::FRAC_PI_4, 0));
    circuit.apply(Gate::rz(std::f64::consts::FRAC_PI_4, 0));
    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 1));
    let result = pass.run(&circuit).unwrap();
    assert_eq!(result.circuit.gates.len(), 1);
    assert!(matches!(result.circuit.gates[0], Gate::s(0)));
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn equal_length_synthesis_is_not_applied() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::h(0));
    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 2));
    let result = pass.run(&circuit).unwrap();
    assert!(result.rewrites.is_empty());
    assert_eq!(result.circuit.gates.len(), 2);
}

#[test]
fn identity_removal_wins_over_synthesis() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::h(0));
    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 2));
    let result = pass.run(&circuit).unwrap();
    assert!(result.circuit.gates.is_empty());
    assert_eq!(result.removed_subcircuits, vec![vec![0, 1]]);
    assert!(result.rewrites.iter().any(|r| r.replacement.is_empty()));
}

#[test]
fn consecutive_synth_rewrites_do_not_double_claim() {
    let mut circuit = Circuit::new(1);
    for _ in 0..4 {
        circuit.apply(Gate::s(0));
    }
    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 1));
    let result = pass.run(&circuit).unwrap();
    assert_eq!(result.rewrites.len(), 2);
    assert_eq!(result.circuit.gates.len(), 2);
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn rejects_reset_gate() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::reset(0));
    let error = SuperOpt::analyzer(1, 1).run(&circuit).unwrap_err();
    assert_eq!(error, SuperOptError::NonUnitaryGate { gate_index: 0 });
}

#[test]
fn rejects_out_of_range_qubit() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });
    let error = SuperOpt::analyzer(2, 1).run(&circuit).unwrap_err();
    assert_eq!(
        error,
        SuperOptError::InvalidQubit {
            gate_index: 0,
            qubit: 1,
            num_qubits: 1,
        }
    );
}

#[test]
#[should_panic(expected = "valid unitary circuit")]
fn pass_trait_panics_on_non_unitary_circuit() {
    let mut circuit = Circuit::with_cbits(1, 1);
    circuit.apply(Gate::measure { qubit: 0, cbit: 0 });
    let pass = SuperOpt::analyzer(1, 1);
    Pass::run(&pass, &circuit);
}

#[test]
fn error_messages_name_the_offending_values() {
    let messages = [
        SuperOptError::NonUnitaryGate { gate_index: 7 }.to_string(),
        SuperOptError::InvalidQubit {
            gate_index: 3,
            qubit: 9,
            num_qubits: 4,
        }
        .to_string(),
        SuperOptError::MatrixTooLarge { num_qubits: 40 }.to_string(),
    ];
    assert!(messages[0].contains('7'));
    assert!(messages[1].contains('9') && messages[1].contains('4'));
    assert!(messages[2].contains("40"));
}

#[test]
fn constructor_rejects_invalid_table_config() {
    let error = SuperOpt::new(4, 8, SuperOptTableConfig::new(0, 8, 1_000)).unwrap_err();
    assert!(matches!(error, SuperOptError::InvalidTableConfig { .. }));

    let error = SuperOpt::new(4, 8, SuperOptTableConfig::new(4, 8, 0)).unwrap_err();
    assert!(matches!(error, SuperOptError::InvalidTableConfig { .. }));
}

#[test]
fn cache_stats_count_every_emission() {
    let mut rng = TestRng(0xc047_7000_0000_0001);
    let mut circuit = Circuit::new(4);
    for _ in 0..40 {
        let q = rng.next(4);
        let q2 = (q + 1 + rng.next(3)) % 4;
        circuit.apply(match rng.next(3) {
            0 => Gate::h(q),
            1 => Gate::t(q),
            _ => Gate::cnot {
                control: q,
                target: q2,
            },
        });
    }
    let result = SuperOpt::analyzer(3, 5).run(&circuit).unwrap();
    assert_eq!(
        result.cache_hits + result.cache_misses,
        result.subcircuits.len()
    );
}

#[test]
fn result_lists_are_sorted() {
    let mut circuit = Circuit::new(2);
    for _ in 0..3 {
        circuit.apply(Gate::h(0));
        circuit.apply(Gate::x(1));
        circuit.apply(Gate::h(0));
        circuit.apply(Gate::x(1));
    }
    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    assert!(
        result
            .subcircuits
            .windows(2)
            .all(|pair| pair[0].gate_indices <= pair[1].gate_indices)
    );
    assert!(
        result
            .removed_subcircuits
            .windows(2)
            .all(|pair| pair[0] <= pair[1])
    );
}

#[test]
fn without_subcircuits_matches_collected_run() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::s(1));
    circuit.apply(Gate::s(1));

    let table = synthesis_table(2, 2);
    let collected = SuperOpt::analyzer(2, 4)
        .with_synthesis_table(Arc::clone(&table))
        .run(&circuit)
        .unwrap();
    let skipped = SuperOpt::analyzer(2, 4)
        .with_synthesis_table(table)
        .without_subcircuits()
        .run(&circuit)
        .unwrap();

    assert!(skipped.subcircuits.is_empty());
    assert!(!collected.subcircuits.is_empty());
    // The optimization result must be identical regardless of collection.
    assert_eq!(
        format!("{:?}", collected.circuit.gates),
        format!("{:?}", skipped.circuit.gates)
    );
    assert_eq!(collected.removed_subcircuits, skipped.removed_subcircuits);
    assert_eq!(collected.rewrites.len(), skipped.rewrites.len());
    // Cache statistics may differ: without subcircuit collection the pass skips
    // the provably-unshortenable single-gate windows, so it performs strictly
    // fewer lookups here (h, cnot, h, s, s each anchor a skipped single-gate
    // window) while reaching the same rewrites.
    let collected_lookups = collected.cache_hits + collected.cache_misses;
    let skipped_lookups = skipped.cache_hits + skipped.cache_misses;
    assert!(skipped_lookups < collected_lookups);
}

#[test]
fn window_bound_counts_gates_not_index_span() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(1));
    circuit.apply(Gate::x(1));
    circuit.apply(Gate::h(0));
    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert!(result.removed_subcircuits.contains(&vec![0, 3]));
    assert!(result.removed_subcircuits.contains(&vec![1, 2]));
    assert!(result.circuit.gates.is_empty());
}

#[test]
fn library_enumeration_excludes_rotation_gates() {
    for num_qubits in 1..=4 {
        for gate in library_gates(num_qubits) {
            assert!(
                !matches!(gate.to_gate(), Gate::rz(..)),
                "enumeration must stay discrete: {gate:?}"
            );
        }
    }
}

#[test]
fn synthesis_table_keeps_a_smallest_circuit() {
    let table = synthesis_table(1, 2);
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::s(0));
    circuit.apply(Gate::s(0));
    let matrix = naive_matrix(&circuit, &[0, 1], &[0]);

    let replacement = table.synthesize(&matrix).unwrap();
    assert_eq!(replacement.len(), 1);
    assert!(matches!(replacement[0], Gate::z(0)));
    assert!(!table.is_saturated(1));
}

#[test]
fn replaces_subcircuit_with_shorter_synthesized_circuit() {
    let mut circuit = Circuit::new(3);
    circuit.apply(Gate::h(2));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::x(2));
    circuit.apply(Gate::h(2));

    let pass = SuperOpt::analyzer(1, 3).with_synthesis_table(synthesis_table(1, 1));
    let result = pass.run(&circuit).unwrap();

    assert_eq!(result.rewrites.len(), 1);
    assert_eq!(result.rewrites[0].gate_indices, vec![0, 2, 3]);
    assert_eq!(result.rewrites[0].replacement.len(), 1);
    assert!(matches!(result.rewrites[0].replacement[0], Gate::z(2)));
    assert_eq!(result.circuit.gates.len(), 2);
    assert!(matches!(result.circuit.gates[0], Gate::z(2)));
    assert!(matches!(result.circuit.gates[1], Gate::x(0)));
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn synthesized_two_qubit_replacement_uses_physical_qubits() {
    let mut circuit = Circuit::new(4);
    circuit.apply(Gate::h(3));
    circuit.apply(Gate::cnot {
        control: 1,
        target: 3,
    });
    circuit.apply(Gate::h(3));

    let pass = SuperOpt::analyzer(2, 3).with_synthesis_table(synthesis_table(2, 1));
    let result = pass.run(&circuit).unwrap();

    assert_eq!(result.circuit.gates.len(), 1);
    assert!(matches!(
        result.circuit.gates[0],
        Gate::cz {
            control: 1,
            target: 3
        }
    ));
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn overlapping_synthesized_rewrites_are_not_both_applied() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::s(0));
    circuit.apply(Gate::s(0));
    circuit.apply(Gate::s(0));

    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 1));
    let result = pass.run(&circuit).unwrap();

    assert_eq!(result.rewrites.len(), 1);
    assert_eq!(result.rewrites[0].gate_indices, vec![0, 1]);
    assert!(matches!(result.rewrites[0].replacement[0], Gate::z(0)));
    assert_eq!(result.circuit.gates.len(), 2);
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn synthesis_table_reports_entry_cap() {
    let table = UnitaryCircuitTable::build(SuperOptTableConfig {
        max_qubits: 4,
        max_gates: 6,
        max_entries_per_qubit: 100,
    })
    .unwrap();
    assert_eq!(table.entry_count(4), 100);
    assert!(table.is_saturated(4));
}

#[test]
fn synthesis_table_serialization_round_trips_deterministically() {
    let table = synthesis_table(2, 3);
    let directory = tempfile::tempdir().unwrap();
    let first = directory.path().join("first.bin");
    let second = directory.path().join("second.bin");
    table.save(&first).unwrap();
    table.save(&second).unwrap();
    assert_eq!(
        std::fs::read(&first).unwrap(),
        std::fs::read(&second).unwrap()
    );

    let loaded = UnitaryCircuitTable::load(&first).unwrap();
    assert_eq!(loaded.max_gates(), table.max_gates());
    for num_qubits in 1..=2 {
        assert_eq!(
            loaded.entry_count(num_qubits),
            table.entry_count(num_qubits)
        );
        assert_eq!(
            loaded.completed_depth(num_qubits),
            table.completed_depth(num_qubits)
        );
        assert_eq!(
            loaded.is_saturated(num_qubits),
            table.is_saturated(num_qubits)
        );
    }

    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(1));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });
    circuit.apply(Gate::h(1));
    let matrix = naive_matrix(&circuit, &[0, 1, 2], &[0, 1]);
    let replacement = loaded.synthesize(&matrix).unwrap();
    assert_eq!(replacement.len(), 1);
    assert!(matches!(replacement[0], Gate::cz { .. }));
}

#[test]
fn synthesis_table_load_rejects_invalid_file() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("invalid.bin");
    std::fs::write(&path, b"not a synthesis table").unwrap();
    let error = UnitaryCircuitTable::load(path).unwrap_err();
    assert!(matches!(
        error,
        SuperOptError::InvalidTableFile { .. } | SuperOptError::TableIo { .. }
    ));
}

#[test]
fn randomized_synthesized_rewrites_preserve_unitary() {
    let table = synthesis_table(3, 2);
    let mut rng = TestRng(0x51a7_4e51_5eed_cafe);
    for _ in 0..25 {
        let mut circuit = Circuit::new(3);
        for _ in 0..30 {
            let q = rng.next(3);
            let other = (q + 1 + rng.next(2)) % 3;
            let gate = match rng.next(8) {
                0 => Gate::h(q),
                1 => Gate::x(q),
                2 => Gate::s(q),
                3 => Gate::t(q),
                4 => Gate::tdg(q),
                5 | 6 => Gate::cnot {
                    control: q,
                    target: other,
                },
                _ => Gate::cz {
                    control: q,
                    target: other,
                },
            };
            circuit.apply(gate);
        }

        let pass = SuperOpt::analyzer(3, 4).with_synthesis_table(Arc::clone(&table));
        let optimized = pass.run(&circuit).unwrap().circuit;
        assert!(crate::unitary::circuits_equiv(
            &circuit,
            &optimized,
            IDENTITY_TOLERANCE,
        ));
        assert!(optimized.gates.len() <= circuit.gates.len());
    }
}

/// Independently verify every rewrite the pass selected on `circuit`:
/// disjoint claims, commutation of skipped gates past the window span,
/// support-confined replacements, and matrix equality up to global phase.
/// Local soundness of each rewrite implies whole-circuit equivalence.
fn audit_rewrites(circuit: &Circuit, result: &SuperOptResult) {
    let mut claimed = vec![false; circuit.gates.len()];
    for rewrite in &result.rewrites {
        let mut support = Vec::new();
        for &gate_index in &rewrite.gate_indices {
            assert!(!claimed[gate_index], "gate {gate_index} claimed twice");
            claimed[gate_index] = true;
            support = union_qubits(&support, &unique_qubits(&circuit.gates[gate_index]));
        }

        let first = rewrite.gate_indices[0];
        let last = *rewrite.gate_indices.last().unwrap();
        for skipped in first..=last {
            if rewrite.gate_indices.binary_search(&skipped).is_ok() {
                continue;
            }
            for qubit in unique_qubits(&circuit.gates[skipped]) {
                assert!(
                    support.binary_search(&qubit).is_err(),
                    "skipped gate {skipped} touches window qubit {qubit}"
                );
            }
        }

        assert!(
            rewrite.replacement.len() < rewrite.gate_indices.len(),
            "rewrite must strictly shrink the circuit"
        );
        let mut replacement_matrix = UnitaryMatrix::identity(support.len()).unwrap();
        for gate in &rewrite.replacement {
            assert!(
                !matches!(gate, Gate::ccx { .. }),
                "rewrite introduced a Toffoli: {:?}",
                rewrite.gate_indices
            );
            for qubit in unique_qubits(gate) {
                assert!(
                    support.binary_search(&qubit).is_ok(),
                    "replacement leaves the window support"
                );
            }
            replacement_matrix.apply_gate_left(gate, &support);
        }
        let original = naive_matrix(circuit, &rewrite.gate_indices, &support);
        assert!(
            original.equivalent_up_to_global_phase(&replacement_matrix, IDENTITY_TOLERANCE),
            "replacement matrix differs for gates {:?}",
            rewrite.gate_indices
        );
    }
}

#[test]
fn randomized_production_config_rewrites_are_sound() {
    let table = Arc::new(
        UnitaryCircuitTable::build(SuperOptTableConfig {
            max_qubits: 4,
            max_gates: 3,
            max_entries_per_qubit: 2_000,
        })
        .unwrap(),
    );
    let mut rng = TestRng(0xfab1_e5ca_1e50_44d5);
    for _ in 0..10 {
        let mut circuit = Circuit::new(5);
        for gate_index in 0..60 {
            let q = rng.next(5);
            let q2 = (q + 1 + rng.next(4)) % 5;
            let mut q3 = rng.next(5);
            while q3 == q || q3 == q2 {
                q3 = rng.next(5);
            }
            let gate = match rng.next(12) {
                0 => Gate::x(q),
                1 => Gate::h(q),
                2 => Gate::s(q),
                3 => Gate::sdg(q),
                4 => Gate::z(q),
                5 => Gate::t(q),
                6 => Gate::tdg(q),
                7 => Gate::rz((gate_index + 1) as f64 / 13.0, q),
                8 | 9 => Gate::cnot {
                    control: q,
                    target: q2,
                },
                10 => Gate::cz {
                    control: q,
                    target: q2,
                },
                _ => Gate::ccx {
                    control1: q,
                    control2: q2,
                    target: q3,
                },
            };
            circuit.apply(gate);
        }

        let pass = SuperOpt::analyzer(4, 8).with_synthesis_table(Arc::clone(&table));
        let result = pass.run(&circuit).unwrap();
        audit_rewrites(&circuit, &result);
        assert!(result.circuit.gates.len() <= circuit.gates.len());
        assert!(crate::unitary::circuits_equiv(
            &circuit,
            &result.circuit,
            IDENTITY_TOLERANCE,
        ));
    }
}

#[test]
fn removes_noncontiguous_identity_subcircuit_from_circuit() {
    let mut circuit = Circuit::new(2);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(1));
    circuit.apply(Gate::h(0));

    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert_eq!(result.removed_subcircuits, vec![vec![0, 2]]);
    assert_eq!(result.circuit.gates.len(), 1);
    assert!(matches!(result.circuit.gates[0], Gate::x(1)));
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn checks_identity_windows_shorter_than_gate_limit() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::h(0));

    let result = SuperOpt::analyzer(1, 8)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert_eq!(result.removed_subcircuits, vec![vec![0, 1]]);
    assert!(result.circuit.gates.is_empty());
    assert!(
        result
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0])
    );
    assert!(
        result
            .subcircuits
            .iter()
            .any(|window| window.gate_indices == [0, 1])
    );
}

#[test]
fn removes_identity_up_to_global_phase() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::z(0));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::z(0));

    let result = SuperOpt::analyzer(1, 4)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert_eq!(result.removed_subcircuits, vec![vec![0, 1, 2, 3]]);
    assert!(result.circuit.gates.is_empty());
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn overlapping_identity_windows_are_not_both_removed() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::x(0));

    let result = SuperOpt::analyzer(1, 2)
        .with_synthesis_table(synthesis_table(1, 0))
        .run(&circuit)
        .unwrap();
    assert_eq!(result.removed_subcircuits, vec![vec![0, 1]]);
    assert_eq!(result.circuit.gates.len(), 1);
    assert!(matches!(result.circuit.gates[0], Gate::x(0)));
    assert!(crate::unitary::circuits_equiv(
        &circuit,
        &result.circuit,
        IDENTITY_TOLERANCE,
    ));
}

#[test]
fn nonidentity_window_is_preserved() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(0));

    let result = SuperOpt::analyzer(1, 2).run(&circuit).unwrap();
    assert!(result.removed_subcircuits.is_empty());
    assert_eq!(result.circuit.gates.len(), 2);
}

#[test]
fn implements_optimization_pass_interface() {
    let mut circuit = Circuit::new(1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::h(0));

    let pass = SuperOpt::analyzer(1, 2).with_synthesis_table(synthesis_table(1, 0));
    let optimized = Pass::run(&pass, &circuit);
    assert!(optimized.gates.is_empty());
}

#[test]
fn every_supported_unitary_gate_matches_naive_matrix() {
    let mut circuit = Circuit::new(3);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::x(0));
    circuit.apply(Gate::s(0));
    circuit.apply(Gate::sdg(0));
    circuit.apply(Gate::z(0));
    circuit.apply(Gate::t(0));
    circuit.apply(Gate::tdg(0));
    circuit.apply(Gate::rz(0.29, 0));
    circuit.apply(Gate::cnot {
        control: 0,
        target: 1,
    });
    circuit.apply(Gate::cz {
        control: 1,
        target: 0,
    });
    circuit.apply(Gate::ccx {
        control1: 0,
        control2: 1,
        target: 2,
    });

    let result = SuperOpt::analyzer(3, 3).run(&circuit).unwrap();
    for window in &result.subcircuits {
        let expected = naive_matrix(&circuit, &window.gate_indices, &window.qubits);
        assert_matrix_close(&window.matrix, &expected);
    }
}

#[test]
fn randomized_results_match_naive_anchored_scan() {
    let mut rng = TestRng(0x5eed_1234_9876_abcd);
    for _ in 0..30 {
        let mut circuit = Circuit::new(4);
        for _ in 0..30 {
            let q = rng.next(4);
            let q2 = (q + 1 + rng.next(3)) % 4;
            let mut q3 = rng.next(4);
            while q3 == q || q3 == q2 {
                q3 = rng.next(4);
            }
            let gate = match rng.next(11) {
                0 => Gate::x(q),
                1 => Gate::h(q),
                2 => Gate::s(q),
                3 => Gate::sdg(q),
                4 => Gate::z(q),
                5 => Gate::t(q),
                6 => Gate::tdg(q),
                7 => Gate::rz(rng.next(100) as f64 / 17.0, q),
                8 => Gate::cnot {
                    control: q,
                    target: q2,
                },
                9 => Gate::cz {
                    control: q,
                    target: q2,
                },
                _ => Gate::ccx {
                    control1: q,
                    control2: q2,
                    target: q3,
                },
            };
            circuit.apply(gate);
        }

        for max_qubits in 1..=3 {
            for window_gates in 1..=5 {
                let result = SuperOpt::analyzer(max_qubits, window_gates)
                    .run(&circuit)
                    .unwrap();
                let expected = naive_windows(&circuit, max_qubits, window_gates);
                let actual: Vec<_> = result
                    .subcircuits
                    .iter()
                    .map(|window| (window.gate_indices.clone(), window.qubits.clone()))
                    .collect();
                assert_eq!(actual, expected);
                for window in &result.subcircuits {
                    let expected = naive_matrix(&circuit, &window.gate_indices, &window.qubits);
                    assert_matrix_close(&window.matrix, &expected);
                }
            }
        }
    }
}

#[test]
fn rejects_non_unitary_circuit() {
    let mut circuit = Circuit::with_cbits(1, 1);
    circuit.apply(Gate::h(0));
    circuit.apply(Gate::measure { qubit: 0, cbit: 0 });

    let error = SuperOpt::analyzer(1, 1).run(&circuit).unwrap_err();
    assert_eq!(error, SuperOptError::NonUnitaryGate { gate_index: 1 });
}

#[test]
fn rejects_zero_gate_window() {
    let error = SuperOpt::analyzer(2, 0).run(&Circuit::new(2)).unwrap_err();
    assert_eq!(error, SuperOptError::ZeroWindowGates);
}

fn load_optimizer_profile_table() -> Arc<UnitaryCircuitTable> {
    use std::time::Instant;

    let start = Instant::now();
    let table = shared_synthesis_table(SuperOptTableConfig::default()).unwrap();
    println!(
        "initialized optimizer synthesis table in {:.3} s: entries {:?}, complete depths {:?}",
        start.elapsed().as_secs_f64(),
        (1..=4)
            .map(|num_qubits| table.entry_count(num_qubits))
            .collect::<Vec<_>>(),
        (1..=4)
            .map(|num_qubits| table.completed_depth(num_qubits))
            .collect::<Vec<_>>(),
    );
    table
}

#[test]
#[ignore = "manual release-mode equivalence check on small benchmarks"]
fn verify_small_benchmarks_preserve_unitary() {
    let table = load_optimizer_profile_table();
    for name in ["tof_3", "barenco_tof_3", "mod5_4", "hwb6"] {
        let path = format!(
            "{}/benchmarks/feynman/{name}.qasm",
            env!("CARGO_MANIFEST_DIR")
        );
        let circuit = crate::qasm::parse(&std::fs::read_to_string(&path).unwrap()).unwrap();
        let pass = SuperOpt::analyzer(4, 8)
            .with_synthesis_table(Arc::clone(&table))
            .without_subcircuits();
        let result = pass.run(&circuit).unwrap();
        assert!(
            crate::unitary::circuits_equiv(&circuit, &result.circuit, IDENTITY_TOLERANCE),
            "{name} rewrite changed the unitary"
        );

        let default_result = Pass::run(
            &crate::phase_fold_rand::PhaseFoldRand,
            &Pass::run(&crate::cancel::CancelGates, &circuit),
        );
        let pipelined = pass.run(&default_result).unwrap();
        assert!(
            crate::unitary::circuits_equiv(&circuit, &pipelined.circuit, IDENTITY_TOLERANCE),
            "{name} default+subcircuit pipeline changed the unitary"
        );
        println!(
            "{name}: {} gates -> {} (standalone) / {} (default+subcircuit), unitary preserved",
            circuit.gates.len(),
            result.circuit.gates.len(),
            pipelined.circuit.gates.len(),
        );
    }
}

#[test]
#[ignore = "manual release-mode randomized fuzz with guaranteed rewrites"]
fn fuzz_subcircuit_rewrites_change_circuit_and_preserve_unitary() {
    let table = load_optimizer_profile_table();
    let mut rng = TestRng(0xdeed_beef_5eed_0001);
    let num_cases = 10_000;
    for round in 0..num_cases {
        let mut circuit = Circuit::new(6);

        // Guarantee that every fuzz case exercises the rewrite path. The
        // gadget varies across single-, two-, and three-qubit gates.
        match rng.next(8) {
            0 => {
                let q = rng.next(6);
                circuit.apply(Gate::h(q));
                circuit.apply(Gate::h(q));
            }
            1 => {
                let q = rng.next(6);
                circuit.apply(Gate::x(q));
                circuit.apply(Gate::x(q));
            }
            2 => {
                let q = rng.next(6);
                circuit.apply(Gate::z(q));
                circuit.apply(Gate::z(q));
            }
            3 => {
                let q = rng.next(6);
                circuit.apply(Gate::s(q));
                circuit.apply(Gate::sdg(q));
            }
            4 => {
                let q = rng.next(6);
                circuit.apply(Gate::t(q));
                circuit.apply(Gate::tdg(q));
            }
            5 => {
                circuit.apply(Gate::cnot {
                    control: 0,
                    target: 1,
                });
                circuit.apply(Gate::cnot {
                    control: 0,
                    target: 1,
                });
            }
            6 => {
                circuit.apply(Gate::cz {
                    control: 0,
                    target: 1,
                });
                circuit.apply(Gate::cz {
                    control: 1,
                    target: 0,
                });
            }
            _ => {
                circuit.apply(Gate::ccx {
                    control1: 0,
                    control2: 1,
                    target: 2,
                });
                circuit.apply(Gate::ccx {
                    control1: 0,
                    control2: 1,
                    target: 2,
                });
            }
        }

        for gate_index in 0..100 {
            let q = rng.next(6);
            let q2 = (q + 1 + rng.next(5)) % 6;
            let mut q3 = rng.next(6);
            while q3 == q || q3 == q2 {
                q3 = rng.next(6);
            }
            let gate = match rng.next(12) {
                0 => Gate::x(q),
                1 => Gate::h(q),
                2 => Gate::s(q),
                3 => Gate::sdg(q),
                4 => Gate::z(q),
                5 => Gate::t(q),
                6 => Gate::tdg(q),
                7 => Gate::rz((gate_index + 1) as f64 / 13.0, q),
                8 | 9 => Gate::cnot {
                    control: q,
                    target: q2,
                },
                10 => Gate::cz {
                    control: q,
                    target: q2,
                },
                _ => Gate::ccx {
                    control1: q,
                    control2: q2,
                    target: q3,
                },
            };
            circuit.apply(gate);
        }

        let pass = SuperOpt::analyzer(4, 8).with_synthesis_table(Arc::clone(&table));
        let result = pass.run(&circuit).unwrap();
        assert!(!result.rewrites.is_empty(), "round {round} made no rewrite");
        assert!(
            result.circuit.gates.len() < circuit.gates.len(),
            "round {round} did not change the circuit"
        );
        audit_rewrites(&circuit, &result);
        assert!(
            crate::unitary::circuits_equiv(&circuit, &result.circuit, IDENTITY_TOLERANCE),
            "round {round} changed the unitary"
        );
    }
    println!(
        "{num_cases} random 6-qubit circuits: all changed, rewrites audited, unitaries preserved"
    );
}

#[test]
#[ignore = "manual release-mode rewrite audit over the full benchmark corpora"]
fn audit_all_benchmark_rewrites() {
    use crate::cancel::CancelGates;
    use crate::phase_fold_rand::PhaseFoldRand;

    let mut paths = Vec::new();
    for corpus in ["feynman", "cobble"] {
        let directory = format!("{}/benchmarks/{corpus}", env!("CARGO_MANIFEST_DIR"));
        paths.extend(
            std::fs::read_dir(directory)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| {
                    path.extension()
                        .is_some_and(|extension| extension == "qasm")
                }),
        );
    }
    paths.sort();

    let table = load_optimizer_profile_table();
    let pass = SuperOpt::analyzer(4, 8).with_synthesis_table(Arc::clone(&table));

    let mut total_rewrites = 0;
    for path in paths {
        let name = path.file_stem().unwrap().to_string_lossy();
        let circuit = crate::qasm::parse(&std::fs::read_to_string(&path).unwrap()).unwrap();

        let standalone = pass.run(&circuit).unwrap();
        audit_rewrites(&circuit, &standalone);

        let default_result = Pass::run(&PhaseFoldRand, &Pass::run(&CancelGates, &circuit));
        let pipelined = pass.run(&default_result).unwrap();
        audit_rewrites(&default_result, &pipelined);

        total_rewrites += standalone.rewrites.len() + pipelined.rewrites.len();
        println!(
            "{name}: {} standalone + {} pipelined rewrites audited",
            standalone.rewrites.len(),
            pipelined.rewrites.len(),
        );
    }
    println!("TOTAL: {total_rewrites} rewrites audited");
}
