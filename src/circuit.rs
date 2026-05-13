//! Circuit representation: gates, qubits, and display.

use std::fmt;

pub type Qubit = usize;
pub type CBit = usize;

#[allow(non_camel_case_types)]
#[derive(Clone, Debug)]
pub enum Gate {
    x(Qubit),
    h(Qubit),
    s(Qubit),
    sdg(Qubit),
    z(Qubit),
    t(Qubit),
    tdg(Qubit),
    rz(f64, Qubit),
    cnot { control: Qubit, target: Qubit },
    ccx { control1: Qubit, control2: Qubit, target: Qubit },
    measure { qubit: Qubit, cbit: CBit },
    reset(Qubit),
}

#[derive(Clone, Debug)]
pub struct Circuit {
    pub num_qubits: usize,
    pub num_cbits: usize,
    pub gates: Vec<Gate>,
    pub has_toffoli: bool,
    pub has_measurement: bool,
}

impl Circuit {
    pub fn new(num_qubits: usize) -> Self {
        Circuit {
            num_qubits,
            num_cbits: 0,
            gates: Vec::new(),
            has_toffoli: false,
            has_measurement: false,
        }
    }

    pub fn with_cbits(num_qubits: usize, num_cbits: usize) -> Self {
        Circuit {
            num_qubits,
            num_cbits,
            gates: Vec::new(),
            has_toffoli: false,
            has_measurement: false,
        }
    }

    pub fn apply(&mut self, gate: Gate) {
        match &gate {
            Gate::ccx { .. } => self.has_toffoli = true,
            Gate::measure { .. } | Gate::reset(_) => self.has_measurement = true,
            _ => {}
        }
        self.gates.push(gate);
    }

    pub fn to_qasm(&self) -> String {
        crate::qasm::serialize(self)
    }

    pub fn from_qasm(qasm: &str) -> Result<Self, String> {
        crate::qasm::parse(qasm)
    }
}

impl fmt::Display for Gate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Gate::x(q) => write!(f, "x q{q}"),
            Gate::h(q) => write!(f, "h q{q}"),
            Gate::s(q) => write!(f, "s q{q}"),
            Gate::sdg(q) => write!(f, "sdg q{q}"),
            Gate::z(q) => write!(f, "z q{q}"),
            Gate::t(q) => write!(f, "t q{q}"),
            Gate::tdg(q) => write!(f, "tdg q{q}"),
            Gate::rz(theta, q) => write!(f, "rz({theta:.4}) q{q}"),
            Gate::cnot { control, target } => write!(f, "cnot q{control}, q{target}"),
            Gate::ccx { control1, control2, target } => {
                write!(f, "ccx q{control1}, q{control2}, q{target}")
            }
            Gate::measure { qubit, cbit } => write!(f, "measure q{qubit} -> c{cbit}"),
            Gate::reset(q) => write!(f, "reset q{q}"),
        }
    }
}

impl fmt::Display for Circuit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Circuit ({} qubits, {} gates):", self.num_qubits, self.gates.len())?;
        for (i, gate) in self.gates.iter().enumerate() {
            writeln!(f, "  {i}: {gate}")?;
        }
        Ok(())
    }
}

/// Return the qubits a gate acts on.
pub fn qubits_of(gate: &Gate) -> Vec<Qubit> {
    match gate {
        Gate::x(q) | Gate::h(q) | Gate::s(q) | Gate::sdg(q) | Gate::z(q)
        | Gate::t(q) | Gate::tdg(q) | Gate::rz(_, q) | Gate::reset(q) => vec![*q],
        Gate::cnot { control, target } => vec![*control, *target],
        Gate::ccx { control1, control2, target } => vec![*control1, *control2, *target],
        Gate::measure { qubit, .. } => vec![*qubit],
    }
}

/// Remap a gate's qubits through a lookup table: qubit i becomes its index in `qubits`.
/// Classical bits are not remapped.
pub fn remap_gate(gate: &Gate, qubits: &[Qubit]) -> Gate {
    let m = |q: &Qubit| qubits.iter().position(|&x| x == *q).unwrap();
    match gate {
        Gate::x(q) => Gate::x(m(q)),
        Gate::h(q) => Gate::h(m(q)),
        Gate::s(q) => Gate::s(m(q)),
        Gate::sdg(q) => Gate::sdg(m(q)),
        Gate::z(q) => Gate::z(m(q)),
        Gate::t(q) => Gate::t(m(q)),
        Gate::tdg(q) => Gate::tdg(m(q)),
        Gate::rz(theta, q) => Gate::rz(*theta, m(q)),
        Gate::cnot { control, target } => Gate::cnot { control: m(control), target: m(target) },
        Gate::ccx { control1, control2, target } => Gate::ccx {
            control1: m(control1),
            control2: m(control2),
            target: m(target),
        },
        Gate::measure { qubit, cbit } => Gate::measure { qubit: m(qubit), cbit: *cbit },
        Gate::reset(q) => Gate::reset(m(q)),
    }
}

/// Build a compact circuit with qubits remapped to 0..n.
pub fn remap_subcircuit(gates: &[Gate], qubits: &[Qubit]) -> Circuit {
    let n = qubits.len();
    let mut c = Circuit::new(n);
    for g in gates {
        c.apply(remap_gate(g, qubits));
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::f64::consts::PI;

    #[test]
    fn bell_pair() {
        let mut c = Circuit::new(2);
        c.apply(Gate::h(0));
        c.apply(Gate::cnot { control: 0, target: 1 });
        assert_eq!(c.gates.len(), 2);
        let s = format!("{c}");
        assert!(s.contains("h q0"));
        assert!(s.contains("cnot q0, q1"));
        println!("{c}");
    }

    #[test]
    fn ghz_state() {
        let n = 4;
        let mut c = Circuit::new(n);
        c.apply(Gate::h(0));
        for i in 0..n - 1 {
            c.apply(Gate::cnot { control: i, target: i + 1 });
        }
        assert_eq!(c.gates.len(), 4);
        println!("{c}");
    }

    #[test]
    fn t_gate_decomposition_of_rz() {
        let mut c = Circuit::new(1);
        c.apply(Gate::t(0));
        c.apply(Gate::s(0));
        c.apply(Gate::rz(PI / 4.0, 0));
        let s = format!("{c}");
        assert!(s.contains("t q0"));
        assert!(s.contains("s q0"));
        assert!(s.contains("rz(0.7854) q0"));
        println!("{c}");
    }

    #[test]
    fn ccx_gate() {
        let mut c = Circuit::new(3);
        c.apply(Gate::h(2));
        c.apply(Gate::ccx { control1: 0, control2: 1, target: 2 });
        c.apply(Gate::h(2));
        assert_eq!(c.gates.len(), 3);
        let s = format!("{c}");
        assert!(s.contains("ccx q0, q1, q2"));
        println!("{c}");
    }

    #[test]
    fn qft_3qubit() {
        let mut c = Circuit::new(3);
        c.apply(Gate::h(0));
        c.apply(Gate::rz(PI / 2.0, 0));
        c.apply(Gate::cnot { control: 1, target: 0 });
        c.apply(Gate::rz(PI / 4.0, 0));
        c.apply(Gate::cnot { control: 2, target: 0 });
        c.apply(Gate::h(1));
        c.apply(Gate::rz(PI / 2.0, 1));
        c.apply(Gate::cnot { control: 2, target: 1 });
        c.apply(Gate::h(2));
        assert_eq!(c.num_qubits, 3);
        assert_eq!(c.gates.len(), 9);
        println!("{c}");
    }

    #[test]
    fn z_gate_display() {
        let mut c = Circuit::new(1);
        c.apply(Gate::z(0));
        let s = format!("{c}");
        assert!(s.contains("z q0"));
    }

    #[test]
    fn sdg_gate_display() {
        let mut c = Circuit::new(1);
        c.apply(Gate::sdg(0));
        let s = format!("{c}");
        assert!(s.contains("sdg q0"));
    }

    #[test]
    fn measure_gate_display() {
        let mut c = Circuit::with_cbits(1, 1);
        c.apply(Gate::measure { qubit: 0, cbit: 0 });
        let s = format!("{c}");
        assert!(s.contains("measure q0 -> c0"));
        assert!(c.has_measurement);
    }

    #[test]
    fn reset_gate_display() {
        let mut c = Circuit::new(1);
        c.apply(Gate::reset(0));
        let s = format!("{c}");
        assert!(s.contains("reset q0"));
        assert!(c.has_measurement);
    }

    #[test]
    fn measure_qubits_of() {
        let g = Gate::measure { qubit: 3, cbit: 7 };
        assert_eq!(qubits_of(&g), vec![3]);
    }

    #[test]
    fn reset_qubits_of() {
        let g = Gate::reset(2);
        assert_eq!(qubits_of(&g), vec![2]);
    }

    #[test]
    fn measure_remap() {
        let g = Gate::measure { qubit: 5, cbit: 2 };
        let remapped = remap_gate(&g, &[5]);
        match remapped {
            Gate::measure { qubit: 0, cbit: 2 } => {}
            _ => panic!("expected measure q0 -> c2, got {remapped:?}"),
        }
    }

    #[test]
    fn reset_remap() {
        let g = Gate::reset(5);
        let remapped = remap_gate(&g, &[5]);
        assert!(matches!(remapped, Gate::reset(0)));
    }

    #[test]
    fn with_cbits_default_fields() {
        let c = Circuit::with_cbits(2, 3);
        assert_eq!(c.num_qubits, 2);
        assert_eq!(c.num_cbits, 3);
        assert!(!c.has_measurement);
        assert!(!c.has_toffoli);
        assert_eq!(c.gates.len(), 0);
    }

    #[test]
    fn has_measurement_flag_set_by_reset_alone() {
        // reset has no cbits but still counts as measurement
        let mut c = Circuit::new(1);
        assert!(!c.has_measurement);
        c.apply(Gate::reset(0));
        assert!(c.has_measurement);
    }
}
