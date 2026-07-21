use crate::circuit::{Circuit, Gate};

/// An optimization pass: takes a circuit, returns an equivalent one.
pub trait Pass: Sync {
    fn name(&self) -> &str;
    fn run(&self, circuit: &Circuit) -> Circuit;
}

/// The outcome of [`run_passes`].
pub struct PassResult {
    pub circuit: Circuit,
    /// T-count after only the first pass, for attributing reductions to it.
    pub t_after_first: usize,
    /// Gate count after only the first pass, for attributing reductions to it.
    pub gates_after_first: usize,
}

/// Run `passes` in order, feeding each pass's output to the next.
pub fn run_passes(circuit: &Circuit, passes: &[&dyn Pass]) -> PassResult {
    let mut c = circuit.clone();
    let mut t_after_first = 0;
    let mut gates_after_first = 0;
    for (i, p) in passes.iter().enumerate() {
        c = p.run(&c);
        if i == 0 {
            t_after_first = count_t(&c);
            gates_after_first = c.gates.len();
        }
    }
    PassResult {
        circuit: c,
        t_after_first,
        gates_after_first,
    }
}

/// Number of `t`/`tdg` gates in the circuit.
pub fn count_t(c: &Circuit) -> usize {
    c.gates
        .iter()
        .filter(|g| matches!(g, Gate::t(_) | Gate::tdg(_)))
        .count()
}

/// Number of `rz` gates in the circuit.
pub fn count_rz(c: &Circuit) -> usize {
    c.gates.iter().filter(|g| matches!(g, Gate::rz(..))).count()
}
