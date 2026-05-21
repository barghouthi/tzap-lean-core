"""
Modular exponentiation circuit using Qiskit.

Constructs the unitary |x⟩|1⟩ → |x⟩|a^x mod N⟩ used in Shor's algorithm.
Built from controlled modular multiplications, each of which is built from
controlled modular additions via the Beauregard / Draper approach.
"""

from qiskit import QuantumCircuit, QuantumRegister
from qiskit.circuit.library import QFT
import numpy as np


def controlled_modular_addition(n_bits: int, a: int, N: int) -> QuantumCircuit:
    """
    Controlled addition of classical constant `a` modulo `N` in the QFT basis.
    Uses the Draper adder approach: addition is phase rotations in QFT space.

    Registers: ctrl(1), b(n_bits+1) already in QFT basis, ancilla(1).
    Computes |ctrl⟩|b⟩ → |ctrl⟩|b + a mod N⟩ when ctrl=1.
    """
    n = n_bits + 1  # extra qubit for overflow detection

    ctrl = QuantumRegister(1, "ctrl")
    b = QuantumRegister(n, "b")
    anc = QuantumRegister(1, "anc")
    qc = QuantumCircuit(ctrl, b, anc, name=f"CModAdd({a},{N})")

    def phi_add(circuit, target, value, n_qubits, control=None):
        """Add classical `value` to `target` register (QFT basis) via phase rotations."""
        for i in range(n_qubits):
            angle = 0
            for j in range(i, n_qubits):
                if (value >> (n_qubits - 1 - j)) & 1:
                    angle += np.pi / (1 << (j - i))
            if angle != 0:
                if control is not None:
                    circuit.cp(angle, control, target[i])
                else:
                    circuit.p(angle, target[i])

    def phi_sub(circuit, target, value, n_qubits, control=None):
        """Subtract classical `value` from `target` register (QFT basis)."""
        phi_add(circuit, target, value, n_qubits, control)
        # Invert by negating all angles
        for i in range(n_qubits):
            angle = 0
            for j in range(i, n_qubits):
                if (value >> (n_qubits - 1 - j)) & 1:
                    angle += np.pi / (1 << (j - i))
            if angle != 0:
                total = -2 * angle  # negate the original and subtract what was added
                if control is not None:
                    circuit.cp(total, control, target[i])
                else:
                    circuit.p(total, target[i])

    # Controlled add a
    phi_add(qc, b, a, n, control=ctrl[0])
    # Subtract N (unconditional)
    phi_add(qc, b, (1 << n) - N, n)  # equivalent to subtracting N mod 2^n
    # Check MSB (overflow) → ancilla
    qc.append(QFT(n, inverse=True).to_gate(), b[:])
    qc.cx(b[0], anc[0])
    qc.append(QFT(n).to_gate(), b[:])
    # If overflow (ancilla=1), add N back
    phi_add(qc, b, N, n, control=anc[0])
    # Uncompute ancilla
    phi_add(qc, b, (1 << n) - a, n, control=ctrl[0])  # subtract a
    qc.append(QFT(n, inverse=True).to_gate(), b[:])
    qc.cx(b[0], anc[0])
    qc.append(QFT(n).to_gate(), b[:])
    # Re-add a (controlled)
    phi_add(qc, b, a, n, control=ctrl[0])

    return qc


def controlled_modular_multiply(n_bits: int, a: int, N: int) -> QuantumCircuit:
    """
    Controlled multiplication by classical `a` modulo `N`.
    |ctrl⟩|x⟩|0⟩ → |ctrl⟩|x⟩|a*x mod N⟩  (when ctrl=1),
    then swap x↔result and uncompute to get |ctrl⟩|a*x mod N⟩|0⟩.
    """
    n = n_bits + 1

    ctrl = QuantumRegister(1, "ctrl")
    x = QuantumRegister(n_bits, "x")
    b = QuantumRegister(n, "b")
    anc = QuantumRegister(1, "anc")
    qc = QuantumCircuit(ctrl, x, b, anc, name=f"CModMul({a},{N})")

    # QFT on b
    qc.append(QFT(n).to_gate(), b[:])

    # Controlled modular additions: b += a * 2^i * x_i mod N
    for i in range(n_bits):
        val = (a * (1 << i)) % N
        add_gate = controlled_modular_addition(n_bits, val, N).to_gate()
        # Use x[i] as extra control by composing with ctrl
        # Simplified: use a two-control approach
        qc.append(add_gate.control(1), [x[i]] + [ctrl[0]] + list(b[:]) + [anc[0]])

    # Inverse QFT on b
    qc.append(QFT(n, inverse=True).to_gate(), b[:])

    # Controlled swap x ↔ b[1:n_bits+1]
    for i in range(n_bits):
        qc.cswap(ctrl[0], x[i], b[i + 1])

    # Inverse multiplication by a^{-1} to uncompute b
    a_inv = pow(a, -1, N)
    qc.append(QFT(n).to_gate(), b[:])
    for i in range(n_bits - 1, -1, -1):
        val = (a_inv * (1 << i)) % N
        add_gate = controlled_modular_addition(n_bits, val, N).to_gate()
        inv_gate = add_gate.inverse()
        qc.append(inv_gate.control(1), [x[i]] + [ctrl[0]] + list(b[:]) + [anc[0]])
    qc.append(QFT(n, inverse=True).to_gate(), b[:])

    return qc


def modular_exponentiation(a: int, N: int, n_count: int = None) -> QuantumCircuit:
    """
    Build the full modular exponentiation circuit:
        |x⟩|1⟩ → |x⟩|a^x mod N⟩

    Parameters
    ----------
    a : base of exponentiation, must be coprime to N
    N : modulus
    n_count : number of counting qubits (controls precision);
              defaults to 2 * ceil(log2(N))

    Returns the full quantum circuit.
    """
    assert 1 < a < N, "Need 1 < a < N"
    from math import gcd, ceil, log2
    assert gcd(a, N) == 1, "a must be coprime to N"

    n_bits = int(ceil(log2(N + 1)))
    if n_count is None:
        n_count = 2 * n_bits

    # Registers
    counting = QuantumRegister(n_count, "count")
    target = QuantumRegister(n_bits, "target")
    work = QuantumRegister(n_bits + 1, "work")  # overflow + workspace
    ancilla = QuantumRegister(1, "anc")
    qc = QuantumCircuit(counting, target, work, ancilla,
                        name=f"ModExp({a}^x mod {N})")

    # Initialize target to |1⟩
    qc.x(target[0])

    # Apply Hadamard to counting register
    qc.h(counting[:])

    # Controlled modular multiplications: multiply by a^(2^i) for each counting qubit i
    for i in range(n_count):
        exponent = pow(a, 1 << i, N)
        cmul = controlled_modular_multiply(n_bits, exponent, N)
        qc.append(
            cmul.to_gate(),
            [counting[i]] + list(target[:]) + list(work[:]) + [ancilla[0]]
        )

    # Inverse QFT on counting register to extract phase
    qc.append(QFT(n_count, inverse=True).to_gate(), counting[:])

    return qc


# --- Simple / pedagogical version using permutation matrices ---

def mod_exp_simple(a: int, N: int, n_count: int = None) -> QuantumCircuit:
    """
    Simplified modular exponentiation using Qiskit's unitary synthesis.
    Directly encodes the permutation |y⟩ → |a*y mod N⟩ as a unitary.

    Good for small N (say N ≤ 16) where the 2^n × 2^n matrix fits in memory.
    """
    from math import ceil, log2, gcd
    assert gcd(a, N) == 1

    n_bits = int(ceil(log2(N + 1)))
    if n_count is None:
        n_count = 2 * n_bits
    dim = 1 << n_bits

    counting = QuantumRegister(n_count, "count")
    target = QuantumRegister(n_bits, "target")
    qc = QuantumCircuit(counting, target, name=f"ModExp_simple({a}^x mod {N})")

    # |target⟩ = |1⟩
    qc.x(target[0])
    qc.h(counting[:])

    for i in range(n_count):
        exp = pow(a, 1 << i, N)
        # Build permutation matrix for |y⟩ → |exp*y mod N⟩
        U = np.zeros((dim, dim))
        for y in range(dim):
            if y < N:
                U[(exp * y) % N, y] = 1
            else:
                U[y, y] = 1  # identity for states ≥ N
        gate = QuantumCircuit(n_bits, name=f"Mul({exp})")
        gate.unitary(U, range(n_bits))
        c_gate = gate.to_gate().control(1)
        qc.append(c_gate, [counting[i]] + list(target[:]))

    qc.append(QFT(n_count, inverse=True).to_gate(), counting[:])
    return qc


def export_qasm(qc: QuantumCircuit, filename: str):
    """Decompose to basis gates and export as OpenQASM 2.0."""
    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    pm = generate_preset_pass_manager(optimization_level=1)
    transpiled = pm.run(qc)
    qasm_str = transpiled.qasm()
    with open(filename, "w") as f:
        f.write(qasm_str)
    return transpiled


if __name__ == "__main__":
    import time
    from math import gcd

    # (a, N) pairs for increasing sizes
    # Pick a coprime to N for each; N are products of two primes
    test_cases = [
        (7, 15),      # 4-bit
        (2, 21),      # 5-bit
        (3, 35),      # 6-bit
        (5, 77),      # 7-bit
        (3, 143),     # 8-bit
    ]

    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    from qiskit.qasm2 import dumps as qasm2_dumps

    print(f"{'N':>6} {'a':>4} {'n_bits':>6} {'n_count':>7} {'qubits':>6}  {'depth':>7}  {'gates':>7}  {'cx':>7}  {'time':>8}")
    print("-" * 75)

    for a, N in test_cases:
        assert gcd(a, N) == 1, f"gcd({a},{N}) != 1"
        t0 = time.time()
        qc = mod_exp_simple(a, N)

        # Transpile to basis gates for meaningful depth/gate counts
        pm = generate_preset_pass_manager(optimization_level=1)
        transpiled = pm.run(qc)

        elapsed = time.time() - t0
        n_bits = int(np.ceil(np.log2(N + 1)))
        n_count = 2 * n_bits
        depth = transpiled.depth()
        total_gates = transpiled.size()
        cx_count = transpiled.count_ops().get("cx", 0)

        print(f"{N:>6} {a:>4} {n_bits:>6} {n_count:>7} {transpiled.num_qubits:>6}  {depth:>7}  {total_gates:>7}  {cx_count:>7}  {elapsed:>7.2f}s")

        # Export QASM
        qasm_file = f"qasm/mod_exp_{a}x_mod{N}.qasm"
        with open(qasm_file, "w") as f:
            f.write(qasm2_dumps(transpiled))
        print(f"       -> {qasm_file}")
