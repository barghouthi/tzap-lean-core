"""Smoke-test an installed wheel and its default framework integrations."""

from pathlib import Path

import pennylane as qml
import tzap
from qiskit import QuantumCircuit
from tzap.pennylane import optimize as optimize_pennylane
from tzap.qiskit import optimize as optimize_qiskit

package_dir = Path(tzap.__file__).parent
assert (package_dir / "py.typed").is_file()
assert (package_dir / "_native.pyi").is_file()

result = tzap.optimize_qasm(
    """\
OPENQASM 2.0;
include "qelib1.inc";
qreg q[1];
x q[0];
x q[0];
""",
    level="O1",
)

assert result.report.input.gates == 2
assert result.report.output.gates == 0

qiskit_circuit = QuantumCircuit(1)
qiskit_circuit.x(0)
qiskit_circuit.x(0)
assert not optimize_qiskit(qiskit_circuit, level="O1").data

pennylane_tape = qml.tape.QuantumScript([qml.PauliX(0), qml.PauliX(0)])
pennylane_tapes, _ = optimize_pennylane(pennylane_tape, level="O1")
assert not pennylane_tapes[0].operations
