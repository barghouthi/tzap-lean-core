"""PennyLane transform integration for tzap."""

from __future__ import annotations

import math
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

import pennylane as qml
from pennylane.tape import QuantumScript

from ._core import optimize_qasm


class PennyLaneError(ValueError):
    """A PennyLane circuit cannot be represented safely by tzap."""


_SIMPLE_OPERATIONS = (
    (qml.PauliX, "x"),
    (qml.Hadamard, "h"),
    (qml.S, "s"),
    (qml.PauliZ, "z"),
    (qml.T, "t"),
    (qml.RZ, "rz"),
    (qml.CNOT, "cx"),
    (qml.CZ, "cz"),
    (qml.Toffoli, "ccx"),
    (qml.CCZ, "ccz"),
)

_ARITIES = {
    "x": 1,
    "h": 1,
    "s": 1,
    "sdg": 1,
    "z": 1,
    "t": 1,
    "tdg": 1,
    "rz": 1,
    "cx": 2,
    "cz": 2,
    "ccx": 3,
    "ccz": 3,
}


def _operation_name(operation) -> str:
    if isinstance(operation, qml.ops.op_math.Adjoint):
        if isinstance(operation.base, qml.S):
            return "sdg"
        if isinstance(operation.base, qml.T):
            return "tdg"
        raise PennyLaneError(
            "tzap does not support PennyLane operation {!r}; only adjoints of "
            "S and T are supported".format(operation.name)
        )

    for operation_type, name in _SIMPLE_OPERATIONS:
        if isinstance(operation, operation_type):
            return name
    raise PennyLaneError(
        "tzap does not support PennyLane operation {!r}; decompose to "
        "[PauliX, Hadamard, S, Adjoint(S), PauliZ, T, Adjoint(T), RZ, "
        "CNOT, CZ, Toffoli, CCZ] before applying tzap".format(operation.name)
    )


def _concrete_angle(operation) -> float:
    try:
        angle = operation.data[0]
    except (AttributeError, IndexError) as error:
        raise PennyLaneError("RZ must have exactly one angle") from error

    if qml.math.requires_grad(angle) or qml.math.is_abstract(angle):
        raise PennyLaneError(
            "tzap requires RZ angles to be concrete and non-trainable; "
            "optimizing a trainable or traced angle would break autodiff"
        )
    try:
        value = float(angle)
    except (TypeError, ValueError) as error:
        raise PennyLaneError("tzap requires RZ angles to be real scalars") from error
    if not math.isfinite(value):
        raise PennyLaneError("tzap requires finite RZ angles")
    return value


def _tape_to_qasm(
    tape: QuantumScript,
) -> Tuple[str, Sequence[object], Sequence[object]]:
    wires = tuple(tape.wires)
    # QuantumScript derives wire order by first appearance. For conventional
    # integer or string labels, a canonical ordering avoids changing tzap's
    # greedy window choices merely because a high-numbered wire happened to
    # receive the first operation. Mixed/custom labels may not be orderable,
    # in which case PennyLane's own order remains the deterministic fallback.
    try:
        wires = tuple(sorted(wires))
    except TypeError:
        pass
    wire_indices: Dict[object, int] = {
        wire: index for index, wire in enumerate(wires)
    }
    global_phases = []
    lines = [
        "OPENQASM 2.0;",
        'include "qelib1.inc";',
        "qreg q[{}];".format(len(wires)),
    ]

    for operation in tape.operations:
        if isinstance(operation, qml.GlobalPhase):
            global_phases.append(operation)
            continue

        name = _operation_name(operation)
        operation_wires = tuple(operation.wires)
        if len(operation_wires) != _ARITIES[name]:
            raise PennyLaneError(
                "operation {!r} has {} wires, expected {}".format(
                    operation.name,
                    len(operation_wires),
                    _ARITIES[name],
                )
            )
        operands = ",".join(
            "q[{}]".format(wire_indices[wire]) for wire in operation_wires
        )
        if name == "rz":
            lines.append("rz({!r}) {};".format(_concrete_angle(operation), operands))
        else:
            lines.append("{} {};".format(name, operands))

    return "\n".join(lines) + "\n", wires, tuple(global_phases)


def _index(operand: str) -> int:
    return int(operand[operand.index("[") + 1 : operand.index("]")])


def _indices(operands: str) -> List[int]:
    return [_index(operand.strip()) for operand in operands.split(",")]


def _output_operations(qasm: str, wires: Sequence[object]):
    operations = []
    with qml.QueuingManager.stop_recording():
        for raw_line in qasm.splitlines():
            line = raw_line.strip()
            if (
                not line
                or line.startswith("OPENQASM")
                or line.startswith("include ")
                or line.startswith("qreg ")
                or line.startswith("creg ")
            ):
                continue

            statement = line[:-1] if line.endswith(";") else line
            name, operands = statement.split(" ", 1)
            wire_operands = [wires[index] for index in _indices(operands)]
            if name.startswith("rz("):
                operations.append(
                    qml.RZ(float(name[3 : name.rfind(")")]), wires=wire_operands[0])
                )
            elif name == "x":
                operations.append(qml.PauliX(wires=wire_operands[0]))
            elif name == "h":
                operations.append(qml.Hadamard(wires=wire_operands[0]))
            elif name == "s":
                operations.append(qml.S(wires=wire_operands[0]))
            elif name == "sdg":
                operations.append(qml.adjoint(qml.S(wires=wire_operands[0])))
            elif name == "z":
                operations.append(qml.PauliZ(wires=wire_operands[0]))
            elif name == "t":
                operations.append(qml.T(wires=wire_operands[0]))
            elif name == "tdg":
                operations.append(qml.adjoint(qml.T(wires=wire_operands[0])))
            elif name == "cx":
                operations.append(qml.CNOT(wires=wire_operands))
            elif name == "cz":
                operations.append(qml.CZ(wires=wire_operands))
            elif name == "ccx":
                operations.append(qml.Toffoli(wires=wire_operands))
            elif name == "ccz":
                operations.append(qml.CCZ(wires=wire_operands))
            else:
                raise PennyLaneError(
                    "tzap returned an operation unsupported by the PennyLane "
                    "adapter: {!r}".format(name)
                )
    return operations


@qml.transform
def _optimize_transform(
    tape: QuantumScript,
    *,
    level: str = "O3",
    passes: Optional[Iterable[str]] = None,
    fixpoint: bool = False,
    decompose_rz: bool = False,
    decompose_cz: bool = False,
    rz_epsilon: float = 1e-10,
    expr: bool = False,
    parallel: bool = False,
    superopt_qubits: Optional[int] = None,
    superopt_window_gates: Optional[int] = None,
    superopt_table_entries: Optional[int] = None,
):
    """Optimize a PennyLane tape, quantum function, or QNode with tzap.

    Terminal measurements and observables are retained by copying the input
    ``QuantumScript`` with only its operation list replaced. Existing
    ``GlobalPhase`` operations are preserved. RZ parameters must be concrete,
    finite, and non-trainable.
    """

    qasm, wires, global_phases = _tape_to_qasm(tape)
    pass_list = None if passes is None else tuple(passes)
    result = optimize_qasm(
        qasm,
        level=level,
        passes=pass_list,
        fixpoint=fixpoint,
        decompose_rz=decompose_rz,
        decompose_cz=decompose_cz,
        rz_epsilon=rz_epsilon,
        expr=expr,
        parallel=parallel,
        superopt_qubits=superopt_qubits,
        superopt_window_gates=superopt_window_gates,
        superopt_table_entries=superopt_table_entries,
    )
    optimized_operations = [
        *global_phases,
        *_output_operations(result.qasm, wires),
    ]
    transformed_tape = tape.copy(operations=optimized_operations)

    def null_postprocessing(results):
        return results[0]

    return (transformed_tape,), null_postprocessing


def optimize(
    tape=None,
    *,
    level: str = "O3",
    passes: Optional[Iterable[str]] = None,
    fixpoint: bool = False,
    decompose_rz: bool = False,
    decompose_cz: bool = False,
    rz_epsilon: float = 1e-10,
    expr: bool = False,
    parallel: bool = False,
    superopt_qubits: Optional[int] = None,
    superopt_window_gates: Optional[int] = None,
    superopt_table_entries: Optional[int] = None,
):
    """Optimize a PennyLane tape, quantum function, or QNode with tzap.

    Called without a circuit-like first argument, this returns a decorator.
    This wrapper keeps parameterized-decorator syntax consistent across
    PennyLane versions whose transform dispatchers differ on that syntax.
    """

    options = {
        "level": level,
        "passes": None if passes is None else tuple(passes),
        "fixpoint": fixpoint,
        "decompose_rz": decompose_rz,
        "decompose_cz": decompose_cz,
        "rz_epsilon": rz_epsilon,
        "expr": expr,
        "parallel": parallel,
        "superopt_qubits": superopt_qubits,
        "superopt_window_gates": superopt_window_gates,
        "superopt_table_entries": superopt_table_entries,
    }

    def apply_transform(target):
        return _optimize_transform(target, **options)

    if tape is None:
        return apply_transform
    return apply_transform(tape)


tzap_transform = optimize

__all__ = ["PennyLaneError", "optimize", "tzap_transform"]
