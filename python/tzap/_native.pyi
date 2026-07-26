from typing_extensions import TypeAlias

RawMetrics: TypeAlias = tuple[int, int, int, int, int]
RawReport: TypeAlias = tuple[RawMetrics, RawMetrics, RawMetrics]

class TzapError(Exception): ...
class QasmError(TzapError): ...
class OptimizationError(TzapError): ...

__version__: str

def _optimize_qasm(
    qasm: str,
    *,
    level: str = "O3",
    passes: list[str] | None = None,
    fixpoint: bool = False,
    decompose_rz: bool = False,
    decompose_cz: bool = False,
    rz_epsilon: float = 1e-10,
    expr: bool = False,
    parallel: bool = False,
    superopt_qubits: int | None = None,
    superopt_window_gates: int | None = None,
    superopt_table_entries: int | None = None,
) -> tuple[str, RawReport]: ...
