from typing import List, Optional, Tuple

RawMetrics = Tuple[int, int, int, int, int]
RawReport = Tuple[RawMetrics, RawMetrics, RawMetrics]

class TzapError(Exception): ...
class QasmError(TzapError): ...
class OptimizationError(TzapError): ...

__version__: str

def _optimize_qasm(
    qasm: str,
    *,
    level: str = "O3",
    passes: Optional[List[str]] = None,
    fixpoint: bool = False,
    decompose_rz: bool = False,
    decompose_cz: bool = False,
    rz_epsilon: float = 1e-10,
    expr: bool = False,
    parallel: bool = False,
    superopt_qubits: Optional[int] = None,
    superopt_window_gates: Optional[int] = None,
    superopt_table_entries: Optional[int] = None,
) -> Tuple[str, RawReport]: ...
