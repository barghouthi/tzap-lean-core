import subprocess
import sys

from qiskit import qasm2

QASM = """\
OPENQASM 2.0;
include "qelib1.inc";
qreg q[1];
h q[0];
h q[0];
"""


def run_module(*args):
    return subprocess.run(
        [sys.executable, "-m", "tzap", *map(str, args)],
        check=False,
        capture_output=True,
        text=True,
    )


def test_module_version():
    completed = run_module("--version")

    assert completed.returncode == 0
    assert completed.stdout.startswith("tzap ")
    assert completed.stderr == ""


def test_module_help():
    completed = run_module("--help")

    assert completed.returncode == 0
    assert "fast Clifford+T circuit optimizer" in completed.stdout
    assert "--decompose-rz" in completed.stdout


def test_module_optimizes_to_output_flag(tmp_path):
    source = tmp_path / "input.qasm"
    output = tmp_path / "output.qasm"
    source.write_text(QASM, encoding="utf-8")

    completed = run_module(source, "-O1", "-o", output)

    assert completed.returncode == 0
    assert "2 -> 0 gates" in completed.stderr
    assert "wrote" in completed.stderr
    assert output.exists()
    assert len(qasm2.load(output).data) == 0


def test_module_supports_positional_output(tmp_path):
    source = tmp_path / "input.qasm"
    output = tmp_path / "output.qasm"
    source.write_text(QASM, encoding="utf-8")

    completed = run_module(source, output, "-O1")

    assert completed.returncode == 0
    assert output.exists()


def test_module_custom_pass_pipeline(tmp_path):
    source = tmp_path / "input.qasm"
    output = tmp_path / "output.qasm"
    source.write_text(QASM, encoding="utf-8")

    completed = run_module(
        source,
        "-o",
        output,
        "--passes",
        "CancelGates,PhaseFoldRand",
    )

    assert completed.returncode == 0
    assert len(qasm2.load(output).data) == 0


def test_module_missing_input_is_an_argparse_error():
    completed = run_module()

    assert completed.returncode == 2
    assert "required" in completed.stderr


def test_module_missing_file_is_reported_without_traceback(tmp_path):
    completed = run_module(tmp_path / "missing.qasm", "-O1")

    assert completed.returncode == 1
    assert "Error:" in completed.stderr
    assert "Traceback" not in completed.stderr


def test_module_bad_qasm_is_reported_without_traceback(tmp_path):
    source = tmp_path / "bad.qasm"
    source.write_text(
        "OPENQASM 2.0; qreg q[1]; y q[0];",
        encoding="utf-8",
    )

    completed = run_module(source, "-O1")

    assert completed.returncode == 1
    assert "unsupported" in completed.stderr
    assert "Traceback" not in completed.stderr


def test_module_rejects_invalid_epsilon_cleanly(tmp_path):
    source = tmp_path / "input.qasm"
    source.write_text(QASM, encoding="utf-8")

    completed = run_module(source, "-O1", "--epsilon", "0")

    assert completed.returncode == 1
    assert "positive, finite" in completed.stderr
