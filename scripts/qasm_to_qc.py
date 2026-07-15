#!/usr/bin/env python3
"""Convert the OpenQASM subset emitted by tzap into Feynman .qc syntax."""

import re
import sys


def qid(text: str) -> str:
    match = re.fullmatch(r"q\[(\d+)\]", text.strip())
    if not match:
        raise ValueError(f"unsupported qubit operand: {text!r}")
    return f"q{match.group(1)}"


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: qasm_to_qc.py input.qasm output.qc")
    inp, out = sys.argv[1], sys.argv[2]
    num_qubits = None
    gates = []

    with open(inp) as handle:
        for raw in handle:
            line = raw.split("//", 1)[0].strip()
            if not line:
                continue
            if line.startswith(("OPENQASM", "include", "creg")):
                continue

            qreg = re.fullmatch(r"qreg\s+q\[(\d+)\];", line)
            if qreg:
                num_qubits = int(qreg.group(1))
                continue

            one = re.fullmatch(r"(h|x|z|s|sdg|t|tdg)\s+(q\[\d+\]);", line)
            if one:
                name, q = one.groups()
                gate = {
                    "h": "H",
                    "x": "X",
                    "z": "Z",
                    "s": "S",
                    "sdg": "S*",
                    "t": "T",
                    "tdg": "T*",
                }[name]
                gates.append(f"{gate} {qid(q)}")
                continue

            two = re.fullmatch(r"(cx|cnot|cz)\s+(q\[\d+\]),\s*(q\[\d+\]);", line)
            if two:
                name, a, b = two.groups()
                gate = "cnot" if name in {"cx", "cnot"} else "cz"
                gates.append(f"{gate} {qid(a)} {qid(b)}")
                continue

            three = re.fullmatch(
                r"(ccx|tof)\s+(q\[\d+\]),\s*(q\[\d+\]),\s*(q\[\d+\]);",
                line,
            )
            if three:
                _, a, b, c = three.groups()
                gates.append(f"tof {qid(a)} {qid(b)} {qid(c)}")
                continue

            raise ValueError(f"unsupported qasm line: {line!r}")

    if num_qubits is None:
        raise ValueError("missing qreg q[...] declaration")

    qubits = [f"q{i}" for i in range(num_qubits)]
    with open(out, "w") as handle:
        handle.write(".v " + " ".join(qubits) + "\n")
        handle.write(".i " + " ".join(qubits) + "\n")
        handle.write(".o " + " ".join(qubits) + "\n\n")
        handle.write("BEGIN\n\n")
        for gate in gates:
            handle.write(gate + "\n")
        handle.write("\nEND\n")


if __name__ == "__main__":
    main()
