#!/usr/bin/env python3
"""
Plot runtime vs input circuit size for tzap and quizx on gf2* circuits.

Usage:
    python3 scripts/plot_timing.py [--out timing.png]
"""

import argparse
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# Data from benchmark run (t_in, runtime_ms)
TZAP_DATA = [
    (112,    8),
    (175,    4),
    (252,    8),
    (343,    4),
    (448,    5),
    (567,    5),
    (700,    8),
    (1792,  11),
    (7168,   9),
    (28672, 17),
    (114688, 83),
]

QUIZX_DATA = [
    (112,       8),
    (175,       9),
    (252,      12),
    (343,      16),
    (448,      26),
    (567,      34),
    (700,      67),
    (1792,    520),
    (7168,  23482),
]

QUIZX_TIMEOUTS = [28672, 114688]  # timed out at 5 min

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="timing.png")
    args = parser.parse_args()

    # ── plot ──────────────────────────────────────────────────────────────────
    fig, ax = plt.subplots(figsize=(8, 5))

    if tzap_pts:
        xs, ys = zip(*sorted(tzap_pts))
        ax.plot(xs, ys, "o-", color="#2196F3", label="tzap", linewidth=2, markersize=6)

    if quizx_pts:
        xs, ys = zip(*sorted(quizx_pts))
        ax.plot(xs, ys, "s-", color="#F44336", label="quizx", linewidth=2, markersize=6)

    for t_in in quizx_timeouts:
        ax.axvline(x=t_in, color="#F44336", linestyle=":", alpha=0.4)
        ax.annotate("timeout", xy=(t_in, ax.get_ylim()[1]),
                    xytext=(t_in, ax.get_ylim()[1]),
                    color="#F44336", fontsize=8, ha="center", va="bottom")

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Input T-gate count", fontsize=12)
    ax.set_ylabel("Runtime (ms)", fontsize=12)
    ax.set_title("Runtime vs circuit size — gf2 multipliers", fontsize=13)
    ax.legend(fontsize=11)
    ax.grid(True, which="both", linestyle="--", alpha=0.4)
    ax.xaxis.set_major_formatter(ticker.FuncFormatter(lambda x, _: f"{x:,.0f}"))
    ax.yaxis.set_major_formatter(ticker.FuncFormatter(lambda x, _: f"{x:,.0f}"))

    plt.tight_layout()
    plt.savefig(args.out, dpi=150)
    print(f"\nSaved to {args.out}")

if __name__ == "__main__":
    main()
