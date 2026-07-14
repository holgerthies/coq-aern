#!/usr/bin/env python3
"""Evaluation of the extracted fractal-drawing examples.

Each example `*_tbounded n` returns a finite set of balls, each of radius
2^-(n+1), whose union is within Hausdorff distance <= 2^-n of the fractal.

For each example we increase n by 1 (n = 1, 2, 3, ...), computing the cover
and forcing every center coordinate/radius to a FIXED precision --prec
(default 53 bits = standard double), independent of n. As long as
prec > n (always true here, since the ball count caps us near n~15), this
is at least as accurate as the cover radius 2^-(n+1).
We record the number of balls and the wall-clock time of the computation
(excluding process start-up). Because the ball count grows like 3^n / 4^n,
any single run exceeding --timeout is killed and we move on to the next
example (larger n would only be slower).

--prec may list several precisions (default: 53 106, i.e. one and two
doubles); all are swept SEQUENTIALLY into a SINGLE CSV, each row tagged with
its coord_bits, so no separate per-precision files are needed.

Usage:
    python3 evaluate_fractals.py [--max-n N] [--prec BITS ...] [--timeout S] [--out FILE]

Requires `stack`. The script builds the `eval-fractals` executable.
"""
import argparse, csv, os, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
EXAMPLES = ["Tn", "STRn", "STEn", "STE4n", "STRLim"]

# For each example: (label, kind, generating basis).
#   kind = what the covered set actually IS:
#     "limit"  -> covers the true self-similar attractor (ST/STR fixpoint)
#     "stage"  -> covers a FINITE construction stage, not the limit
#     "solid"  -> a solid region, not a fractal
# Each Sierpinski map is f_v(p) = (p + v)/2 (contraction ratio 1/2, fixed point v).
META = {
 "Tn":     ("triangle",                        "solid",
            "filled right triangle T = {0<=x, 0<=y, x+y<=1} (grid cover)"),
 "STRn":   ("Sierpinski (right)",              "limit",
            "vertices (0,1),(0,0),(1,0); 3 maps ratio 1/2 -- limit attractor"),
 "STEn":   ("Sierpinski (equilateral)",        "limit",
            "vertices (-1,-1),(1,-1),(0,sqrt3-1); 3 maps ratio 1/2 -- limit attractor"),
 "STE4n":  ("Sierpinski (equilateral, 4-map)", "limit",
            "STE vertices + centroid (0,sqrt3/3-1); 4 maps ratio 1/2 -- limit attractor"),
 "STRLim": ("Sierpinski (limit)",              "limit",
            "vertices (0,1),(0,0),(1,0); limit of any X with STR X -- limit attractor"),
}
LABEL = {ex: m[0] for ex, m in META.items()}
KIND  = {ex: m[1] for ex, m in META.items()}
BASIS = {ex: m[2] for ex, m in META.items()}

def stack(*args, **kw):
    return subprocess.run(["stack", *args], cwd=HERE, **kw)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=40,
                    help="hard cap on accuracy n (the timeout usually stops us first)")
    ap.add_argument("--prec", type=int, nargs="+", default=[53, 106],
                    help="fixed bits for center coords; may list several (default 53 106 = 1 & 2 doubles)")
    ap.add_argument("--timeout", type=float, default=300.0,
                    help="per-run timeout (s); on timeout we skip to the next example")
    ap.add_argument("--out", default="fractal_eval.csv")
    args = ap.parse_args()

    print("building eval-fractals ...", flush=True)
    stack("build", "coq-aern-extracted:exe:eval-fractals", check=True)
    binpath = stack("exec", "--", "which", "eval-fractals",
                    capture_output=True, text=True, check=True).stdout.strip()

    # Sweep every requested precision into ONE file; each row is tagged with
    # coord_bits, so no need for separate per-precision files. Runs stay
    # sequential (one subprocess at a time) so timings are never distorted.
    rows = []          # (example, prec, n, num_balls, seconds)
    for prec in args.prec:
        print(f"\n### centers @ {prec} bits ###", flush=True)
        for ex in EXAMPLES:
            for n in range(1, args.max_n + 1):
                try:
                    times = []
                    nballs = None

                    for _ in range(3):
                        out = subprocess.run(
                            [binpath, ex, str(n), str(prec)],
                            capture_output=True,
                            text=True,
                            timeout=args.timeout,
                        )
                        parts = out.stdout.strip().split(",")
                        if nballs is None:
                            nballs = int(parts[3])
                        times.append(float(parts[4]))

                    secs = sum(times) / len(times)

                    print(f"  {ex:7} n={n:<2} (err<=2^-{n})  balls={nballs:<9} time={secs:9.4f}s", flush=True)
                    rows.append((ex, prec, n, nballs, secs))
                except subprocess.TimeoutExpired:
                    print(f"  {ex:7} n={n:<2} (err<=2^-{n})  >{args.timeout:g}s -> skip to next example", flush=True)
                    rows.append((ex, prec, n, None, None))
                    break   # larger n is only slower; move on

    with open(os.path.join(HERE, args.out), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["example", "description", "kind", "basis",
                    "coord_bits", "accuracy_n", "num_balls", "time_seconds"])
        for ex, prec, n, nb, t in rows:
            w.writerow([ex, LABEL[ex], KIND[ex], BASIS[ex], prec, n,
                        "" if nb is None else nb, "" if t is None else f"{t:.6f}"])
    print(f"\nwrote {args.out}")

    KIND_DESC = {"limit": "covers the true limit attractor",
                 "solid": "solid region, not a fractal"}

    # basis legend: what each example fractal is generated from
    print("\n=== Generating basis of the example fractals ===\n")
    for ex in EXAMPLES:
        print(f"  {ex:7} [{KIND[ex]:5}] {LABEL[ex]}")
        print(f"          {BASIS[ex]}")
    print("\n  kind: " + "; ".join(f"{k} = {v}" for k, v in KIND_DESC.items()))

    # per-example summary: largest n reached within the timeout, per precision
    for prec in args.prec:
        dd = " (= 2 doubles)" if prec == 106 else (" (= 1 double)" if prec == 53 else "")
        print(f"\n=== Largest accuracy n reached within {args.timeout:g}s "
              f"(centers @ {prec} bits{dd}) ===\n")
        print(f"{'example':34} | {'kind':5} | {'max n (err 2^-n)':16} | {'num balls':>11} | {'time (s)':>9}")
        print("-" * 92)
        for ex in EXAMPLES:
            done = [(n, nb, t) for (e, p, n, nb, t) in rows if e == ex and p == prec and t is not None]
            if done:
                n, nb, t = done[-1]
                print(f"{ex+' ('+LABEL[ex]+')':34} | {KIND[ex]:5} | n={n:<2} (2^-{n}){'':6} | {nb:>11} | {t:9.3f}")
            else:
                print(f"{ex+' ('+LABEL[ex]+')':34} | {KIND[ex]:5} | (timed out at n=1){'':1}| {'':>11} | {'':>9}")

if __name__ == "__main__":
    main()
