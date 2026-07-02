#!/usr/bin/env python3
"""Draw the extracted fractal covers on the fly, straight from Haskell.

Builds the `eval-fractals` executable, asks it (in its `js` mode) for the ball
cover of each (example, n) at double-precision (53-bit) centers, and renders
each set as gray squares on white -- drawn at true ball size so the fractal
holes show. Output PNG + PDF go to gallery/img/ (override with --out).

No data.js needed; the ball data is produced live per call.

Examples:
    python3 draw_fractals.py                 # batch: STRn STEn STE4n x n=0,2,5,10
    python3 draw_fractals.py STRn 5 --show   # one figure, then open it
    python3 draw_fractals.py --examples STEn STE4n --ns 3 6 --gray 100

Requires `stack` and Python `Pillow`.
"""
import argparse, json, os, re, subprocess
from PIL import Image, ImageDraw

HERE = os.path.dirname(os.path.abspath(__file__))
DEF_EXAMPLES = ["STRn", "STEn", "STE4n"]
DEF_NS = [0, 2, 5, 10]

def stack(*args, **kw):
    return subprocess.run(["stack", *args], cwd=HERE, **kw)

def build_binary():
    print("building eval-fractals ...", flush=True)
    stack("build", "coq-aern-extracted:exe:eval-fractals", check=True)
    return stack("exec", "--", "which", "eval-fractals",
                 capture_output=True, text=True, check=True).stdout.strip()

def ball_data(binpath, ex, n):
    """Run `eval-fractals <ex> <n> js` and parse its DATA line -> {"r":.., "c":[[x,y],..]}."""
    out = subprocess.run([binpath, ex, str(n), "js"],
                         capture_output=True, text=True, check=True).stdout
    m = re.search(r'=\s*(\{.*\});', out)
    if not m:
        raise RuntimeError(f"could not parse ball data for {ex} n={n}:\n{out[:200]}")
    return json.loads(m.group(1))

def render(d, size, gray, margin):
    img = Image.new("RGB", (size, size), "white")
    if not d or not d["c"]:
        return img
    dr = ImageDraw.Draw(img)
    r = d["r"]
    xs = [c[0] for c in d["c"]]; ys = [c[1] for c in d["c"]]
    minX, maxX = min(xs) - r, max(xs) + r
    minY, maxY = min(ys) - r, max(ys) + r
    span = max(maxX - minX, maxY - minY) or 1.0
    s = (size - 2*margin) / span                     # world -> px
    ox = margin + (size - 2*margin - (maxX - minX)*s) / 2
    oy = margin + (size - 2*margin - (maxY - minY)*s) / 2
    half = r * s                                      # true half-side (tiles cells exactly)
    fill = (gray, gray, gray)
    for x, y in d["c"]:
        px = ox + (x - minX)*s
        py = size - (oy + (y - minY)*s)               # flip y so +y is up
        dr.rectangle([px-half, py-half, px+half, py+half], fill=fill)
    return img

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("example", nargs="?", help="single example (e.g. STRn); omit for batch")
    ap.add_argument("n", nargs="?", type=int, help="single accuracy n")
    ap.add_argument("--examples", nargs="+", default=DEF_EXAMPLES, help="batch example list")
    ap.add_argument("--ns", nargs="+", type=int, default=DEF_NS, help="batch n list")
    ap.add_argument("--size", type=int, default=2000, help="output resolution (px)")
    ap.add_argument("--gray", type=int, default=128, help="fill gray 0(black)-255(white)")
    ap.add_argument("--margin", type=int, default=24)
    ap.add_argument("--out", default=os.path.join(HERE, "gallery", "img"))
    ap.add_argument("--show", action="store_true", help="open the PNG(s) after drawing (macOS)")
    args = ap.parse_args()

    if args.example is not None and args.n is not None:
        jobs = [(args.example, args.n)]
    else:
        jobs = [(ex, n) for ex in args.examples for n in args.ns]

    binpath = build_binary()
    os.makedirs(args.out, exist_ok=True)
    for ex, n in jobs:
        d = ball_data(binpath, ex, n)
        img = render(d, args.size, args.gray, args.margin)
        base = os.path.join(args.out, f"{ex}_{n}")
        img.save(base + ".png")
        img.save(base + ".pdf", "PDF", resolution=300.0)
        print(f"  {ex+'_'+str(n):10} {len(d['c']):>8} balls -> {os.path.relpath(base, HERE)}.png/.pdf")
        if args.show:
            subprocess.run(["open", base + ".png"])

if __name__ == "__main__":
    main()
