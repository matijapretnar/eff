#!/usr/bin/env python3
"""Draw the results of bench.py as graphs.

For each benchmark, the graph shows the ratio of the time of each variant to
the time of the baseline native-pure, for each input size, on a logarithmic
scale. A variant that failed, gave a wrong result, or exceeded the time limit
at some size has a cross above the graph at that size. The script writes
graphs.tex next to summary.csv and compiles it to graphs.pdf with pdflatex.
"""

import argparse
import csv
import subprocess
from collections import defaultdict
from pathlib import Path

# Style of each variant: colour, line and mark. Native variants are grey, the
# suite's OCaml 5 programs black, and Eff blue (plain OCaml) or red (OCaml 5
# handlers), dashed without optimisations.
STYLES = {
    "native-pure": "gray, mark=none, thick",
    "native-ref": "gray, mark=square*, mark size=1.2pt",
    "native-exn": "gray, mark=triangle*, mark size=1.5pt",
    "native-seq": "gray, mark=diamond*, mark size=1.5pt",
    "ocaml5": "black, mark=*, mark size=1.2pt",
    "eff-plain": "blue, mark=*, mark size=1.2pt, thick",
    "eff-plain-noopt": "blue, dashed, mark=o, mark size=1.2pt",
    "eff-handlers": "red, mark=*, mark size=1.2pt, thick",
    "eff-handlers-noopt": "red, dashed, mark=o, mark size=1.2pt",
}
STOPPED = ("timeout", "skipped", "failed", "wrong")


def tex_name(name):
    return name.replace("_", r"\_")


def short(n):
    """A size in at most four characters, such as 7.5k or 32M"""
    if n >= 1_000_000:
        return f"{n / 1_000_000:g}M"
    if n >= 10_000:
        return f"{n / 1_000:g}k"
    return str(n)


def read(summary):
    """Ratios and stopped sizes, by benchmark and variant"""
    ratios = defaultdict(lambda: defaultdict(list))
    stopped = defaultdict(lambda: defaultdict(list))
    sizes = defaultdict(set)
    for row in csv.DictReader(open(summary)):
        if not row["size"]:
            continue
        b, v, n = row["benchmark"], row["variant"], int(row["size"])
        sizes[b].add(n)
        if row["status"] in ("ok", "checked"):
            ratios[b][v].append((n, float(row["ratio"])))
        elif row["status"] in STOPPED:
            stopped[b][v].append(n)
    return ratios, stopped, sizes


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("summary", type=Path, help="summary.csv from bench.py")
    p.add_argument("--columns", type=int, default=3)
    args = p.parse_args()

    ratios, stopped, sizes = read(args.summary)
    benchmarks = sorted(sizes)
    rows = (len(benchmarks) + args.columns - 1) // args.columns

    body = []
    for i, b in enumerate(benchmarks):
        ticks = ",".join(str(n) for n in sorted(sizes[b]))
        labels = ",".join(short(n) for n in sorted(sizes[b]))
        options = [
            f"title={{{tex_name(b)}}}",
            f"xtick={{{ticks}}}",
            f"xticklabels={{{labels}}}",
        ]
        # Sizes that double are evenly spaced on a logarithmic axis
        if max(sizes[b]) >= 4 * min(sizes[b]):
            options.append("xmode=log, log basis x=2")
        if i % args.columns == 0:
            options.append("ylabel={time / native-pure}")
        if i == 0:
            options.append("legend to name=legend")
        body.append(rf"\nextgroupplot[{', '.join(options)}]")
        if i == 0:
            # The legend comes from these images, so that a variant without
            # data does not shift the entries.
            for variant, style in STYLES.items():
                body.append(rf"\addlegendimage{{{style}}}")
                body.append(rf"\addlegendentry{{{tex_name(variant)}}}")
        for variant, style in STYLES.items():
            points = sorted(ratios[b].get(variant, []))
            if points:
                coords = " ".join(f"({n},{r})" for n, r in points)
                body.append(rf"\addplot[{style}, forget plot] coordinates {{{coords}}};")
        # A cross at the top edge for each size where a variant stopped
        for variant, ns in stopped[b].items():
            colour = STYLES[variant].split(",")[0]
            for n in ns:
                body.append(
                    rf"\node[{colour}, inner sep=0pt, anchor=south] "
                    rf"at ({{axis cs:{n},1}} |- {{rel axis cs:0,1}}) "
                    r"{\scriptsize$\times$};"
                )

    tex = rf"""\documentclass{{standalone}}
\usepackage{{pgfplots}}
\pgfplotsset{{compat=1.18}}
\usepgfplotslibrary{{groupplots}}
\begin{{document}}
\begin{{tikzpicture}}
\begin{{groupplot}}[
  group style={{group size={args.columns} by {rows}, horizontal sep=1.4cm, vertical sep=1.6cm}},
  width=6cm, height=4.5cm,
  ymode=log, log basis y=10,
  xticklabel style={{font=\tiny, rotate=30, anchor=east}},
  yticklabel style={{font=\tiny}},
  title style={{font=\small}},
  ylabel style={{font=\scriptsize}},
  clip=false,
  legend columns=5,
  legend style={{font=\scriptsize, draw=none}},
  legend cell align=left,
]
{chr(10).join(body)}
\end{{groupplot}}
\node[anchor=north] at ([yshift=-0.4cm]current bounding box.south) {{\pgfplotslegendfromname{{legend}}}};
\end{{tikzpicture}}
\end{{document}}
"""
    out = args.summary.parent / "graphs.tex"
    out.write_text(tex)
    r = subprocess.run(
        ["pdflatex", "-interaction=nonstopmode", out.name],
        cwd=out.parent,
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        print(r.stdout[-3000:])
        raise SystemExit("pdflatex failed")
    print(out.with_suffix(".pdf"))


if __name__ == "__main__":
    main()
