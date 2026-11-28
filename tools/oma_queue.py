#!/usr/bin/env python3
"""Print a queue of problems with no Lean statement yet, best known first, for tools/oma.sh next (OMA_QUEUE).

  python3 -I tools/oma_queue.py [--source "OEIS conjectures (not formalized)"] [--part K/N] > queue.txt

The long-tail catalogue (data/extra2.json) is already sorted by fame. Problems that already have a statement in
statements/ are left out. --part K/N keeps every N-th problem starting at the K-th (0-based), so N fleets of one owner
can work disjoint queues and never ask the desk for the same problem.
"""
import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

ap = argparse.ArgumentParser()
ap.add_argument("--source", default="OEIS conjectures (not formalized)")
ap.add_argument("--part", default="0/1", help="K/N: keep the problems whose rank is K modulo N")
a = ap.parse_args()
k, n = (int(x) for x in a.part.split("/"))
if not 0 <= k < n:
    sys.exit("oma_queue: --part K/N needs 0 <= K < N")

data = json.load(open(os.path.join(ROOT, "data", "extra2.json"), encoding="utf-8"))
if a.source not in data["sources"]:
    sys.exit("oma_queue: unknown source %r; sources: %s" % (a.source, ", ".join(data["sources"])))
src = data["sources"].index(a.source)
stated = {f[:-5] for f in os.listdir(os.path.join(ROOT, "statements")) if f.endswith(".lean")}
rank = 0
for row in data["rows"]:
    pid = row[0]
    if row[2] != src or pid in stated:
        continue
    if rank % n == k:
        print(pid)
    rank += 1
