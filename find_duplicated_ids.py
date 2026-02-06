#!/usr/bin/env python3

# Look through the trace-*.smt2 files and look for variables with the same ids.
# I saw them at some point, but it might have been due to mismatched programs.
# This script acts as a sanity check to look for cases where powdr would reuse
# variable ids. It seems it doesn't, but just in case...

import argparse
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument('basedir', type=Path)
args = parser.parse_args()

r = re.compile("\\(declare-fun (.*)@([0-9]+) ")

for test in args.basedir.glob("*"):
    print(f'looking for duplicates in {test}...')
    matches = {}
    for file in test.glob("trace*.smt2"):
        with open(file, 'r') as f:
            for m in r.finditer(f.read()):
                name,id = m.groups()
                if matches.setdefault(id, name) != name:
                    print(f"found collision for @{id}: {matches[id]} vs {name}")
