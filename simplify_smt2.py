#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path

def eval(m) -> str:
    match m.group(1):
        case "=":
            return "true" if int(m.group(2)) == int(m.group(3)) else "false"
        case "<":
            return "true" if int(m.group(2)) < int(m.group(3)) else "false"
        case "<=":
            return "true" if int(m.group(2)) <= int(m.group(3)) else "false"
        case "+":
            return str(int(m.group(2)) + int(m.group(3)))
        case "-":
            return str(int(m.group(2)) - int(m.group(3)))
        case "*":
            return str(int(m.group(2)) * int(m.group(3)))
        case "mod":
            return str(int(m.group(2)) % int(m.group(3)))
        case _:
            assert False, f"Unknown operator: {m.group(1)}"

ID = "[a-zA-Z0-9_@-]+"
NUM = "[0-9-]+"

SIMP_SUBS = {
    fr"\(declare-fun {NUM} \(\) Int\)\n": "",
    r"\(declare-fun (true|false) \(\) Bool\)\n": "",

    r"\(and(\s+true)+\s*\)": "true",
    r"\(or(\s+false)*\s+true(\s+false)*\s*\)": "true",

    r"\(not true\)": "false",
    r"\(not false\)": "true",
    fr"\(=\s+(?P<x>{ID})\s+(?P=x)\s*\)": "true",

    fr"\((=)\s+({NUM})\s+({NUM})\s*\)": eval,
    fr"\((<)\s+({NUM})\s+({NUM})\s*\)": eval,
    fr"\((<=)\s+({NUM})\s+({NUM})\s*\)": eval,
    fr"\((\+)\s+({NUM})\s+({NUM})\s*\)": eval,
    fr"\((\-)\s+({NUM})\s+({NUM})\s*\)": eval,
    fr"\((\*)\s+({NUM})\s+({NUM})\s*\)": eval,

    fr"\((mod)\s+({NUM})\s+({NUM})\s*\)": eval,
    
    fr"\(ite\s+false\s+({ID})\s+({ID})\s*\)": r"\2",
    fr"\(ite\s+true\s+({ID})\s+({ID})\s*\)": r"\1",

#    fr"\({ID} Int\)\n\s+": "",
#    fr"\({ID} Bool\)\n\s+": "",
    fr"\(-?[0-9]+ Int\)\n\s+": "",
    fr"\(true Bool\)\n\s+": "",
    fr"\(false Bool\)\n\s+": "",
}

FIX_NEG = {
    r"(\s+)-([0-9]+)": r"\1(- \2)"
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input_path")
    ap.add_argument("model_path")
    ap.add_argument("output_path")
    args = ap.parse_args()
    text = Path(args.input_path).read_text(encoding="utf-8")
    model = json.loads(Path(args.model_path).read_text(encoding="utf-8"))
    for pat, rep in model.items():
        if rep is True:
            rep = "true"
        elif rep is False:
            rep = "false"
        else:
            rep = str(rep)
        text = re.sub(pat, rep, text)
    while True:
        print("simp loop")
        last = text
        for pat, rep in SIMP_SUBS.items():
            text = re.sub(pat, rep, text)
        if text == last:
            break
    for pat, rep in FIX_NEG.items():
        text = re.sub(pat, rep, text)
    Path(args.output_path).write_text(text, encoding="utf-8")

if __name__ == "__main__":
    main()
