#!/usr/bin/env python3
import argparse
import re
from pathlib import Path

VAR_SUBS = {
    "after-a__0_0@19": 2,
    "after-b__0_0@23": 5,
    "after-b__1_0@24": 255,
    "after-b__2_0@25": 4,
    "after-b__3_0@26": 0,
    "after-cmp_result_1@54": 1,
    "after-free_var_64@64": 1006632961,
    "after-from_state__timestamp_0@1": 536739841,
    "after-memory-0-data0-2": 5,
    "after-memory-0-data0-new": 0,
    "after-memory-0-data1-2": 255,
    "after-memory-0-data1-new": 0,
    "after-memory-0-data2-2": 4,
    "after-memory-0-data2-new": 0,
    "after-memory-0-data3-2": 0,
    "after-memory-0-data3-new": 0,
    "after-memory-0-data4-2": 0,
    "after-memory-0-data4-new": 0,
    "after-memory-0-hadinput-2": "false",
    "after-memory-0-hadinput-new": "true",
    "after-memory-0-isinput": "true",
    "after-memory-0-mult-2": 1,
    "after-memory-0-mult-new": 0,
    "after-memory-1-data0-2": 0,
    "after-memory-1-data0-new": 5,
    "after-memory-1-data1-2": 0,
    "after-memory-1-data1-new": 255,
    "after-memory-1-data2-2": 0,
    "after-memory-1-data2-new": 4,
    "after-memory-1-data3-2": 0,
    "after-memory-1-data3-new": 0,
    "after-memory-1-data4-2": 0,
    "after-memory-1-data4-new": 536739841,
    "after-memory-1-hadinput-2": "true",
    "after-memory-1-hadinput-new": "true",
    "after-memory-1-isinput": "false",
    "after-memory-1-mult-2": 0,
    "after-memory-1-mult-new": 1,
    "after-memory-2-data0-2": 255,
    "after-memory-2-data0-new": 0,
    "after-memory-2-data1-2": 255,
    "after-memory-2-data1-new": 0,
    "after-memory-2-data2-2": 255,
    "after-memory-2-data2-new": 0,
    "after-memory-2-data3-2": 255,
    "after-memory-2-data3-new": 0,
    "after-memory-2-data4-2": 2013134852,
    "after-memory-2-data4-new": 0,
    "after-memory-2-hadinput-2": "false",
    "after-memory-2-hadinput-new": "true",
    "after-memory-2-isinput": "true",
    "after-memory-2-mult-2": 1,
    "after-memory-2-mult-new": 0,
    "after-memory-3-data0-2": 0,
    "after-memory-3-data0-new": 2,
    "after-memory-3-data1-2": 0,
    "after-memory-3-data1-new": 0,
    "after-memory-3-data2-2": 0,
    "after-memory-3-data2-new": 0,
    "after-memory-3-data3-2": 0,
    "after-memory-3-data3-new": 0,
    "after-memory-3-data4-2": 0,
    "after-memory-3-data4-new": 536739844,
    "after-memory-3-hadinput-2": "true",
    "after-memory-3-hadinput-new": "true",
    "after-memory-3-isinput": "false",
    "after-memory-3-mult-2": 0,
    "after-memory-3-mult-new": 1,
    "after-memory-4-data0-2": 0,
    "after-memory-4-data0-new": 0,
    "after-memory-4-data1-2": 0,
    "after-memory-4-data1-new": 0,
    "after-memory-4-data2-2": 0,
    "after-memory-4-data2-new": 0,
    "after-memory-4-data3-2": 0,
    "after-memory-4-data3-new": 0,
    "after-memory-4-data4-2": 2013134854,
    "after-memory-4-data4-new": 0,
    "after-memory-4-hadinput-2": "false",
    "after-memory-4-hadinput-new": "true",
    "after-memory-4-isinput": "true",
    "after-memory-4-mult-2": 1,
    "after-memory-4-mult-new": 0,
    "after-memory-5-data0-2": 0,
    "after-memory-5-data0-new": 0,
    "after-memory-5-data1-2": 0,
    "after-memory-5-data1-new": 0,
    "after-memory-5-data2-2": 0,
    "after-memory-5-data2-new": 0,
    "after-memory-5-data3-2": 0,
    "after-memory-5-data3-new": 0,
    "after-memory-5-data4-2": 0,
    "after-memory-5-data4-new": 536739845,
    "after-memory-5-hadinput-2": "true",
    "after-memory-5-hadinput-new": "true",
    "after-memory-5-isinput": "false",
    "after-memory-5-mult-2": 0,
    "after-memory-5-mult-new": 1,
    "after-reads_aux__0__base__prev_timestamp_0@6": 0,
    "after-reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0@7": 0,
    "after-reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1@41": 0,
    "after-reads_aux__1__base__prev_timestamp_1@43": 2013134854,
    "after-reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_1@44": 131071,
    "after-writes_aux__base__prev_timestamp_0@12": 2013134852,
    "after-writes_aux__base__timestamp_lt_aux__lower_decomp__0_0@13": 131071,
    "after-writes_aux__prev_data__0_0@15": 255,
    "after-writes_aux__prev_data__1_0@16": 255,
    "after-writes_aux__prev_data__2_0@17": 255,
    "after-writes_aux__prev_data__3_0@18": 255,
    "before-a__0_0@19": 2,
    "before-b__0_0@23": 5,
    "before-b__1_0@24": 255,
    "before-b__2_0@25": 4,
    "before-b__3_0@26": 0,
    "before-cmp_result_1@54": 1,
    "before-free_var_64@64": 1006632961,
    "before-from_state__timestamp_0@1": 536739841,
    "before-from_state__timestamp_1@37": 536739844,
    "before-memory-0-data0-2": 5,
    "before-memory-0-data0-new": 0,
    "before-memory-0-data1-2": 255,
    "before-memory-0-data1-new": 0,
    "before-memory-0-data2-2": 4,
    "before-memory-0-data2-new": 0,
    "before-memory-0-data3-2": 0,
    "before-memory-0-data3-new": 0,
    "before-memory-0-data4-2": 0,
    "before-memory-0-data4-new": 0,
    "before-memory-0-hadinput-2": "false",
    "before-memory-0-hadinput-new": "true",
    "before-memory-0-isinput": "true",
    "before-memory-0-mult-2": 1,
    "before-memory-0-mult-new": 0,
    "before-memory-1-data0-2": 0,
    "before-memory-1-data0-new": 5,
    "before-memory-1-data1-2": 0,
    "before-memory-1-data1-new": 255,
    "before-memory-1-data2-2": 0,
    "before-memory-1-data2-new": 4,
    "before-memory-1-data3-2": 0,
    "before-memory-1-data3-new": 0,
    "before-memory-1-data4-2": 0,
    "before-memory-1-data4-new": 536739841,
    "before-memory-1-hadinput-2": "true",
    "before-memory-1-hadinput-new": "true",
    "before-memory-1-isinput": "false",
    "before-memory-1-mult-2": 0,
    "before-memory-1-mult-new": 1,
    "before-memory-2-data0-2": 255,
    "before-memory-2-data0-new": 0,
    "before-memory-2-data1-2": 255,
    "before-memory-2-data1-new": 0,
    "before-memory-2-data2-2": 255,
    "before-memory-2-data2-new": 0,
    "before-memory-2-data3-2": 255,
    "before-memory-2-data3-new": 0,
    "before-memory-2-data4-2": 2013134852,
    "before-memory-2-data4-new": 0,
    "before-memory-2-hadinput-2": "false",
    "before-memory-2-hadinput-new": "true",
    "before-memory-2-isinput": "true",
    "before-memory-2-mult-2": 1,
    "before-memory-2-mult-new": 0,
    "before-memory-3-data0-2": 0,
    "before-memory-3-data0-new": 2,
    "before-memory-3-data1-2": 0,
    "before-memory-3-data1-new": 0,
    "before-memory-3-data2-2": 0,
    "before-memory-3-data2-new": 0,
    "before-memory-3-data3-2": 0,
    "before-memory-3-data3-new": 0,
    "before-memory-3-data4-2": 0,
    "before-memory-3-data4-new": 536739844,
    "before-memory-3-hadinput-2": "true",
    "before-memory-3-hadinput-new": "true",
    "before-memory-3-isinput": "false",
    "before-memory-3-mult-2": 0,
    "before-memory-3-mult-new": 1,
    "before-memory-4-data0-2": 0,
    "before-memory-4-data0-new": 0,
    "before-memory-4-data1-2": 0,
    "before-memory-4-data1-new": 0,
    "before-memory-4-data2-2": 0,
    "before-memory-4-data2-new": 0,
    "before-memory-4-data3-2": 0,
    "before-memory-4-data3-new": 0,
    "before-memory-4-data4-2": 2013134854,
    "before-memory-4-data4-new": 0,
    "before-memory-4-hadinput-2": "false",
    "before-memory-4-hadinput-new": "true",
    "before-memory-4-isinput": "true",
    "before-memory-4-mult-2": 1,
    "before-memory-4-mult-new": 0,
    "before-memory-5-data0-2": 0,
    "before-memory-5-data0-new": 0,
    "before-memory-5-data1-2": 0,
    "before-memory-5-data1-new": 0,
    "before-memory-5-data2-2": 0,
    "before-memory-5-data2-new": 0,
    "before-memory-5-data3-2": 0,
    "before-memory-5-data3-new": 0,
    "before-memory-5-data4-2": 0,
    "before-memory-5-data4-new": 536739845,
    "before-memory-5-hadinput-2": "true",
    "before-memory-5-hadinput-new": "true",
    "before-memory-5-isinput": "false",
    "before-memory-5-mult-2": 0,
    "before-memory-5-mult-new": 1,
    "before-reads_aux__0__base__prev_timestamp_0@6": 0,
    "before-reads_aux__0__base__prev_timestamp_1@40": 536739843,
    "before-reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_0@7": 0,
    "before-reads_aux__0__base__timestamp_lt_aux__lower_decomp__0_1@41": 0,
    "before-reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_0@8": 4095,
    "before-reads_aux__0__base__timestamp_lt_aux__lower_decomp__1_1@42": 0,
    "before-reads_aux__1__base__prev_timestamp_1@43": 2013134854,
    "before-reads_aux__1__base__timestamp_lt_aux__lower_decomp__0_1@44": 131071,
    "before-reads_aux__1__base__timestamp_lt_aux__lower_decomp__1_1@45": 4095,
    "before-writes_aux__base__prev_timestamp_0@12": 2013134852,
    "before-writes_aux__base__timestamp_lt_aux__lower_decomp__0_0@13": 131071,
    "before-writes_aux__base__timestamp_lt_aux__lower_decomp__1_0@14": 4095,
    "before-writes_aux__prev_data__0_0@15": 255,
    "before-writes_aux__prev_data__1_0@16": 255,
    "before-writes_aux__prev_data__2_0@17": 255,
    "before-writes_aux__prev_data__3_0@18": 255
}

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

    fr"\({ID} Int\)\n\s+": "",
    fr"\({ID} Bool\)\n\s+": "",
}

FIX_NEG = {
    r"(\s+)-([0-9]+)": r"\1(- \2)"
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input_path")
    ap.add_argument("output_path")
    args = ap.parse_args()
    text = Path(args.input_path).read_text(encoding="utf-8")
    for pat, rep in VAR_SUBS.items():
        text = re.sub(pat, str(rep), text)
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
