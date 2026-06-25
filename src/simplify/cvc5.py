"""External ``cvc5`` subprocess preprocessing hook for SMT-LIB scripts (debug/experiment)."""
import subprocess
import logging
from pathlib import Path
from .utils import convert_script_to_string
from ..utils.stats import stats_dump

CVC5_BIN = Path("~/stuff/cvc5/build/bin/cvc5").expanduser()

def _extract_script(output: str) -> str | None:
    """Slice cvc5 stdout between ``assertions::pre-theory-preprocess`` trace markers."""
    start_tag = ";; post-asserts start"
    end_tag = ";; post-asserts end"
    start_tag = ";; assertions::pre-theory-preprocess start"
    end_tag = ";; assertions::pre-theory-preprocess end"
    start = output.find(start_tag)
    end = output.find(end_tag)
    if start < 0 or end < 0 or end <= start:
        return None
    return output[start + len(start_tag) : end].strip()

@convert_script_to_string
def simplify_cvc5(smt: str, subaction=None) -> str:
    """Roundtrip through external solver preprocessing."""

    if not CVC5_BIN.exists():
        stats_dump("cvc5", {"applied": False, "skip": "no_cvc5_binary"})
        return None

    proc = subprocess.run(
        #["cvc5", "--dag-thresh", "0", "--preprocess-only", "-o", "post-asserts", "--no-interactive"],
        ["/home/gereon/stuff/cvc5/build/bin/cvc5", "--incremental", "--arrays-exp", "--dag-thresh", "0", "--preprocess-only", "-t", "assertions::pre-theory-preprocess", "--no-interactive"],
        input=smt,
        capture_output=True,
        text=True,
        check=False,
    )

    if proc.returncode != 0:
        logging.warning(
            "external solver pass skipped: cvc5 returned non-zero exit code %s",
            proc.returncode,
        )
        logging.warning(proc.stdout)
        logging.warning(proc.stderr)
        stats_dump(
            "cvc5",
            {
                "applied": False,
                "skip": "cvc5_nonzero",
                "returncode": proc.returncode,
            },
        )
        return None

    post_asserts = _extract_script(proc.stdout)
    if post_asserts is None:
        logging.warning(
            "external solver pass skipped: could not find post-asserts block in cvc5 output"
        )
        stats_dump("cvc5", {"applied": False, "skip": "no_post_asserts_block"})
        return None

    stats_dump(
        "cvc5",
        {
            "applied": True,
            "bytes_in": len(smt),
            "bytes_out": len(post_asserts),
        },
    )
    return post_asserts
