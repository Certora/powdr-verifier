import subprocess
import logging

from .utils import convert_script_to_string

def _extract_script(output: str) -> str | None:
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
def simplify_cvc5(smt: str) -> str:
    """Roundtrip through external solver preprocessing."""

    proc = subprocess.run(
        #["cvc5", "--dag-thresh", "0", "--preprocess-only", "-o", "post-asserts", "--no-interactive"],
        ["/home/gereon/stuff/cvc5/build/bin/cvc5", "--arrays-exp", "--dag-thresh", "0", "--preprocess-only", "-t", "assertions::pre-theory-preprocess", "--no-interactive"],
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
        if proc.stderr:
            logging.debug(proc.stderr)
        return None

    post_asserts = _extract_script(proc.stdout)
    if post_asserts is None:
        logging.warning(
            "external solver pass skipped: could not find post-asserts block in cvc5 output"
        )
        return None

    return post_asserts
