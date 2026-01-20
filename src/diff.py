import json
import subprocess

from .utils.args import ARGS
from .utils.io import load_apc_dump

def diff():
    before = load_apc_dump(ARGS().input_before, 'before')
    after = load_apc_dump(ARGS().input_after, 'after')

    before_formatted = ARGS().input_before.with_suffix('.formatted.json')
    after_formatted = ARGS().input_after.with_suffix('.formatted.json')

    with open(before_formatted, 'w') as f:
        json.dump(before, f, indent=4)
    
    with open(after_formatted, 'w') as f:
        json.dump(after, f, indent=4)

    subprocess.run(['meld',  before_formatted, after_formatted])
