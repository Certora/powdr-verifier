import json
import subprocess

from .utils import ARGS, load_json, add_base_dump

def diff():
    before = load_json(ARGS().input_before, 'before')
    before = add_base_dump(before)
    after = load_json(ARGS().input_after, 'after')
    after = add_base_dump(after)

    before_formatted = ARGS().input_before.with_suffix('.formatted.json')
    after_formatted = ARGS().input_after.with_suffix('.formatted.json')

    with open(before_formatted, 'w') as f:
        json.dump(before, f, indent=4)
    
    with open(after_formatted, 'w') as f:
        json.dump(after, f, indent=4)

    subprocess.run(['meld',  before_formatted, after_formatted])
