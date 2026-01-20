import logging
import json
from pathlib import Path
from typing import Any

from .args import ARGS

def load_json(file: Path, label: str) -> Any:
    """Load a json file and return the data. Use label for logging."""
    with open(file, 'r') as f:
        data = json.load(f)
    if ARGS().log_json:
        logging.info(f'{label}:\n{json.dumps(data, indent=2)}')
    return data

def load_apc_dump(file: Path, label: str) -> Any:
    """
    Load an apc dump and return the data. Use label for logging.
    If the json is just the machine and not the whole apc dump,
    take the apc from the base dump and only update the machine.
    """
    data = load_json(file, label)
    if 'block' not in data:
        if ARGS().base_dump is not None:
            base_data = load_json(ARGS().base_dump, 'base_dump')
            assert 'block' in base_data, 'no block found in base dump'
            data = base_data |  { 'machine': data }
            logging.info(f'took block from {ARGS().base_dump}')
        else:
            logging.error('no block found and no base dump provided')
    return data
