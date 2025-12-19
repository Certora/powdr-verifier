import logging
from typing import Any
from .utils import iterate_recursive

def collect_variables(data: Any) -> dict[str, Any]:
    id_to_name: dict[int, str] = {}
    name_to_id: dict[str, int] = {}
    for value in iterate_recursive(data):
        match value:
            case {'Reference': { 'name': str(name), 'id': int(id) }}:
                if name in name_to_id and name_to_id[name] != id:
                    logging.error(f"Variable {name} has multiple ids: {name_to_id[name]} and {id}")
                elif id in id_to_name and id_to_name[id] != name:
                    logging.error(f"Variable {id} has multiple names: {id_to_name[id]} and {name}")
                else:
                    name_to_id[name] = id
                    id_to_name[id] = name
            case _:
                pass

    return id_to_name, name_to_id
