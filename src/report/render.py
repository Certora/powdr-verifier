import dataclasses
import json
from pathlib import Path
from typing import Optional

from IPython.display import HTML, display

@dataclasses.dataclass
class TreeNode:
    name: str
    inputs: list = dataclasses.field(default_factory=list)
    running_time: Optional[float] = None   # seconds
    status: str = "pending"                # pending | running | success | error | skipped
    children: list = dataclasses.field(default_factory=list)


class TreeTableWidget:
    _STATUS = {
        "success": ("✓", "#155724", "#d4edda"),
        "running":  ("↻", "#004085", "#cce5ff"),
        "error":    ("✗", "#721c24", "#f8d7da"),
        "pending":  ("·", "#6c757d", "#f8f9fa"),
        "skipped":  ("–", "#856404", "#fff3cd"),
    }

    def __init__(self, roots: list[TreeNode], *, collapsed: bool = False):
        self._roots = roots
        self._collapsed = collapsed

    def display(self):
        display(HTML(self._render()))

    def _render(self) -> str:
        rows = "\n".join(self._render_node(n, depth=0, alt=i % 2 == 1)
                         for i, n in enumerate(self._roots))
        return f"""
<style>
  .ttt-wrap  {{ border: 1px solid #dee2e6; border-radius: 4px; overflow: hidden;
               width: fit-content; font-family: sans-serif; font-size: 13px; }}
  .ttt-head  {{ display: flex; }}
  .ttt-hcell {{ background: #343a40; color: white !important; padding: 7px 10px;
               font-weight: 600; white-space: nowrap; box-sizing: border-box; }}
  .ttt-row   {{ display: flex; align-items: stretch;
               border-bottom: 1px solid #dee2e6; box-sizing: border-box; }}
  .ttt-cell  {{ padding: 5px 10px; display: flex; align-items: center;
               overflow: hidden; text-overflow: ellipsis; white-space: nowrap;
               box-sizing: border-box; }}
  .ttt-n     {{ width: 280px; }}
  .ttt-i     {{ width: 260px; font-size: 0.85em; color: #555; }}
  .ttt-t     {{ width: 90px;  justify-content: flex-end;
               font-variant-numeric: tabular-nums; color: #555; }}
  .ttt-s     {{ width: 110px; }}
  .ttt-badge {{ border-radius: 10px; padding: 1px 8px; font-size: 0.82em;
               border: 1px solid; white-space: nowrap; }}
  .ttt-btn   {{ background: none; border: none; cursor: pointer; font-size: 10px;
               width: 20px; flex-shrink: 0; padding: 0; line-height: 1; }}
  .ttt-spc   {{ display: inline-block; width: 20px; flex-shrink: 0; }}
</style>
<div class="ttt-wrap">
  <div class="ttt-head">
    <div class="ttt-hcell ttt-n">Name</div>
    <div class="ttt-hcell ttt-i">Inputs</div>
    <div class="ttt-hcell ttt-t">Time</div>
    <div class="ttt-hcell ttt-s">Status</div>
  </div>
  {rows}
</div>
"""

    def _render_node(self, node: TreeNode, depth: int, alt: bool = False) -> str:
        icon, fg, bg = self._STATUS.get(node.status, self._STATUS["pending"])
        row_bg = bg if node.status != "pending" else ("#f8f9fa" if alt else "white")
        has_children = bool(node.children)
        node_id = f"ttt_{id(node)}"

        indent = f'<span style="display:inline-block;width:{depth * 20}px;flex-shrink:0"></span>'
        if has_children:
            arrow = "▶" if self._collapsed else "▼"
            js = (
                f"(function(b){{"
                f"var e=document.getElementById('{node_id}');"
                f"var h=e.style.display==='none';"
                f"e.style.display=h?'':'none';"
                f"b.textContent=h?'\\u25bc':'\\u25b6';"
                f"}})(this)"
            )
            toggle = f'<button class="ttt-btn" onclick="{js}">{arrow}</button>'
        else:
            toggle = '<span class="ttt-spc"></span>'

        inputs_str = ", ".join(str(i) for i in node.inputs) if node.inputs else "—"
        time_str   = f"{node.running_time:.3f}s" if node.running_time is not None else "—"

        row = (
            f'<div class="ttt-row" style="background:{row_bg}">'
            f'  <div class="ttt-cell ttt-n" style="background:{row_bg}">'
            f'    {indent}{toggle}'
            f'    <code style="font-size:0.9em">{node.name}</code>'
            f'  </div>'
            f'  <div class="ttt-cell ttt-i" style="background:{row_bg}">{inputs_str}</div>'
            f'  <div class="ttt-cell ttt-t" style="background:{row_bg}">{time_str}</div>'
            f'  <div class="ttt-cell ttt-s" style="background:{row_bg}">'
            f'    <span class="ttt-badge" style="background:{bg};color:{fg};border-color:{fg}88">'
            f'      {icon} {node.status}'
            f'    </span>'
            f'  </div>'
            f'</div>'
        )

        if has_children:
            hidden = 'style="display:none"' if self._collapsed else ''
            children = "\n".join(
                self._render_node(c, depth + 1, alt=not alt)
                for c in node.children
            )
            row += f'<div id="{node_id}" {hidden}>{children}</div>'

        return row

def to_tree_node(data: dict) -> TreeNode:
    return TreeNode(
        name=data["name"],
        inputs=data.get("inputs", []),
        running_time=data["running_time"],
        status=data.get("status", ""),
        children=[to_tree_node(c) for c in data["actions"]]
    )

def collect(basedir: Path):
    data = []
    for file in basedir.glob("**/*.json"):
        with open(file, "r") as f:
            data.append(json.load(f))
    
    data.sort(key=lambda x: (x["test"], x["inputs"]))

    return TreeTableWidget([to_tree_node(d) for d in data])
