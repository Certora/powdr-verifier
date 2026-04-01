import dataclasses
import html
from pathlib import Path
from typing import Optional

from IPython.display import HTML, display

from .action import Action
from ..utils.io import load_json


def _title_attr(s: str) -> str:
    return f' title="{html.escape(s, quote=True)}"'


@dataclasses.dataclass
class TreeNode:
    name: str
    inputs: list = dataclasses.field(default_factory=list)
    running_time: Optional[float] = None   # seconds
    result: str = "unknown"
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
               width: 100%; font-family: sans-serif; font-size: 13px;
               table-layout: fixed; color: #555; }}
  .ttt-nested {{ width: 100%; border-collapse: collapse; table-layout: fixed; }}
  .ttt-hcell {{ background: #343a40; color: white !important; text-align: left; }}
  .ttt-row   {{ border-bottom: 1px solid #dee2e6; }}
  .ttt-cell  {{ overflow: hidden; text-overflow: ellipsis;
               white-space: nowrap; vertical-align: middle;
               text-align: left; }}
  .ttt-n     {{ width: 25%; }}
  .ttt-i     {{ width: 50%; }}
  .ttt-t     {{ width: 10%; text-align: right;
               font-variant-numeric: tabular-nums; }}
  .ttt-s     {{ width: 15%; }}
  .ttt-badge {{ border-radius: 10px; padding: 1px 8px; font-size: 0.82em;
               border: 1px solid; white-space: nowrap; }}
  .ttt-btn   {{ background: none; border: none; font-size: 10px;
               padding: 0; line-height: 1;
               vertical-align: middle; }}
  .ttt-spc   {{ display: inline-block; width: 20px; flex-shrink: 0; }}
  .ttt-nesttd {{ padding: 0 !important; border: none !important; vertical-align: top; }}
</style>
<table class="ttt-wrap">
  <colgroup>
    <col class="ttt-n"><col class="ttt-i"><col class="ttt-t"><col class="ttt-s">
  </colgroup>
  <thead>
    <tr>
      <th class="ttt-hcell ttt-n">Name</th>
      <th class="ttt-hcell ttt-i">Inputs</th>
      <th class="ttt-hcell ttt-t">Time</th>
      <th class="ttt-hcell ttt-s">Status</th>
    </tr>
  </thead>
  <tbody>
{rows}
  </tbody>
</table>
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
        time_str   = f"{node.running_time:.2f}s" if node.running_time is not None else "—"
        status_str = f"{icon} {node.result}"

        row = (
            f'<tr class="ttt-row" style="background:{row_bg}">'
            f'  <td class="ttt-cell ttt-n" style="background:{row_bg}"{_title_attr(node.name)}>'
            f'    {indent}{toggle}'
            f'    <code style="font-size:0.9em">{node.name}</code>'
            f'  </td>'
            f'  <td class="ttt-cell ttt-i" style="background:{row_bg}"{_title_attr(inputs_str)}>{inputs_str}</td>'
            f'  <td class="ttt-cell ttt-t" style="background:{row_bg}"{_title_attr(time_str)}>{time_str}</td>'
            f'  <td class="ttt-cell ttt-s" style="background:{row_bg}"{_title_attr(status_str)}>'
            f'    <span class="ttt-badge" style="background:{bg};color:{fg};border-color:{fg}88">'
            f'      {icon} {node.result}'
            f'    </span>'
            f'  </td>'
            f'</tr>'
        )

        if has_children:
            hidden = 'style="display:none"' if self._collapsed else ''
            children = "\n".join(
                self._render_node(c, depth + 1, alt=not alt)
                for c in node.children
            )
            row += (
                f'<tr id="{node_id}" {hidden}><td colspan="4" class="ttt-nesttd">'
                f'<table class="ttt-nested"><colgroup>'
                f'<col class="ttt-n"><col class="ttt-i"><col class="ttt-t"><col class="ttt-s">'
                f'</colgroup><tbody>{children}</tbody></table>'
                f'</td></tr>'
            )

        return row

def to_tree_node(data: Action, inputdir: Path) -> TreeNode:
    result = ""
    status = "unknown"
    if s := data.status():
        result = s[0]
        status = {
            True: "success",
            False: "error",
            None: "unknown",
        }[s[1]]
    return TreeNode(
        name=data.name,
        inputs=[
            i.relative_to(inputdir, walk_up=True) for i in data.properties.get("inputs", [])
        ],
        running_time=data.running_time,
        result=result,
        status=status,
        children=[to_tree_node(c, inputdir) for c in data.actions]
    )

def collect(basedir: Path):
    inputdir = (Path(__file__).parent.parent.parent.parent / "data" / basedir.name).resolve()
    data = []
    for file in sorted(basedir.glob("**/*.json")):
        data.append(load_json(file))

    return TreeTableWidget([to_tree_node(d, inputdir) for d in data])
