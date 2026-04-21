import dataclasses
import html
import tempfile
import webbrowser
from pathlib import Path
from typing import Optional

from .database import (
    clear_verification_steps,
    close_db,
    commit_db,
    connect_db,
    create_db,
    insert_substeps,
    insert_verification_row,
)
from .plots import (
    basic_stats,
    block_solved_percentage_ecdf,
    cactus_time_blocks,
    pass_solved_percentage_ecdf,
    scatter_time_size_by_outcome,
    scatter_time_size_success_only,
    substeps_stacked_lines,
    verified_over_time,
)
from .action import Action
from ..utils.args import ARGS
from ..utils.io import load_json
from ..utils.inputs import load_files_by_block, load_verification_steps


def _title_attr(s: str) -> str:
    return f' title="{html.escape(s, quote=True)}"'


def report_data_dir(report_dir: Path) -> Path:
    return (Path(__file__).parent.parent.parent.parent / "data" / report_dir.name).resolve()


@dataclasses.dataclass
class TreeNode:
    name: str
    inputs: list = dataclasses.field(default_factory=list)
    running_time: Optional[float] = None   # seconds
    result: str = "unknown"
    status: str = "pending"                # pending | running | success | error | skipped
    children: list = dataclasses.field(default_factory=list)
    block: Optional[int] = None
    passname: Optional[str] = None

class TreeTableWidget:
    _STATUS = {
        "success": ("✓", "#155724", "#d4edda"),
        "running":  ("↻", "#004085", "#cce5ff"),
        "error":    ("✗", "#721c24", "#f8d7da"),
        "pending":  ("·", "#6c757d", "#f8f9fa"),
        "skipped":  ("–", "#856404", "#fff3cd"),
    }

    def __init__(self, roots: list[TreeNode], *, collapsed: bool = False, basedir: Path):
        self._roots = roots
        self._collapsed = collapsed
        self._basedir = basedir

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

        if node.inputs:
            inputs = [i.relative_to(self._basedir, walk_up=True) for i in node.inputs]
            inputs_str = ", ".join(str(i).removeprefix("apc_candidate_") for i in inputs)
        else:
            inputs_str = "—"
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


def _substep_label(node: TreeNode) -> str:
    if not node.name == "check":
        return node.name
    blob = " ".join(str(p) for p in node.inputs).lower()
    if "soundness" in blob:
        return f"{node.name} (soundness)"
    if "completeness" in blob:
        return f"{node.name} (completeness)"
    return node.name


def collect_substeps(node: TreeNode) -> list[tuple[str, float | None, str | None]]:
    out: list[tuple[str, float | None, str | None]] = []
    for c in node.children:
        st = c.status
        out.append((_substep_label(c), c.running_time, str(st) if st is not None else None))
    return out


def to_tree_node(data: Action) -> TreeNode:
    return TreeNode(
        name=data.name,
        inputs=data.properties.get("inputs", []),
        running_time=data.running_time,
        result=data.properties.get("result", "unknown"),
        status=data.status(),
        children=[to_tree_node(c) for c in data.actions]
    )

def collect(basedir: Path):
    inputdir = report_data_dir(basedir)
    data = []
    for file in sorted(basedir.glob("**/*.json")):
        try:
            res = load_json(file)
            data.append(res)
        except Exception as e:
            continue

    ttw = TreeTableWidget([to_tree_node(d) for d in data], basedir=inputdir)
    results = load_verification_steps(inputdir)
    for node in ttw._roots:
        if node.name == "verify":
            assert len(node.inputs) == 2
            i1, i2 = node.inputs
            assert (i1, i2) in results
            node.block, node.passname = results[(i1, i2)]
            results[(i1, i2)] = node
            step_id = insert_verification_row(i1, i2, node)
            insert_substeps(step_id, collect_substeps(node))
    for (i1, i2), val in results.items():
        if isinstance(val, tuple):
            insert_verification_row(i1, i2, val)
    commit_db()
    return ttw, results

def report():
    report_dir = ARGS().report_dir
    connect_db(report_dir / "verification_results.db")
    try:
        create_db()
        clear_verification_steps()
        table, _ = collect(report_dir)
        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Report</title>
</head>
<body>
{basic_stats()}

{verified_over_time()}

{cactus_time_blocks()}

{block_solved_percentage_ecdf()}

{pass_solved_percentage_ecdf()}

{scatter_time_size_success_only()}

{scatter_time_size_by_outcome()}

{substeps_stacked_lines(report_data_dir(report_dir))}

<!--{table._render()}-->
</body>
</html>
"""
        ARGS().output.write_text(html, encoding="utf-8")
    finally:
        close_db()
    #webbrowser.open(ARGS().output.resolve().as_uri())
