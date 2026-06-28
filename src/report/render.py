"""Generate static HTML reports from recorded verification steps in SQLite."""
import dataclasses
import html
import tempfile
import webbrowser
from datetime import datetime, timezone
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
    pass_solved_percentage_ecdf,
    scatter_time_size_by_isqf_and_outcome,
    scatter_time_size_by_outcome,
    scatter_time_size_success_only,
    simplifier_pass_stats_bar,
    substeps_stacked_lines,
    verified_over_time,
)
from .action import Action
from .html_utils import copy_command_badge
from ..paths import DATA_DIR, POWDR_DUMPS_DIR
from ..utils.args import ARGS
from ..utils.io import load_json
from ..utils.inputs import load_files_by_block, load_verification_steps


def _title_attr(s: str) -> str:
    return f' title="{html.escape(s, quote=True)}"'


def report_data_dir(report_dir: Path) -> Path:
    return (DATA_DIR / report_dir.name).resolve()


def _format_duration(seconds: float) -> str:
    if seconds < 60:
        return f"{seconds:.1f}s"
    if seconds < 3600:
        m, s = divmod(seconds, 60)
        return f"{int(m)}m {s:.0f}s"
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    return f"{int(h)}h {int(m)}m {s:.0f}s"


def _format_job_timestamp(iso: str) -> str:
    try:
        dt = datetime.fromisoformat(iso)
    except ValueError:
        return iso
    if dt.tzinfo is not None:
        dt = dt.astimezone(timezone.utc).replace(tzinfo=None)
        return dt.strftime("%Y-%m-%d %H:%M:%S UTC")
    return dt.strftime("%Y-%m-%d %H:%M:%S")


def job_banner(report_dir: Path) -> str:
    job_file = report_dir / "job.json"
    if not job_file.is_file():
        return ""
    job = load_json(job_file)
    command = html.escape(str(job.get("command", "")))
    test = html.escape(str(job.get("test", "")))
    started = _format_job_timestamp(str(job.get("started_at", "")))
    running_time = job.get("running_time")
    duration = _format_duration(float(running_time)) if running_time is not None else "—"
    command_line = job.get("command_line")
    cmd_html = (
        f'<code class="text-break user-select-all flex-grow-1 min-width-0" style="font-size:0.82em">'
        f"{html.escape(command_line)}</code>"
        if command_line
        else '<span class="text-body-secondary">—</span>'
    )
    timing = (
        f'<span class="fw-semibold">{html.escape(duration)}</span>'
        f'<span class="text-body-secondary"> @ {html.escape(started)}</span>'
    )
    copy_badge = copy_command_badge(command_line)
    return f"""
<section class="container-fluid py-2 pb-0">
  <div class="card shadow-sm">
    <div class="card-body py-2 px-3">
      <div class="d-flex align-items-center justify-content-between gap-3 mb-1" style="font-size:0.9em">
        <span class="fw-semibold"><code>{command}</code> <code>{test}</code></span>
        <span class="text-end text-nowrap">{timing}</span>
      </div>
      <div class="d-flex align-items-center gap-2 min-width-0">
        {cmd_html}
        {copy_badge}
      </div>
    </div>
  </div>
</section>
"""


@dataclasses.dataclass
class TreeNode:
    name: str
    inputs: list = dataclasses.field(default_factory=list)
    running_time: Optional[float] = None   # seconds
    result: Optional[str] = None
    expected: Optional[str] = None
    error_message: Optional[str] = None
    status: str = "pending"                # pending | running | success | error | memout | skipped
    children: list = dataclasses.field(default_factory=list)
    block: Optional[int] = None
    passname: Optional[str] = None
    command_line: Optional[str] = None

class TreeTableWidget:
    _STATUS = {
        "success": ("✓", "#155724", "#d4edda"),
        "running":  ("↻", "#004085", "#cce5ff"),
        "wrong":    ("≠", "#856404", "#fff3cd"),
        "timeout":  ("⏱", "#856404", "#ffeeba"),
        "memout":   ("M", "#9a3412", "#ffedd5"),
        "unknown":  ("?", "#664d03", "#fff3cd"),
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
  .ttt-n     {{ width: 18%; }}
  .ttt-i     {{ width: 28%; }}
  .ttt-t     {{ width: 8%; text-align: right;
               font-variant-numeric: tabular-nums; }}
  .ttt-s     {{ width: 12%; }}
  .ttt-c     {{ width: 34%; font-family: monospace; font-size: 0.78em; }}
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
    <col class="ttt-n"><col class="ttt-i"><col class="ttt-t"><col class="ttt-s"><col class="ttt-c">
  </colgroup>
  <thead>
    <tr>
      <th class="ttt-hcell ttt-n">Name</th>
      <th class="ttt-hcell ttt-i">Inputs</th>
      <th class="ttt-hcell ttt-t">Time</th>
      <th class="ttt-hcell ttt-s">Status</th>
      <th class="ttt-hcell ttt-c">Command</th>
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
        shown_result = node.result if node.result is not None else node.status
        status_str = f"{icon} {shown_result}"
        if node.error_message:
            status_str = f"{status_str} — {node.error_message}"

        if node.command_line:
            cmd_esc = html.escape(node.command_line)
            cmd_cell = (
                f'<span{_title_attr(node.command_line)}>{cmd_esc}</span>'
                f' {copy_command_badge(node.command_line)}'
            )
        else:
            cmd_cell = "—"

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
            f'      {icon} {shown_result}'
            f'    </span>'
            f'  </td>'
            f'  <td class="ttt-cell ttt-c" style="background:{row_bg}">{cmd_cell}</td>'
            f'</tr>'
        )

        if has_children:
            hidden = 'style="display:none"' if self._collapsed else ''
            children = "\n".join(
                self._render_node(c, depth + 1, alt=not alt)
                for c in node.children
            )
            row += (
                f'<tr id="{node_id}" {hidden}><td colspan="5" class="ttt-nesttd">'
                f'<table class="ttt-nested"><colgroup>'
                f'<col class="ttt-n"><col class="ttt-i"><col class="ttt-t"><col class="ttt-s"><col class="ttt-c">'
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


def normalize_substep_tree(node: TreeNode) -> TreeNode:
    return TreeNode(
        name=_substep_label(node),
        inputs=node.inputs,
        running_time=node.running_time,
        result=node.result,
        expected=node.expected,
        error_message=node.error_message,
        status=node.status,
        children=[normalize_substep_tree(child) for child in node.children],
        block=node.block,
        passname=node.passname,
        command_line=node.command_line,
    )


def to_tree_node(data: Action) -> TreeNode:
    return TreeNode(
        name=data.name,
        inputs=data.properties.get("inputs", []),
        running_time=data.running_time,
        result=data.properties.get("result"),
        expected=data.properties.get("expected"),
        error_message=data.properties.get("error_message"),
        status=data.status(),
        children=[to_tree_node(c) for c in data.actions],
        command_line=data.properties.get("command_line"),
    )

def collect(basedir: Path):
    inputdir = (POWDR_DUMPS_DIR / basedir.name).resolve()
    data = []
    for file in sorted(basedir.glob("**/*.json")):
        if file.name == "job.json":
            continue
        try:
            res = load_json(file)
            if not isinstance(res, Action):
                continue
            data.append(res)
        except Exception as e:
            continue

    ttw = TreeTableWidget([to_tree_node(d) for d in data], basedir=inputdir)
    results = load_verification_steps(inputdir)
    for node in ttw._roots:
        if node.name == "verify":
            assert len(node.inputs) == 2
            i1, i2 = node.inputs
            assert (i1, i2) in results, f"Verification step not found for inputs {i1} and {i2}"
            node.block, node.passname = results[(i1, i2)]
            results[(i1, i2)] = node
            step_id = insert_verification_row(i1, i2, node)
            insert_substeps(step_id, [normalize_substep_tree(child) for child in node.children])
    for (i1, i2), val in results.items():
        if isinstance(val, tuple):
            insert_verification_row(i1, i2, val)
    commit_db()
    return ttw, results

def report_db_path(output: Path) -> Path:
    return output.with_suffix(".db")


def report():
    report_dir = ARGS().report_dir
    output = ARGS().output
    connect_db(report_db_path(output))
    try:
        create_db()
        clear_verification_steps()
        collect(report_dir)
        html = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Report</title>
<link href="https://cdn.jsdelivr.net/npm/bootstrap@latest/dist/css/bootstrap.min.css" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/plotly.js-dist-min@latest/plotly.min.js"></script>
</head>
<body>
{job_banner(report_dir)}

{basic_stats()}

{block_solved_percentage_ecdf()}

{verified_over_time()}

{substeps_stacked_lines(report_data_dir(report_dir))}

{pass_solved_percentage_ecdf()}

{scatter_time_size_success_only(report_data_dir(report_dir))}

{scatter_time_size_by_outcome(report_data_dir(report_dir))}

{scatter_time_size_by_isqf_and_outcome(report_data_dir(report_dir))}

{simplifier_pass_stats_bar()}
</body>
</html>
"""
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(html, encoding="utf-8")
    finally:
        close_db()
    #webbrowser.open(ARGS().output.resolve().as_uri())
