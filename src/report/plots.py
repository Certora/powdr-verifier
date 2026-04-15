import functools
from pathlib import Path
from typing import Iterable
import pandas
import plotly.express
import re

from .database import query, query_single_value

RE_FILENAME = re.compile(r"^.*/apc_candidate_(\d+)_(\d+)(?:_(.*))?\.json$")
def parse_filename(filename: str) -> tuple[int, int, str]:
    m = RE_FILENAME.match(filename)
    assert m, f"Invalid filename: {filename}"
    return int(m.group(1)), int(m.group(2)), m.group(3) or ""

def list_verifications(data) -> Iterable:
    for d in data._roots:
        if d.name == "verify":
            yield d

def list_passes(data) -> Iterable:
    for v in list_verifications(data):
        assert len(v.inputs) == 2
        _,_,name = parse_filename(str(v.inputs[1]))
        yield name, v

def basic_stats() -> str:
    n_blocks = query_single_value(
        "SELECT COUNT(DISTINCT block) FROM verification_steps WHERE block IS NOT NULL"
    )
    n_steps = query_single_value("SELECT COUNT(*) FROM verification_steps")
    n_passes = query_single_value(
        "SELECT COUNT(DISTINCT passname) FROM verification_steps "
        "WHERE passname IS NOT NULL AND passname != ''"
    )
    return f"""
<dl>
<dt>#blocks</dt>
<dd>{n_blocks}</dd>
<dt>#verification steps</dt>
<dd>{n_steps}</dd>
<dt>#passes</dt>
<dd>{n_passes}</dd>
</dl>

"""

def verified_over_time() -> str:
    rows = query(
        "SELECT running_time FROM verification_steps WHERE status = 'success'"
    )
    d = [{"id": i, "time": row[0]} for i, row in enumerate(rows)]
    df = pandas.DataFrame(d, columns=["id", "time"])
    fig = plotly.express.ecdf(
        df,
        y="time",
        title="Verifies solved",
        ecdfnorm=None,
        orientation="h",
        labels={"count": "# verifies", "time": "Time (s)"},
    )

    return fig.to_html(full_html=False)

@functools.lru_cache(maxsize=1)
def _scatter_time_size_frame() -> pandas.DataFrame:
    rows = query(
        "SELECT input1, input2, running_time, status FROM verification_steps "
        "WHERE running_time IS NOT NULL"
    )
    rec = []
    for input1, input2, rt, status in rows:
        try:
            s = Path(input1).stat().st_size + Path(input2).stat().st_size
        except OSError:
            continue
        rec.append(
            {
                "size": s / 1024,
                "time": rt,
                "outcome": "success" if status == "success" else "failed",
            }
        )
    return pandas.DataFrame(rec, columns=["size", "time", "outcome"])


def scatter_time_size_success_only() -> str:
    df = _scatter_time_size_frame()
    df = df[df["outcome"] == "success"]
    if df.empty:
        return ""
    fig = plotly.express.scatter(
        df,
        x="size",
        y="time",
        title="Verification Size vs. Time (success only)",
        labels={"size": "Size (KiB)", "time": "Time (s)"},
        range_x=[0, df["size"].max() * 1.1],
        range_y=[0, df["time"].max() * 1.1],
    )
    return fig.to_html(full_html=False)


def scatter_time_size_by_outcome() -> str:
    df = _scatter_time_size_frame()
    if df.empty:
        return ""
    fig = plotly.express.scatter(
        df,
        x="size",
        y="time",
        color="outcome",
        color_discrete_map={"success": "#636EFA", "failed": "red"},
        title="Verification Size vs. Time (by outcome)",
        labels={"size": "Size (KiB)", "time": "Time (s)", "outcome": "Outcome"},
        range_x=[0, df["size"].max() * 1.1],
        range_y=[0, df["time"].max() * 1.1],
    )
    return fig.to_html(full_html=False)


def cactus_time_blocks() -> str:
    rows = query(
        """
        SELECT block, SUM(running_time)
        FROM verification_steps
        WHERE block IS NOT NULL
        GROUP BY block
        HAVING SUM(running_time) IS NOT NULL
        """
    )
    d = [{"blkid": row[0], "time": row[1]} for row in rows]
    df = pandas.DataFrame(d, columns=["blkid", "time"])
    fig = plotly.express.ecdf(
        df,
        y="time",
        title="Total number of blocks solved",
        ecdfnorm=None,
        orientation="h",
        labels={"count": "# blocks", "time": "Time (s)"},
    )

    return fig.to_html(full_html=False)


def block_solved_percentage_ecdf() -> str:
    rows = query(
        """
        SELECT block,
               100.0 * SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM verification_steps
        WHERE block IS NOT NULL
        GROUP BY block
        HAVING COUNT(*) > 0
        """
    )
    d = [{"blkid": row[0], "pct": row[1]} for row in rows]
    df = pandas.DataFrame(d, columns=["blkid", "pct"])
    fig = plotly.express.ecdf(
        df,
        y="pct",
        title="Percentage of verification steps solved per block",
        ecdfnorm=None,
        orientation="h",
        ecdfmode="complementary",
        range_y=[0, 100],
        labels={"count": "# blocks", "pct": "% steps solved"},
    )
    return fig.to_html(full_html=False)


def pass_solved_percentage_ecdf() -> str:
    rows = query(
        """
        SELECT passname,
               100.0 * SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM verification_steps
        WHERE passname IS NOT NULL AND passname != ''
        GROUP BY passname
        HAVING COUNT(*) > 0
        """
    )
    d = [{"passname": row[0], "pct": row[1]} for row in rows]
    df = pandas.DataFrame(d, columns=["passname", "pct"]).sort_values("pct", ascending=False)
    fig = plotly.express.bar(
        df,
        x="passname",
        y="pct",
        title="Percentage of verification steps solved per pass",
        range_y=[0, 100],
        labels={"passname": "pass", "pct": "% steps solved"},
    )
    fig.update_xaxes(tickangle=-35)
    return fig.to_html(full_html=False)


def cactus_time_passes(data) -> str:
    d = []
    for name,v in list_passes(data):
        d.append({
            "name": name,
            "time": v.running_time,
        })

    df = pandas.DataFrame(d, columns=["name", "time"])
    fig = plotly.express.ecdf(
        df,
        y="time",
        title="Total number of optimization passes solved",
        ecdfnorm=None,
        orientation="h",
        labels={"count": "# optimization passes", "time": "Time (s)"},
    )

    return fig.to_html(full_html=False)