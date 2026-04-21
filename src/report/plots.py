import functools
from pathlib import Path
import pandas
import plotly.express

from .database import query, query_single_value


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
    whole = query(
        """
        SELECT running_time FROM verification_steps
        WHERE status = 'success' AND running_time IS NOT NULL
        """
    )
    sub = query(
        """
        SELECT name, running_time FROM substeps
        WHERE status = 'success' AND running_time IS NOT NULL
        """
    )
    rec: list[dict[str, object]] = []
    for (rt,) in whole:
        rec.append({"series": "verification", "time": rt})
    for name, rt in sub:
        rec.append({"series": str(name), "time": rt})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    names = {r["series"] for r in rec}
    order: list[str] = []
    if "verification" in names:
        order.append("verification")
        names.discard("verification")
    order.extend(sorted(names))
    fig = plotly.express.ecdf(
        df,
        y="time",
        color="series",
        title="Verifies solved",
        ecdfnorm=None,
        orientation="h",
        category_orders={"series": order},
        labels={"count": "# samples", "time": "Time (s)", "series": "Series"},
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


def block_solved_percentage_ecdf() -> str:
    whole = query(
        """
        SELECT block,
               100.0 * SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM verification_steps
        WHERE block IS NOT NULL
        GROUP BY block
        HAVING COUNT(*) > 0
        """
    )
    sub = query(
        """
        SELECT v.block, s.name,
               100.0 * SUM(CASE WHEN s.status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM substeps s
        JOIN verification_steps v ON v.id = s.verification_step_id
        WHERE v.block IS NOT NULL
        GROUP BY v.block, s.name
        HAVING COUNT(*) > 0
        """
    )
    rec: list[dict[str, object]] = []
    for _blk, pct in whole:
        rec.append({"series": "verification", "pct": pct})
    for _blk, name, pct in sub:
        rec.append({"series": str(name), "pct": pct})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    names = {r["series"] for r in rec}
    order: list[str] = []
    if "verification" in names:
        order.append("verification")
        names.discard("verification")
    order.extend(sorted(names))
    fig = plotly.express.ecdf(
        df,
        y="pct",
        color="series",
        title="Percentage of verification steps solved per block",
        ecdfnorm=None,
        orientation="h",
        ecdfmode="complementary",
        range_y=[0, 100],
        category_orders={"series": order},
        labels={"count": "# blocks", "pct": "% solved", "series": "Series"},
    )
    return fig.to_html(full_html=False)


def pass_solved_percentage_ecdf() -> str:
    whole = query(
        """
        SELECT passname,
               100.0 * SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM verification_steps
        WHERE passname IS NOT NULL AND passname != ''
        GROUP BY passname
        HAVING COUNT(*) > 0
        """
    )
    sub = query(
        """
        SELECT v.passname, s.name,
               100.0 * SUM(CASE WHEN s.status = 'success' THEN 1 ELSE 0 END) / COUNT(*) AS pct
        FROM substeps s
        JOIN verification_steps v ON v.id = s.verification_step_id
        WHERE v.passname IS NOT NULL AND v.passname != ''
        GROUP BY v.passname, s.name
        HAVING COUNT(*) > 0
        """
    )
    rec: list[dict[str, object]] = []
    for passname, pct in whole:
        rec.append({"series": "verification", "passname": passname, "pct": pct})
    for passname, name, pct in sub:
        rec.append({"series": str(name), "passname": passname, "pct": pct})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    ver = df[df["series"] == "verification"].set_index("passname")["pct"]
    pass_order = ver.sort_values(ascending=False).index.tolist()
    names = {r["series"] for r in rec}
    order: list[str] = []
    if "verification" in names:
        order.append("verification")
        names.discard("verification")
    order.extend(sorted(names))
    fig = plotly.express.bar(
        df,
        x="passname",
        y="pct",
        color="series",
        category_orders={"passname": pass_order, "series": order},
        title="Percentage of verification steps solved per pass",
        range_y=[0, 100],
        labels={"passname": "pass", "pct": "% solved", "series": "Series"},
    )
    fig.update_layout(barmode="group")
    fig.update_xaxes(tickangle=-35)
    return fig.to_html(full_html=False)


def _path_relative_to_base(path_str: str, base: Path) -> str:
    try:
        return str(Path(path_str).resolve().relative_to(base.resolve()))
    except ValueError:
        return path_str


def substeps_stacked_lines(input_base: Path) -> str:
    rows = query(
        """
        SELECT sub.verification_step_id, sub.name, COALESCE(sub.running_time, 0),
               v.input1, v.input2, sub.status
        FROM substeps sub
        JOIN verification_steps v ON v.id = sub.verification_step_id
        """
    )
    if not rows:
        return ""
    df = pandas.DataFrame(
        rows,
        columns=["verification_step_id", "name", "running_time", "input1", "input2", "status"],
    )
    df = df.groupby(["verification_step_id", "name"], as_index=False).agg(
        running_time=("running_time", "sum"),
        input1=("input1", "first"),
        input2=("input2", "first"),
        status=("status", "first"),
    )
    df["input1"] = df["input1"].map(lambda p: _path_relative_to_base(str(p), input_base))
    df["input2"] = df["input2"].map(lambda p: _path_relative_to_base(str(p), input_base))
    pt = df.pivot_table(
        index="verification_step_id",
        columns="name",
        values="running_time",
        aggfunc="sum",
        fill_value=0,
    )
    enc_col = "verify-encode"
    encode_series = pt[enc_col] if enc_col in pt.columns else pandas.Series(0.0, index=pt.index)
    step_order = encode_series.sort_values(ascending=True).index.tolist()
    rank = {vid: i for i, vid in enumerate(step_order)}
    df["x_rank"] = df["verification_step_id"].map(rank)

    names = list(df["name"].unique())
    stack_order = []
    if enc_col in names:
        stack_order.append(enc_col)
    stack_order.extend(sorted(n for n in names if n != enc_col))

    fig = plotly.express.bar(
        df,
        x="x_rank",
        y="running_time",
        color="name",
        category_orders={"name": stack_order},
        title="Substep time by verification step (stacked)",
        labels={
            "x_rank": "Step order (sorted by encode time)",
            "running_time": "Time (s)",
            "name": "Substep",
            "input1": "Input file 1",
            "input2": "Input file 2",
            "verification_step_id": "Step id",
            "status": "Status",
        },
        hover_data=["verification_step_id", "input1", "input2", "status"],
    )
    fig.update_layout(barmode="stack", bargap=0)
    return fig.to_html(full_html=False)