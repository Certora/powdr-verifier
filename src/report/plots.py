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
        WHERE parent IS NULL AND status = 'success' AND running_time IS NOT NULL
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
def _scatter_time_size_frame(input_base: Path) -> pandas.DataFrame:
    rows = query(
        "SELECT input1, input2, size_bytes, running_time, status FROM verification_steps "
        "WHERE running_time IS NOT NULL AND size_bytes IS NOT NULL"
    )
    rec = []
    for input1, input2, size_bytes, rt, status in rows:
        rec.append(
            {
                "size": size_bytes,
                "time": rt,
                "outcome": "success" if status == "success" else "failed",
                "input1": _path_relative_to_base(str(input1), input_base),
                "input2": _path_relative_to_base(str(input2), input_base),
            }
        )
    return pandas.DataFrame(rec, columns=["size", "time", "outcome", "input1", "input2"])


def _append_trace_counts(fig, counts: dict[str, int]) -> None:
    for trace in fig.data:
        name = str(trace.name)
        count = counts.get(name)
        if count is not None:
            trace.name = f"{name} ({count})"


def scatter_time_size_success_only(input_base: Path) -> str:
    df = _scatter_time_size_frame(input_base)
    df = df[df["outcome"] == "success"]
    if df.empty:
        return ""
    fig = plotly.express.scatter(
        df,
        x="size",
        y="time",
        title="Verification Size vs. Time (success only)",
        labels={
            "size": "Size",
            "time": "Time (s)",
            "input1": "Input file 1",
            "input2": "Input file 2",
        },
        range_x=[0, df["size"].max() * 1.1],
        range_y=[0, df["time"].max() * 1.1],
        hover_data=["input1", "input2"],
    )
    return fig.to_html(full_html=False)


def scatter_time_size_by_outcome(input_base: Path) -> str:
    df = _scatter_time_size_frame(input_base)
    if df.empty:
        return ""
    fig = plotly.express.scatter(
        df,
        x="size",
        y="time",
        color="outcome",
        color_discrete_map={"success": "#636EFA", "failed": "red"},
        title="Verification Size vs. Time (by outcome)",
        labels={
            "size": "Size",
            "time": "Time (s)",
            "outcome": "Outcome",
            "input1": "Input file 1",
            "input2": "Input file 2",
        },
        range_x=[0, df["size"].max() * 1.1],
        range_y=[0, df["time"].max() * 1.1],
        hover_data=["input1", "input2"],
    )
    _append_trace_counts(fig, df["outcome"].value_counts().to_dict())
    return fig.to_html(full_html=False)


def scatter_time_size_by_isqf_and_outcome(input_base: Path) -> str:
    rows = query(
        """
        SELECT v.id, v.input1, v.input2, v.size_bytes, v.running_time, v.status, s.status
        FROM verification_steps v
        JOIN substeps s ON s.verification_step_id = v.id
        WHERE v.running_time IS NOT NULL
          AND v.size_bytes IS NOT NULL
          AND s.name = 'isqf'
          AND s.status IN ('qf', 'not-qf')
        """
    )
    by_step: dict[int, dict[str, object]] = {}
    for step_id, input1, input2, size_bytes, rt, status, isqf_result in rows:
        rec = by_step.setdefault(
            int(step_id),
            {
                "size": size_bytes,
                "time": rt,
                "outcome": "success" if status == "success" else "failed",
                "isqf_result": None,
                "input1": _path_relative_to_base(str(input1), input_base),
                "input2": _path_relative_to_base(str(input2), input_base),
            },
        )
        if isqf_result == "not-qf" or rec["isqf_result"] is None:
            rec["isqf_result"] = str(isqf_result)
    rec = []
    for row in by_step.values():
        isqf_result = row["isqf_result"]
        if isqf_result is None:
            continue
        rec.append({**row, "series": f"{isqf_result} / {row['outcome']}"})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    series_order = ["qf / success", "qf / failed", "not-qf / success", "not-qf / failed"]
    fig = plotly.express.scatter(
        df,
        x="size",
        y="time",
        color="series",
        category_orders={"series": series_order},
        color_discrete_map={
            "qf / success": "#636EFA",
            "qf / failed": "#7F7F7F",
            "not-qf / success": "#00CC96",
            "not-qf / failed": "#EF553B",
        },
        title="Verification Size vs. Time (by isqf result and outcome)",
        labels={
            "size": "Size",
            "time": "Time (s)",
            "series": "Series",
            "input1": "Input file 1",
            "input2": "Input file 2",
        },
        range_x=[0, df["size"].max() * 1.1],
        range_y=[0, df["time"].max() * 1.1],
        hover_data=["input1", "input2"],
    )
    _append_trace_counts(fig, df["series"].value_counts().to_dict())
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
        WHERE s.parent IS NULL AND v.block IS NOT NULL
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
        WHERE s.parent IS NULL AND v.passname IS NOT NULL AND v.passname != ''
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
        WHERE sub.parent IS NULL
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