"""Plotly figures and HTML fragments for report dashboards (ECDFs, timelines, heatmaps)."""
import filecmp
import functools
import html
from pathlib import Path
import pandas
import plotly.express
import plotly.graph_objects as go
from plotly.subplots import make_subplots

from .database import query, query_single_value
from .html_utils import copy_command_badge


_PLOT_FONT_SIZE = 14

_BLOCK_SERIES_ORDER = ["encode", "completeness", "soundness"]

_PASS_SOLVED_SUBSTEPS = {
    "verify-encode": "encode",
    "check (completeness)": "check (completeness)",
    "check (soundness)": "check (soundness)",
    "simplifier (completeness)": "simplify (completeness)",
    "simplifier (soundness)": "simplify (soundness)",
}

_PASS_SOLVED_SERIES_ORDER = list(_PASS_SOLVED_SUBSTEPS.values())

_PASS_SOLVED_SUBSTEP_NAMES_SQL = ", ".join(
    f"'{name}'" for name in _PASS_SOLVED_SUBSTEPS
)

_PASS_SOLVED_SUBSTEP_NAMES_UNION = " UNION ALL ".join(
    f"SELECT '{name}' AS name" for name in _PASS_SOLVED_SUBSTEPS
)


def _substep_solved_where(prefix: str = "s.") -> str:
    return f"""(
        ({prefix}name = 'verify-encode' AND {prefix}status = 'success')
        OR ({prefix}name IN ('check (completeness)', 'check (soundness)')
            AND ({prefix}status = 'success'
                 OR ({prefix}status IN ('sat', 'unsat') AND {prefix}status = {prefix}expected)))
        OR ({prefix}name IN ('simplifier (completeness)', 'simplifier (soundness)')
            AND {prefix}status IN ('qf', 'not-qf'))
    )"""


def _substep_solved_case(prefix: str = "s.") -> str:
    return f"CASE WHEN {_substep_solved_where(prefix)} THEN 1 ELSE 0 END"


def _report_series_name(substep_name: str) -> str | None:
    return _PASS_SOLVED_SUBSTEPS.get(substep_name)


def _style_fig(fig) -> None:
    fig.update_layout(
        font=dict(size=_PLOT_FONT_SIZE),
        title_font=dict(size=_PLOT_FONT_SIZE + 2),
    )


def _fig_html(fig) -> str:
    _style_fig(fig)
    return fig.to_html(full_html=False, include_plotlyjs=False)


def basic_stats() -> str:
    n_blocks = query_single_value(
        "SELECT COUNT(DISTINCT block) FROM verification_steps WHERE block IS NOT NULL"
    )
    n_steps = query_single_value("SELECT COUNT(*) FROM verification_steps")
    n_checked = query_single_value(
        "SELECT COUNT(*) FROM verification_steps WHERE status = 'success'"
    )
    n_timeouts = query_single_value(
        "SELECT COUNT(*) FROM verification_steps WHERE status = 'timeout'"
    )
    n_memouts = query_single_value(
        "SELECT COUNT(*) FROM verification_steps WHERE status = 'memout'"
    )
    n_not_qf = query_single_value(
        """
        SELECT COUNT(DISTINCT v.id) FROM verification_steps v
        JOIN substeps s ON s.verification_step_id = v.id
        WHERE s.name = 'isqf' AND s.status = 'not-qf'
        """
    )
    n_wrongs = query_single_value(
        """
        SELECT COUNT(DISTINCT v.id) FROM verification_steps v
        WHERE EXISTS (
            SELECT 1 FROM substeps s
            WHERE s.verification_step_id = v.id
              AND s.expected IN ('sat', 'unsat')
              AND s.result IN ('sat', 'unsat')
              AND s.result != s.expected
        )
        """
    )
    n_errors = query_single_value(
        "SELECT COUNT(*) FROM verification_steps WHERE status = 'error'"
    )
    worst_blocks = query(
        """
        SELECT block,
               COUNT(*) AS n_total,
               SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) AS n_ok
        FROM verification_steps
        WHERE block IS NOT NULL
        GROUP BY block
        HAVING COUNT(*) > 0
        ORDER BY (COUNT(*) - SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END)) DESC,
                 COUNT(*) DESC,
                 block ASC
        """
    )
    n_passes = query_single_value(
        "SELECT COUNT(DISTINCT passname) FROM verification_steps "
        "WHERE passname IS NOT NULL AND passname != ''"
    )
    worst_passes = query(
        """
        SELECT passname,
               COUNT(*) AS n_total,
               SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END) AS n_ok
        FROM verification_steps
        WHERE passname IS NOT NULL AND passname != ''
        GROUP BY passname
        HAVING COUNT(*) > 0
        ORDER BY (COUNT(*) - SUM(CASE WHEN status = 'success' THEN 1 ELSE 0 END)) DESC,
                 COUNT(*) DESC,
                 passname ASC
        """
    )
    selected_jobs = _jobs_of_interest()
    selected_jobs_list = _render_selected_jobs_list("Jobs of interest", selected_jobs)
    steps_rows = [
        ("checked", n_checked or 0),
        ("timeouts", n_timeouts or 0),
        ("memouts", n_memouts or 0),
        ("errors", n_errors or 0),
        ("not-qf", n_not_qf or 0),
        ("wrongs", n_wrongs or 0),
    ]
    blocks_detail: list[tuple[str, object, int]] = []
    for row in worst_blocks or []:
        blk, n_total, n_ok = row[0], int(row[1]), int(row[2])
        n_fail = n_total - n_ok
        blocks_detail.append((f"block {blk}", f"{n_fail} failed / {n_total} steps", n_fail))
    if not blocks_detail:
        blocks_detail.append(("—", "no block data", 0))
    passes_detail: list[tuple[str, object, int]] = []
    for row in worst_passes or []:
        pname, n_total, n_ok = row[0], int(row[1]), int(row[2])
        n_fail = n_total - n_ok
        passes_detail.append((str(pname), f"{n_fail} failed / {n_total} steps", n_fail))
    if not passes_detail:
        passes_detail.append(("—", "no pass data", 0))
    return f"""
<section class="container-fluid py-3">
  <div class="row g-2 mb-3">
    {_render_stat_card_detail(f"{n_steps or 0} verification steps", steps_rows)}
    {_render_stat_card_detail(
        f"{n_blocks or 0} blocks", blocks_detail, preview_limit=_STAT_CARD_PREVIEW, sortable=True
    )}
    {_render_stat_card_detail(
        f"{n_passes or 0} passes", passes_detail, preview_limit=_STAT_CARD_PREVIEW, sortable=True
    )}
  </div>
  <div class="row g-3">
    <div class="col-12">{selected_jobs_list}</div>
  </div>
</section>
{_SORT_SCRIPT}

"""


def _parse_job_kinds(kinds_csv: str | None) -> list[tuple[str, str | None]]:
    if not kinds_csv:
        return []
    kinds: list[tuple[str, str | None]] = []
    for part in kinds_csv.split(","):
        if "@" in part:
            kind, step = part.split("@", 1)
            kinds.append((kind, step or None))
        else:
            kinds.append((part, None))
    return kinds


def _jobs_of_interest() -> list[tuple]:
    rows = query(
        """
        WITH interested AS (
            SELECT
                v.id,
                v.input1,
                v.input2,
                v.running_time,
                v.size_bytes,
                v.command_line,
                v.status
            FROM verification_steps v
            WHERE
                EXISTS (
                    SELECT 1 FROM substeps s
                    WHERE s.verification_step_id = v.id
                      AND s.expected IN ('sat', 'unsat')
                      AND s.result IN ('sat', 'unsat')
                      AND s.result != s.expected
                )
                OR v.status IN ('error', 'timeout', 'memout')
                OR EXISTS (
                    SELECT 1 FROM substeps s
                    WHERE s.verification_step_id = v.id
                      AND s.name = 'check'
                      AND s.status = 'error'
                      AND (s.result = 'unknown' OR s.result LIKE 'unknown-%')
                )
                OR EXISTS (
                    SELECT 1 FROM substeps s
                    WHERE s.verification_step_id = v.id
                      AND s.name = 'isqf'
                      AND s.status = 'not-qf'
                )
        ),
        outcome_at AS (
            WITH RECURSIVE tree AS (
                SELECT id, verification_step_id, name, status, result, parent, 0 AS depth
                FROM substeps
                WHERE parent IS NULL
                UNION ALL
                SELECT s.id, s.verification_step_id, s.name, s.status, s.result, s.parent,
                       t.depth + 1
                FROM substeps s
                JOIN tree t ON s.parent = t.id
            ),
            matches AS (
                SELECT verification_step_id, name, depth,
                       CASE
                           WHEN status = 'timeout' OR result = 'timeout' THEN 'timeout'
                           WHEN status = 'memout' OR result = 'memout' THEN 'memout'
                       END AS outcome
                FROM tree
                WHERE status IN ('timeout', 'memout') OR result IN ('timeout', 'memout')
            ),
            picked AS (
                SELECT verification_step_id, outcome, name AS outcome_step,
                       ROW_NUMBER() OVER (
                           PARTITION BY verification_step_id, outcome
                           ORDER BY depth DESC, name ASC
                       ) AS rn
                FROM matches
                WHERE outcome IS NOT NULL
            )
            SELECT verification_step_id, outcome, outcome_step
            FROM picked
            WHERE rn = 1
        ),
        job_kinds AS (
            SELECT i.id, 'wrong' AS kind, NULL AS step, 1 AS ord
            FROM interested i
            WHERE EXISTS (
                SELECT 1 FROM substeps s
                WHERE s.verification_step_id = i.id
                  AND s.expected IN ('sat', 'unsat')
                  AND s.result IN ('sat', 'unsat')
                  AND s.result != s.expected
            )
            UNION ALL
            SELECT i.id, 'error', NULL, 2
            FROM interested i
            WHERE i.status = 'error'
            UNION ALL
            SELECT i.id, 'unknown', NULL, 3
            FROM interested i
            WHERE EXISTS (
                SELECT 1 FROM substeps s
                WHERE s.verification_step_id = i.id
                  AND s.name = 'check'
                  AND s.status = 'error'
                  AND (s.result = 'unknown' OR s.result LIKE 'unknown-%')
            )
            UNION ALL
            SELECT i.id, 'timeout', o.outcome_step, 4
            FROM interested i
            JOIN outcome_at o
                ON o.verification_step_id = i.id AND o.outcome = 'timeout'
            WHERE i.status = 'timeout'
            UNION ALL
            SELECT i.id, 'memout', o.outcome_step, 5
            FROM interested i
            JOIN outcome_at o
                ON o.verification_step_id = i.id AND o.outcome = 'memout'
            WHERE i.status = 'memout'
            UNION ALL
            SELECT i.id, 'not-qf', NULL, 6
            FROM interested i
            WHERE EXISTS (
                SELECT 1 FROM substeps s
                WHERE s.verification_step_id = i.id
                  AND s.name = 'isqf'
                  AND s.status = 'not-qf'
            )
        )
        SELECT
            (
                SELECT GROUP_CONCAT(
                    jk.kind || COALESCE('@' || jk.step, ''),
                    ',' ORDER BY jk.ord
                )
                FROM job_kinds jk
                WHERE jk.id = i.id
            ) AS kinds,
            i.input1,
            i.input2,
            i.running_time,
            i.size_bytes,
            COALESCE(
                (
                    SELECT s.command_line FROM substeps s
                    JOIN outcome_at o ON o.verification_step_id = i.id
                    WHERE s.verification_step_id = i.id
                      AND s.name = o.outcome_step
                      AND o.outcome IN ('timeout', 'memout')
                    ORDER BY CASE o.outcome WHEN 'timeout' THEN 1 ELSE 2 END
                    LIMIT 1
                ),
                i.command_line
            ) AS command_line
        FROM interested i
        ORDER BY i.running_time IS NULL, i.running_time ASC, i.size_bytes ASC
        """
    )
    return [
        (
            _parse_job_kinds(kinds_csv),
            input1,
            input2,
            running_time,
            size_bytes,
            command_line,
        )
        for kinds_csv, input1, input2, running_time, size_bytes, command_line in rows
    ]


def _job_name(input1: str, input2: str) -> str:
    p1 = Path(input1).name.removesuffix(".json")
    p2 = Path(input2).name.removesuffix(".json")
    return f"{p1} -> {p2}"


def _inputs_byte_identical(input1: str, input2: str) -> bool:
    p1, p2 = Path(input1), Path(input2)
    if p1 == p2:
        return True
    try:
        return filecmp.cmp(p1, p2, shallow=False)
    except OSError:
        return False


def _badge_identical_inputs() -> str:
    title = html.escape("Byte-identical dumps", quote=True)
    return (
        f'<span class="badge text-bg-light border" title="{title}" '
        f'style="font-size:0.82em">≡</span>'
    )


def _render_stat_card(label: str, value: object) -> str:
    return (
        '<div class="col-12 col-md-4">'
        '<div class="card h-100 shadow-sm">'
        '<div class="card-body py-2 px-3">'
        f'<div class="small text-body-secondary">{html.escape(str(label))}</div>'
        f'<div class="fs-5 fw-semibold">{html.escape(str(value))}</div>'
        "</div></div></div>"
    )


_STAT_CARD_PREVIEW = 6
_JOBS_LIST_PREVIEW = 10


def _render_sort_links(
    keys: list[tuple[str, str]], *, active: str, direction: str = "asc"
) -> str:
    parts: list[str] = []
    for i, (key, label) in enumerate(keys):
        if i:
            parts.append('<span class="mx-1">·</span>')
        is_active = key == active
        active_cls = " stat-sort-active" if is_active else ""
        dir_attr = f' data-stat-sort-dir="{direction}"' if is_active else ""
        if is_active:
            glyph = "↑" if direction == "asc" else "↓"
        else:
            glyph = "↕"
        parts.append(
            f'<a href="#" class="stat-sort-link{active_cls}" data-stat-sort="{key}"{dir_attr}>'
            f'<span class="me-1 stat-sort-glyph" aria-hidden="true">{glyph}</span>'
            f"{html.escape(label)}</a>"
        )
    return '<div class="small text-nowrap text-body-secondary">' + "".join(parts) + "</div>"


def _render_stat_detail_row(
    key: str,
    value: object,
    *,
    sort_fails: int | None = None,
) -> str:
    attrs = ""
    if sort_fails is not None:
        attrs = (
            ' class="sortable-item d-flex justify-content-between small mt-1"'
            f' data-sort-name="{html.escape(key, quote=True)}"'
            f' data-sort-fails="{sort_fails}"'
        )
    else:
        attrs = ' class="d-flex justify-content-between small mt-1"'
    return (
        f"<div{attrs}>"
        f'<span class="text-body-secondary">{html.escape(key)}</span>'
        f'<span class="fw-medium">{html.escape(str(value))}</span>'
        "</div>"
    )


_SORT_SCRIPT = """<style>
.stat-sort-link {
  color: var(--bs-secondary-color);
  text-decoration: none;
}
.stat-sort-link:hover {
  color: var(--bs-body-color);
}
.stat-sort-link.stat-sort-active {
  color: var(--bs-body-color);
  font-weight: 600;
}
</style>
<script>
(function () {
  var DEFAULT_DIR = {name: "asc", kind: "asc", fails: "desc", time: "asc", size: "asc"};

  function compareRows(a, b, sortBy) {
    if (sortBy === "name" || sortBy === "kind") {
      var attr = sortBy === "name" ? "data-sort-name" : "data-sort-kind";
      return a.getAttribute(attr).localeCompare(b.getAttribute(attr));
    }
    if (sortBy === "fails") {
      return Number(a.getAttribute("data-sort-fails"))
        - Number(b.getAttribute("data-sort-fails"));
    }
    var key = sortBy === "time" ? "data-sort-time" : "data-sort-size";
    var av = Number(a.getAttribute(key));
    var bv = Number(b.getAttribute(key));
    if (av < 0 && bv < 0) return 0;
    if (av < 0) return 1;
    if (bv < 0) return -1;
    return av - bv;
  }

  function updateSortLinks(card, activeLink, dir) {
    card.querySelectorAll("[data-stat-sort]").forEach(function (l) {
      var glyph = l.querySelector(".stat-sort-glyph");
      if (l === activeLink) {
        l.classList.add("stat-sort-active");
        l.setAttribute("data-stat-sort-dir", dir);
        if (glyph) glyph.textContent = dir === "asc" ? "↑" : "↓";
      } else {
        l.classList.remove("stat-sort-active");
        l.removeAttribute("data-stat-sort-dir");
        if (glyph) glyph.textContent = "↕";
      }
    });
  }

  function renumberJobs(container) {
    var items = container.querySelectorAll(".sortable-item");
    Array.prototype.forEach.call(items, function (item, i) {
      var idx = item.querySelector(".job-list-idx");
      if (idx) idx.textContent = (i + 1) + ".";
    });
  }

  function applyPreview(container) {
    var limit = Number(container.getAttribute("data-preview-limit"));
    if (!limit) return;
    var listType = container.getAttribute("data-list-type");
    var more = container.querySelector(".stat-detail-more");
    var rows = Array.prototype.slice.call(
      container.querySelectorAll(".sortable-item")
    );
    if (more) more.remove();
    if (listType === "ul") {
      var ul = container.querySelector("ul");
      if (!ul) {
        ul = document.createElement("ul");
        ul.className = "list-group list-group-flush";
        container.appendChild(ul);
      }
      rows.forEach(function (row) {
        ul.appendChild(row);
      });
    } else {
      rows.forEach(function (row) {
        container.appendChild(row);
      });
    }
    var visible = rows.slice(0, limit);
    var hidden = rows.slice(limit);
    if (listType === "ul") {
      var visibleUl = container.querySelector("ul");
      visible.forEach(function (row) {
        visibleUl.appendChild(row);
      });
      renumberJobs(container);
      if (!hidden.length) return;
      more = document.createElement("details");
      more.className = "stat-detail-more mt-1";
      var summary = document.createElement("summary");
      summary.className = "small text-body-secondary";
      summary.textContent = "Show " + hidden.length + " more";
      more.appendChild(summary);
      var hiddenUl = document.createElement("ul");
      hiddenUl.className = "list-group list-group-flush mt-1";
      hidden.forEach(function (row) {
        hiddenUl.appendChild(row);
      });
      more.appendChild(hiddenUl);
      container.appendChild(more);
      return;
    }
    if (!hidden.length) return;
    more = document.createElement("details");
    more.className = "stat-detail-more mt-1";
    var summary = document.createElement("summary");
    summary.className = "small text-body-secondary";
    summary.textContent = "Show " + hidden.length + " more";
    more.appendChild(summary);
    hidden.forEach(function (row) {
      more.appendChild(row);
    });
    container.appendChild(more);
  }

  document.addEventListener("click", function (e) {
    var link = e.target.closest("[data-stat-sort]");
    if (!link) return;
    e.preventDefault();
    var card = link.closest(".card-body");
    if (!card) return;
    var container = card.querySelector(".sortable-rows");
    if (!container) return;
    var sortBy = link.getAttribute("data-stat-sort");
    var dir;
    if (link.classList.contains("stat-sort-active")) {
      dir = link.getAttribute("data-stat-sort-dir") === "asc" ? "desc" : "asc";
    } else {
      dir = DEFAULT_DIR[sortBy] || "asc";
    }
    var rows = Array.prototype.slice.call(
      container.querySelectorAll(".sortable-item")
    );
    rows.sort(function (a, b) {
      var cmp = compareRows(a, b, sortBy);
      return dir === "desc" ? -cmp : cmp;
    });
    var more = container.querySelector(".stat-detail-more");
    if (more) more.remove();
    if (container.getAttribute("data-list-type") === "ul") {
      var ul = container.querySelector("ul");
      rows.forEach(function (row) {
        ul.appendChild(row);
      });
    } else {
      rows.forEach(function (row) {
        container.appendChild(row);
      });
    }
    applyPreview(container);
    updateSortLinks(card, link, dir);
  });
})();
</script>"""


def _render_stat_card_detail(
    headline: str,
    rows: list[tuple[str, object] | tuple[str, object, int]],
    *,
    preview_limit: int | None = None,
    sortable: bool = False,
) -> str:
    def render_row(row: tuple) -> str:
        key, value = row[0], row[1]
        fails = int(row[2]) if len(row) >= 3 else None
        return _render_stat_detail_row(key, value, sort_fails=fails if sortable else None)

    if preview_limit is not None and len(rows) > preview_limit:
        preview = rows[:preview_limit]
        rest = rows[preview_limit:]
        sub = "".join(render_row(r) for r in preview)
        sub += (
            '<details class="stat-detail-more mt-1">'
            f'<summary class="small text-body-secondary">Show {len(rest)} more</summary>'
            + "".join(render_row(r) for r in rest)
            + "</details>"
        )
    else:
        sub = "".join(render_row(r) for r in rows)

    if sortable:
        preview_attr = (
            f' data-preview-limit="{preview_limit}"' if preview_limit is not None else ""
        )
        sub = f'<div class="sortable-rows"{preview_attr}>{sub}</div>'
        title = (
            '<div class="d-flex justify-content-between align-items-baseline gap-2">'
            f'<div class="fs-5 fw-semibold">{html.escape(headline)}</div>'
            f'{_render_sort_links([("name", "name"), ("fails", "fails")], active="fails", direction="desc")}'
            "</div>"
        )
    else:
        title = f'<div class="fs-5 fw-semibold">{html.escape(headline)}</div>'

    return (
        '<div class="col-12 col-md-4">'
        '<div class="card h-100 shadow-sm">'
        '<div class="card-body py-2 px-3">'
        f"{title}"
        f'<div class="mt-2 pt-2 border-top">{sub}</div>'
        "</div></div></div>"
    )


def _render_kind_badges(kinds: list[tuple[str, str | None]]) -> str:
    return "".join(_badge_kind(kind, at_step) for kind, at_step in kinds)


def _render_job_list_item(idx: int, row: tuple, *, sortable: bool = False) -> str:
    kinds, input1, input2, running_time, size_bytes = row[:5]
    command_line = row[5] if len(row) > 5 else None
    job_name = _job_name(str(input1), str(input2))
    job = html.escape(job_name)
    identical_badge = (
        _badge_identical_inputs()
        if _inputs_byte_identical(str(input1), str(input2))
        else ""
    )
    kind_badges = _render_kind_badges(kinds)
    time_badge = _badge_time(running_time)
    size_badge = _badge_bytes(size_bytes)
    copy_badge = copy_command_badge(command_line)
    kind_sort = ",".join(
        kind if not at_step else f"{kind}@{at_step}" for kind, at_step in kinds
    )
    if sortable:
        time_val = float(running_time) if running_time is not None else -1
        size_val = int(size_bytes) if size_bytes is not None else -1
        item_attrs = (
            ' class="list-group-item px-0 d-flex align-items-center sortable-item"'
            f' data-sort-name="{html.escape(job_name, quote=True)}"'
            f' data-sort-kind="{html.escape(kind_sort, quote=True)}"'
            f' data-sort-time="{time_val}"'
            f' data-sort-size="{size_val}"'
        )
    else:
        item_attrs = ' class="list-group-item px-0 d-flex align-items-center"'
    return (
        f"<li{item_attrs}>"
        f"<span><span class='text-body-secondary me-2 job-list-idx'>{idx}.</span>"
        f"<code>{job}</code></span>"
        f"<span class='ms-auto d-flex align-items-center gap-1'>"
        f"{identical_badge}{kind_badges} {time_badge} {size_badge}{copy_badge}</span>"
        "</li>"
    )


def _render_selected_jobs_list(title: str, rows: list[tuple]) -> str:
    if not rows:
        return (
            '<div class="card h-100 shadow-sm"><div class="card-body py-2 px-3">'
            f'<h6 class="mb-2">{html.escape(title)}</h6>'
            '<span class="text-body-secondary">None</span>'
            "</div></div>"
        )
    preview = rows[:_JOBS_LIST_PREVIEW]
    rest = rows[_JOBS_LIST_PREVIEW:]
    list_html = (
        f'<div class="sortable-rows" data-preview-limit="{_JOBS_LIST_PREVIEW}"'
        f' data-list-type="ul">'
        f"<ul class='list-group list-group-flush'>"
        f"{''.join(_render_job_list_item(i, row, sortable=True) for i, row in enumerate(preview, start=1))}"
        "</ul>"
    )
    if rest:
        n_more = len(rest)
        list_html += (
            '<details class="stat-detail-more mt-1">'
            f'<summary class="small text-body-secondary">'
            f"Show {n_more} more</summary>"
            f"<ul class='list-group list-group-flush mt-1'>"
            f"{''.join(_render_job_list_item(i, row, sortable=True) for i, row in enumerate(rest, start=len(preview) + 1))}"
            "</ul></details>"
        )
    list_html += "</div>"
    header = (
        '<div class="d-flex justify-content-between align-items-baseline gap-2 mb-2">'
        f'<h6 class="mb-0">{html.escape(title)}</h6>'
        f'{_render_sort_links([("name", "name"), ("kind", "type"), ("time", "time"), ("size", "size")], active="time", direction="asc")}'
        "</div>"
    )
    return (
        '<div class="card h-100 shadow-sm"><div class="card-body py-2 px-3">'
        f"{header}{list_html}"
        "</div></div>"
    )


def _badge_time(running_time: object) -> str:
    if running_time is None:
        label = "n/a"
    else:
        label = f"{float(running_time):.2f}s"
    return f'<span class="badge text-bg-primary">{html.escape(label)}</span>'


def _badge_bytes(size_bytes: object) -> str:
    if size_bytes is None:
        label = "n/a"
    else:
        label = _format_bytes(int(size_bytes))
    return f'<span class="badge text-bg-secondary">{html.escape(label)}</span>'


def _format_bytes(size_bytes: int) -> str:
    if size_bytes < 1024:
        return f"{size_bytes} B"
    if size_bytes < 1024 * 1024:
        return f"{size_bytes / 1024:.1f} KB"
    return f"{size_bytes / (1024 * 1024):.1f} MB"


def _badge_kind(kind: str, at_step: object = None) -> str:
    if kind == "wrong":
        return f'<span class="badge text-bg-danger">{html.escape(kind)}</span>'
    if kind == "error":
        style = (
            "background:repeating-linear-gradient(-45deg,#842029 0 5px,#c82333 5px 10px);"
            "color:#fff;border:1px solid rgba(0,0,0,.2)"
        )
        return f'<span class="badge" style="{style}">{html.escape(kind)}</span>'
    if kind == "timeout":
        label = kind if not at_step else f"{kind}@{at_step}"
        return f'<span class="badge text-bg-warning">{html.escape(label)}</span>'
    if kind == "memout":
        label = kind if not at_step else f"{kind}@{at_step}"
        style = "background:#ffedd5;color:#9a3412;border:1px solid #fdba74"
        return f'<span class="badge" style="{style}">{html.escape(label)}</span>'
    if kind == "unknown":
        css = "text-bg-warning"
    elif kind == "not-qf":
        css = "text-bg-info"
    else:
        css = "text-bg-dark"
    return f'<span class="badge {css}">{html.escape(kind)}</span>'

def verified_over_time() -> str:
    sub = query(
        f"""
        SELECT name, running_time FROM substeps s
        WHERE parent IS NULL
          AND name IN ({_PASS_SOLVED_SUBSTEP_NAMES_SQL})
          AND running_time IS NOT NULL
          AND {_substep_solved_where()}
        """
    )
    rec: list[dict[str, object]] = []
    for name, rt in sub:
        series = _report_series_name(str(name))
        if series is None:
            continue
        rec.append({"series": series, "time": rt})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    order = [s for s in _PASS_SOLVED_SERIES_ORDER if s in df["series"].unique()]
    fig = plotly.express.ecdf(
        df,
        y="time",
        color="series",
        title="Steps solved over time",
        ecdfnorm=None,
        orientation="h",
        category_orders={"series": order},
        labels={
            "count": "number of steps",
            "time": "time (s)",
            "series": "Series",
        },
    )
    fig.update_xaxes(title_text="number of steps")
    fig.update_yaxes(title_text="time (s)")
    return _fig_html(fig)

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
    return _fig_html(fig)


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
    return _fig_html(fig)


def block_solved_percentage_ecdf() -> str:
    rows = query(
        """
        WITH step_outcomes AS (
            SELECT
                v.block,
                v.id,
                MAX(CASE
                    WHEN s.name = 'verify-encode' AND s.parent IS NULL AND s.status = 'success'
                    THEN 1 ELSE 0
                END) AS encode_ok,
                MAX(CASE
                    WHEN s.name = 'check (completeness)' AND s.parent IS NULL
                         AND s.status = 'success'
                    THEN 1 ELSE 0
                END) AS completeness_ok,
                MAX(CASE
                    WHEN s.name = 'check (soundness)' AND s.parent IS NULL AND s.status = 'success'
                    THEN 1 ELSE 0
                END) AS soundness_ok
            FROM verification_steps v
            LEFT JOIN substeps s ON s.verification_step_id = v.id
            WHERE v.block IS NOT NULL
            GROUP BY v.block, v.id
        ),
        block_rates AS (
            SELECT
                block,
                100.0 * SUM(encode_ok) / COUNT(*) AS pct_encode,
                100.0 * SUM(completeness_ok) / COUNT(*) AS pct_completeness,
                100.0 * SUM(soundness_ok) / COUNT(*) AS pct_soundness
            FROM step_outcomes
            GROUP BY block
        )
        SELECT pct_encode, pct_completeness, pct_soundness FROM block_rates
        """
    )
    rec: list[dict[str, object]] = []
    for pct_encode, pct_completeness, pct_soundness in rows:
        rec.append({"series": "encode", "pct": pct_encode})
        rec.append({"series": "completeness", "pct": pct_completeness})
        rec.append({"series": "soundness", "pct": pct_soundness})
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    n_blocks = len(rows)
    order = [s for s in _BLOCK_SERIES_ORDER if s in df["series"].unique()]
    fig = plotly.express.ecdf(
        df,
        y="pct",
        color="series",
        title="Percentage solved per block",
        ecdfnorm=None,
        orientation="h",
        ecdfmode="complementary",
        range_y=[0, 100],
        category_orders={"series": order},
        labels={"pct": "% solved", "series": "Series"},
    )
    fig.for_each_trace(lambda t: t.update(x=[xi + 1 for xi in t.x]))
    fig.update_xaxes(title_text="block count", range=[1, n_blocks], dtick=1)
    return _fig_html(fig)


def pass_solved_percentage_ecdf() -> str:
    sub = query(
        f"""
        SELECT v.passname, n.name,
               COUNT(DISTINCT CASE
                   WHEN s.id IS NOT NULL AND {_substep_solved_case()}
                   THEN v.id END) AS n_solved,
               COUNT(DISTINCT v.id) AS n_total,
               100.0 * COUNT(DISTINCT CASE
                   WHEN s.id IS NOT NULL AND {_substep_solved_case()}
                   THEN v.id END) / COUNT(DISTINCT v.id) AS pct
        FROM verification_steps v
        CROSS JOIN ({_PASS_SOLVED_SUBSTEP_NAMES_UNION}) AS n
        LEFT JOIN substeps s ON s.verification_step_id = v.id
            AND s.parent IS NULL AND s.name = n.name
        WHERE v.passname IS NOT NULL AND v.passname != ''
        GROUP BY v.passname, n.name
        HAVING COUNT(DISTINCT v.id) > 0
        """
    )
    rec: list[dict[str, object]] = []
    for passname, name, n_solved, n_total, pct in sub:
        series = _PASS_SOLVED_SUBSTEPS.get(str(name))
        if series is None:
            continue
        rec.append({
            "series": series,
            "passname": passname,
            "pct": pct,
            "n_solved": int(n_solved),
            "n_total": int(n_total),
        })
    if not rec:
        return ""
    df = pandas.DataFrame(rec)
    pass_order = sorted(df["passname"].unique())
    fig = plotly.express.bar(
        df,
        x="passname",
        y="pct",
        color="series",
        custom_data=["n_solved", "n_total"],
        category_orders={"passname": pass_order, "series": _PASS_SOLVED_SERIES_ORDER},
        title="Percentage of verification steps solved per pass",
        range_y=[0, 100],
        labels={"passname": "pass", "pct": "% solved", "series": "Series"},
    )
    fig.update_traces(
        hovertemplate=(
            "pass=%{x}<br>"
            "%{fullData.name}<br>"
            "solved: %{y:.0f}% (%{customdata[0]}/%{customdata[1]})"
            "<extra></extra>"
        ),
    )
    fig.update_layout(barmode="group")
    fig.update_xaxes(tickangle=-35)
    return _fig_html(fig)


def simplifier_pass_stats_bar() -> str:
    time_rows = query(
        """
        SELECT s.name, s.running_time
        FROM substeps s
        JOIN substeps p ON s.parent = p.id AND p.name = 'simplifier'
        WHERE s.name NOT IN ('load', 'dump')
          AND (s.result IS NULL OR s.result NOT IN ('skipped', 'timeout', 'memout'))
          AND s.running_time IS NOT NULL
        """
    )
    count_rows = query(
        """
        SELECT s.name,
               SUM(CASE WHEN s.result = 'timeout' THEN 1 ELSE 0 END),
               SUM(CASE WHEN s.result = 'memout' THEN 1 ELSE 0 END),
               SUM(CASE WHEN s.result = 'skipped' THEN 1 ELSE 0 END),
               SUM(CASE WHEN s.result IS NULL OR s.result NOT IN ('skipped', 'timeout', 'memout')
                        THEN 1 ELSE 0 END)
        FROM substeps s
        JOIN substeps p ON s.parent = p.id AND p.name = 'simplifier'
        WHERE s.name NOT IN ('load', 'dump')
        GROUP BY s.name
        """
    )
    if not count_rows and not time_rows:
        return ""
    by_name: dict[str, dict[str, int]] = {}
    for name, n_to, n_mo, n_sk, n_ok in count_rows:
        by_name[str(name)] = {
            "timeouts": int(n_to),
            "memouts": int(n_mo),
            "skipped": int(n_sk),
            "n_ok": int(n_ok),
        }
    for name, _rt in time_rows:
        by_name.setdefault(str(name), {"timeouts": 0, "memouts": 0, "skipped": 0, "n_ok": 0})
    from src.simplifier import DEFAULT_TACTIC

    rank: dict[str, int] = {}
    for i, raw in enumerate(DEFAULT_TACTIC.split(":")):
        rank.setdefault(raw, i)
    tail = len(rank) + 1
    ordered = sorted(by_name, key=lambda n: (rank.get(n, tail), n))
    fig = make_subplots(
        rows=1,
        cols=2,
        horizontal_spacing=0.06,
        column_widths=[0.55, 0.45],
        subplot_titles=("Wall time (completed runs)", "Timeouts / memouts / skipped"),
    )
    if time_rows:
        tdf = pandas.DataFrame(time_rows, columns=["name", "running_time"])
        tdf["name"] = tdf["name"].astype(str)
        fig.add_trace(
            go.Box(
                x=tdf["name"],
                y=tdf["running_time"],
                name="time (s)",
                marker_color="#636EFA",
                showlegend=False,
            ),
            row=1,
            col=1,
        )
    timeouts = [by_name[n]["timeouts"] for n in ordered]
    memouts = [by_name[n]["memouts"] for n in ordered]
    skipped = [by_name[n]["skipped"] for n in ordered]
    fig.add_trace(
        go.Bar(
            x=ordered,
            y=timeouts,
            name="timeouts",
            marker_color="#EF553B",
            offsetgroup=0,
            legendgroup="c",
        ),
        row=1,
        col=2,
    )
    fig.add_trace(
        go.Bar(
            x=ordered,
            y=memouts,
            name="memouts",
            marker_color="#F97316",
            offsetgroup=1,
            legendgroup="c",
        ),
        row=1,
        col=2,
    )
    fig.add_trace(
        go.Bar(
            x=ordered,
            y=skipped,
            name="skipped",
            marker_color="#FFA15A",
            offsetgroup=2,
            legendgroup="c",
        ),
        row=1,
        col=2,
    )
    fig.update_layout(
        title="Simplifier passes: time distribution vs timeout/memout/skip counts",
        barmode="group",
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="right", x=1),
    )
    fig.update_xaxes(categoryorder="array", categoryarray=ordered, tickangle=-35, row=1, col=1)
    fig.update_xaxes(categoryorder="array", categoryarray=ordered, tickangle=-35, row=1, col=2)
    fig.update_yaxes(title_text="time (s)", autorange=True, rangemode="normal", row=1, col=1)
    fig.update_yaxes(title_text="count", rangemode="tozero", row=1, col=2)
    return _fig_html(fig)


def _path_relative_to_base(path_str: str, base: Path) -> str:
    try:
        return str(Path(path_str).resolve().relative_to(base.resolve()))
    except ValueError:
        return path_str


def substeps_stacked_lines(input_base: Path) -> str:
    rows = query(
        f"""
        SELECT sub.verification_step_id, sub.name, COALESCE(sub.running_time, 0),
               v.input1, v.input2, v.status
        FROM substeps sub
        JOIN verification_steps v ON v.id = sub.verification_step_id
        WHERE sub.parent IS NULL
          AND sub.name IN ({_PASS_SOLVED_SUBSTEP_NAMES_SQL})
        """
    )
    if not rows:
        return ""
    meta = query(
        """
        SELECT id, input1, input2, status FROM verification_steps
        """
    )
    meta_by_id = {vid: (i1, i2, st) for vid, i1, i2, st in meta}
    rec: list[dict[str, object]] = []
    for vid, name, rt, _i1, _i2, _st in rows:
        series = _report_series_name(str(name))
        if series is None:
            continue
        i1, i2, status = meta_by_id.get(vid, (_i1, _i2, _st))
        rec.append(
            {
                "verification_step_id": vid,
                "series": series,
                "running_time": rt,
                "input1": _path_relative_to_base(str(i1), input_base),
                "input2": _path_relative_to_base(str(i2), input_base),
                "status": status,
            }
        )
    df = pandas.DataFrame(rec)
    df = df.groupby(["verification_step_id", "series"], as_index=False).agg(
        running_time=("running_time", "sum"),
        input1=("input1", "first"),
        input2=("input2", "first"),
        status=("status", "first"),
    )
    pt = df.pivot_table(
        index="verification_step_id",
        columns="series",
        values="running_time",
        aggfunc="sum",
        fill_value=0,
    )
    encode_series = pt["encode"] if "encode" in pt.columns else pandas.Series(0.0, index=pt.index)
    step_order = encode_series.sort_values(ascending=True).index.tolist()
    rank = {vid: i for i, vid in enumerate(step_order)}
    df["x_rank"] = df["verification_step_id"].map(rank)
    stack_order = [s for s in _PASS_SOLVED_SERIES_ORDER if s in df["series"].unique()]

    fig = plotly.express.bar(
        df,
        x="x_rank",
        y="running_time",
        color="series",
        category_orders={"series": stack_order},
        title="Substep time",
        labels={
            "x_rank": "Step order (sorted by encode time)",
            "running_time": "Time (s)",
            "series": "Substep",
            "input1": "Input file 1",
            "input2": "Input file 2",
            "verification_step_id": "Step id",
            "status": "Status",
        },
        hover_data=["verification_step_id", "input1", "input2", "status"],
    )
    fig.update_layout(barmode="stack", bargap=0)
    return _fig_html(fig)