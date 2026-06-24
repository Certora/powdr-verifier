"""Small HTML fragments shared across report views."""
import html
import shlex


def _command_for_copy(cmd: str) -> str:
    parts = shlex.split(cmd)
    out: list[str] = []
    skip = False
    for part in parts:
        if skip:
            skip = False
            continue
        if part in ("-j", "--jobs", "--run-id"):
            skip = True
            continue
        out.append(part)
    return shlex.join(out)


def copy_command_badge(cmd: str | None, *, title: str = "Copy command") -> str:
    if not cmd:
        return ""
    copy_cmd = _command_for_copy(cmd)
    return (
        f'<button type="button" class="badge text-bg-light border copy-cmd-badge" '
        f'title="{html.escape(title, quote=True)}" '
        f'data-copy-cmd="{html.escape(copy_cmd, quote=True)}" '
        f'onclick="navigator.clipboard.writeText(this.dataset.copyCmd).catch(()=>{{}})" '
        f'style="cursor:pointer;font-size:0.82em">⧉</button>'
    )
