"""Small HTML fragments shared across report views."""
import html


def copy_command_badge(cmd: str | None, *, title: str = "Copy command") -> str:
    if not cmd:
        return ""
    return (
        f'<button type="button" class="badge text-bg-light border copy-cmd-badge" '
        f'title="{html.escape(title, quote=True)}" '
        f'data-copy-cmd="{html.escape(cmd, quote=True)}" '
        f'onclick="navigator.clipboard.writeText(this.dataset.copyCmd).catch(()=>{{}})" '
        f'style="cursor:pointer;font-size:0.82em">⧉</button>'
    )
