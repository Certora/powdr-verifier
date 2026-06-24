"""Small HTML fragments shared across report views."""
import html
import json


def copy_command_badge(cmd: str | None, *, title: str = "Copy command") -> str:
    if not cmd:
        return ""
    return (
        f'<button type="button" class="badge text-bg-light border copy-cmd-badge" '
        f'title="{html.escape(title, quote=True)}" '
        f'onclick="navigator.clipboard.writeText({json.dumps(cmd)}).catch(()=>{{}})" '
        f'style="cursor:pointer;font-size:0.82em">⧉</button>'
    )
