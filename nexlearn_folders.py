"""Glass folder cards for Streamlit (a Custom Component v2).

The folder itself is a React + TypeScript + Tailwind component (frontend/src/components/ui/glass-folder-cards.tsx).
`npm run build` in ./frontend bundles it into two files in frontend/dist, and this module hands them to
Streamlit as an inline component. Running the app does not need Node.js: only rebuilding the frontend does.
"""

from __future__ import annotations

import os

import streamlit as st

_DIST = os.path.join(os.path.dirname(os.path.abspath(__file__)), "frontend", "dist")


def _read(name: str) -> str:
    try:
        with open(os.path.join(_DIST, name), "r", encoding="utf-8") as fh:
            return fh.read()
    except OSError:
        return ""


_JS = _read("nexlearn-folders.js")
_CSS = _read("nexlearn-folders.css")

# Declared once, at import time (re-declaring a component by name inside a function misbehaves).
_COMPONENT = (
    st.components.v2.component(
        "nexlearn_folders",
        html="<div data-nexlearn-root></div>",
        css=_CSS,
        js=_JS,
        isolate_styles=True,
    )
    if _JS
    else None
)


def available() -> bool:
    """False if the frontend has not been built yet (the page then simply skips the folders)."""
    return _COMPONENT is not None


def glass_folders(folders: list[dict], *, key: str, width: int = 340, height: int = 380):
    """Draws one or more folders. Each folder is a dict:

        {"id": "notes", "label": "My Notes", "meta": "8 notes", "tone": "dark",
         "art": "aurora" | "ember" | "dusk" | "glacier" | "verdant" | "none",
         "files": [{"name": "Chapter 2", "meta": "Oct 8", "art": "dusk"}, ...]}

    Returns the clicked file, `{"folder": id, "name": ..., "index": ...}`, on the run it was clicked in, else None.
    """
    if _COMPONENT is None:
        return None
    result = _COMPONENT(
        data={"folders": folders, "width": width},
        key=key,
        height=height,
        on_file_change=lambda: None,  # makes `result.file` always exist
    )
    return result.file if result is not None else None
