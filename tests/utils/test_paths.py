"""Path (de)serialization for JSON reports (``src.paths`` + the ``__Path`` codec)."""
import io
import json
from pathlib import Path

from src.paths import (
    WORKSPACE_DIR,
    dump_input_abspath,
    dump_input_relpath,
)
from src.utils.io import dump_json, load_json


class TestDumpInputRelpath:
    def test_outside_workspace_stays_absolute(self):
        """A path outside the workspace (e.g. a scratch/tmp output dir) must not
        raise -- it is kept absolute and round-trips through dump_input_abspath."""
        ext = Path("/tmp/scratch/v.completeness.smt2")
        rel = dump_input_relpath(ext)
        assert rel.is_absolute()
        assert dump_input_abspath(str(rel)) == ext.resolve()

    def test_inside_workspace_is_relative(self):
        inside = WORKSPACE_DIR / "verifier" / "reports" / "x.json"
        assert dump_input_relpath(inside) == Path("verifier/reports/x.json")

    def test_powdr_dumps_normalization_preserved(self):
        pd = WORKSPACE_DIR / "verifier" / "powdr-dumps" / "g" / "a.json"
        assert dump_input_relpath(pd) == Path("verifier/powdr-dumps/g/a.json")


class TestJsonPathRoundTrip:
    def test_report_with_outside_path_serializes(self):
        """A report holding a Path outside the workspace serializes without error
        and decodes back to the resolved absolute path."""
        ext = Path("/tmp/scratch/report/v.smt2")
        buf = io.StringIO()
        dump_json({"outputs": [ext]}, buf)
        buf.seek(0)
        decoded = load_json(buf)
        assert decoded["outputs"][0] == ext.resolve()
