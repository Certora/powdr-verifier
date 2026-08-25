import argparse
from io import BytesIO
import logging
import os
import platform
from pathlib import Path
import re
import requests
import zipfile

re_link = re.compile(r"<(https://api.github.com/[^>]+)>")


def _asset_pattern() -> str:
    # e.g. z3-*-x64-glibc*.zip on Linux, z3-*-arm64-osx*.zip on Apple Silicon
    arch = "arm64" if platform.machine().lower() in ("arm64", "aarch64") else "x64"
    system = platform.system()
    if system == "Linux":
        return rf"z3-.*-{arch}-glibc.*\.zip"
    if system == "Darwin":
        return rf"z3-.*-{arch}-osx.*\.zip"
    raise RuntimeError(f"no known z3 release asset pattern for {system}/{arch}")


re_asset = re.compile(_asset_pattern())

SDK_REL_PATHS = frozenset({"bin/z3", "bin/libz3.so", "bin/libz3.a", "bin/libz3.dylib"})

parser = argparse.ArgumentParser()
parser.add_argument("version")
parser.add_argument("--bindir", type=Path, required=True)
parser.add_argument("--sdk", type=Path)
args = parser.parse_args()
args.bindir = args.bindir.expanduser()
if args.sdk is not None:
    args.sdk = args.sdk.expanduser()


def _github_api_headers() -> dict[str, str]:
    # raises the api.github.com rate limit from 60/hour to 1000/hour
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    return {"Authorization": f"Bearer {token}"} if token else {}


def get_api_json(url: str):
    r = requests.get(url, headers=_github_api_headers())
    if r.status_code != 200:
        raise Exception(f"Failed to get {url}: {r.status_code}")
    return r.json(), r.headers.get("Link", "")


def get_all_releases():
    seen = set()
    todo = set(["https://api.github.com/repos/Z3Prover/z3/releases"])

    res = []

    while len(todo) > 0:
        url = todo.pop()
        if url in seen:
            continue
        seen.add(url)
        releases, links = get_api_json(url)
        res.extend(releases)
        todo |= set(re_link.findall(links))

    return res


def fetch_release_zip(url: str) -> zipfile.ZipFile:
    logging.warning("downloading %s...", url)
    r = requests.get(url)
    if r.status_code != 200:
        raise Exception(f"Failed to download {url}: {r.status_code}")
    return zipfile.ZipFile(BytesIO(r.content))


def zip_root_prefix(names: list[str]) -> str:
    return names[0].split("/", 1)[0] + "/"


def zip_relpath(member: str, root_prefix: str) -> str:
    if member.startswith(root_prefix):
        return member[len(root_prefix) :]
    return member


def release_name(tag: str) -> str:
    return "z3-nightly" if tag == "Nightly" else tag


def download_and_extract_binary(url: str, target: Path):
    if target.exists():
        logging.warning("%s already exists, skipping...", target)
        return
    logging.warning("unpacking to %s...", target)
    with fetch_release_zip(url) as archive:
        for member in archive.namelist():
            if member.endswith("bin/z3"):
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(archive.read(member))
                target.chmod(0o755)
                return
    raise FileNotFoundError(f"bin/z3 not found in {url}")


def install_bin_link(prefix: Path, name: str, bindir: Path):
    src = (prefix / "bin" / "z3").resolve()
    dest = bindir / name
    bindir.mkdir(parents=True, exist_ok=True)
    if dest.exists() or dest.is_symlink():
        dest.unlink()
    dest.symlink_to(src)
    logging.warning("linked %s -> %s", dest, src)


def download_and_extract_sdk(url: str, prefix: Path, bin_name: str):
    marker = prefix / ".installed"
    if marker.is_file():
        logging.warning("%s already installed, skipping...", prefix)
    else:
        logging.warning("unpacking sdk to %s...", prefix)
        with fetch_release_zip(url) as archive:
            names = archive.namelist()
            if not names:
                raise FileNotFoundError(f"empty archive from {url}")
            root = zip_root_prefix(names)
            for member in names:
                rel = zip_relpath(member, root)
                if rel in SDK_REL_PATHS or rel.startswith("include/"):
                    dest = prefix / rel
                    if member.endswith("/"):
                        continue
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes(archive.read(member))
                    if rel == "bin/z3":
                        dest.chmod(0o755)
        marker.write_text(url + "\n", encoding="utf-8")
    install_bin_link(prefix, bin_name, args.bindir)


def release_asset_url(release: dict) -> str | None:
    for asset in release["assets"]:
        if re_asset.match(asset["name"]) is not None:
            return asset["browser_download_url"]
    return None


def download_release_asset(*releases: dict):
    for release in releases:
        name = release_name(release["tag_name"])
        url = release_asset_url(release)
        if url is None:
            continue
        if args.sdk is not None:
            download_and_extract_sdk(url, args.sdk, name)
        else:
            download_and_extract_binary(url, args.bindir / name)


def _already_installed() -> bool:
    # "all"/"latest" need the API; a concrete tag can be checked on disk
    if args.version in ("all", "latest"):
        return False
    if args.sdk is not None:
        return (args.sdk / ".installed").is_file()
    return (args.bindir / args.version).exists()


if _already_installed():
    logging.warning("%s already installed, skipping download", args.version)
    if args.sdk is not None:
        install_bin_link(args.sdk, args.version, args.bindir)
else:
    logging.warning("downloading %s...", args.version)
    match args.version:
        case "all":
            download_release_asset(*get_all_releases())

        case "latest":
            release, _ = get_api_json(
                "https://api.github.com/repos/Z3Prover/z3/releases/latest"
            )
            download_release_asset(release)

        case _:
            release, _ = get_api_json(
                f"https://api.github.com/repos/Z3Prover/z3/releases/tags/{args.version}"
            )
            download_release_asset(release)
