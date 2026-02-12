import argparse
from io import BytesIO
import logging
from pathlib import Path
import re
import requests
import zipfile

re_link = re.compile(r'<(https://api.github.com/[^>]+)>')
re_asset = re.compile(r'z3-.*-x64-glibc.*\.zip')

parser = argparse.ArgumentParser()
parser.add_argument('version', type=str)
parser.add_argument('target', type=Path, default=Path("~/bin").expanduser())
args = parser.parse_args()
assert args.target.is_dir()

def get_api_json(url: str):
    r = requests.get(url)
    if r.status_code != 200:
        raise Exception(f"Failed to get {url}: {r.status_code}")
    return r.json(), r.headers.get('Link', '')

def get_all_releases():
    seen = set()
    todo = set(["https://api.github.com/repos/Z3Prover/z3/releases"])

    res = []

    while len(todo) > 0:
        url = todo.pop()
        if url in seen:
            continue
        seen.add(url)
        releases,links = get_api_json(url)
        res.extend(releases)
        todo |= set(re_link.findall(links))
    
    return res

def download_and_extract_asset(url: str, target: Path):
    if target.exists():
        logging.warning(f'{target} already exists, skipping...')
        return
    logging.warning(f'downloading {url}...')
    r = requests.get(url)
    if r.status_code != 200:
        raise Exception(f"Failed to download {url}: {r.status_code}")
    
    data = BytesIO(r.content)
    logging.warning(f'unpacking to {target}...')
    with zipfile.ZipFile(data) as zip:
        for member in zip.namelist():
            if member.endswith('bin/z3'):
                with open(target, 'wb') as f:
                    f.write(zip.read(member))
                break

def download_release_asset(*releases: dict):
    for release in releases:
        name = release['tag_name']
        if name in ['Nightly']:
            continue
        for asset in release['assets']:
            if re_asset.match(asset['name']) is not None:
                download_and_extract_asset(asset['browser_download_url'], args.target / release['tag_name'])
                break


logging.warning(f'downloading {args.version}...')
match args.version:
    case 'all':
        download_and_extract_asset(*get_all_releases())

    case 'latest':
        release,_ = get_api_json("https://api.github.com/repos/Z3Prover/z3/releases/latest")
        download_release_asset(release)

    case _:
        release,_ = get_api_json(f"https://api.github.com/repos/Z3Prover/z3/releases/tags/{args.version}")
        download_release_asset(release)
