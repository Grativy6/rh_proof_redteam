"""Verify the research inputs. The default check works offline."""
import argparse
import hashlib
import json
import time
from pathlib import Path
from urllib.request import Request, urlopen
from zipfile import ZipFile


def read_upstream(url):
    request = Request(url, headers={"User-Agent": "PAL-RH-source-check"})
    for attempt in range(3):
        try:
            with urlopen(request, timeout=30) as response:
                return response.read()
        except OSError:
            if attempt == 2:
                raise
            time.sleep(attempt + 1)


def check(upstream=False, shelf=None):
    corpus = Path(__file__).resolve().parents[1] / "corpus"
    sources = json.loads((corpus / "sources.json").read_text(encoding="utf-8"))["sources"]
    entries = {entry["file"]: entry for entry in sources}
    assert len(entries) == len(sources), "Duplicate source path"
    direct = members = author = 0
    for source in sources:
        name = source["file"]
        data = (corpus / name).read_bytes()
        assert len(data) == source["bytes"] and hashlib.sha256(data).hexdigest() == source["sha256"], name
        if "archive_member" in source:
            package = source["archive"]
            assert "upstream_url" in entries[package], package
            with ZipFile(corpus / package) as archive:
                assert archive.read(source["archive_member"]) == data, name
            members += 1
        elif source.get("source_kind") == "author-supplied":
            if shelf is not None:
                assert (shelf / source["shelf_path"]).read_bytes() == data, name
            author += 1
        else:
            if "git_blob" in source:
                header = b"blob " + str(len(data)).encode() + b"\0"
                assert hashlib.sha1(header + data).hexdigest() == source["git_blob"], name
            else:
                assert "md5:" + hashlib.md5(data).hexdigest() == source["deposited_checksum"], name
            if upstream:
                assert read_upstream(source["upstream_url"]) == data, name
            direct += 1

    context = corpus / "context-stack"
    for name in ("v0.1", "v0.2", "v0.3"):
        record = json.loads((context / f"Blob_Weld_Investigative_PCP_{name}_manifest.json").read_text(encoding="utf-8-sig"))
        for filename, digest in record["files"].items():
            assert hashlib.sha256((context / filename).read_bytes()).hexdigest() == digest, filename
        if "prior_draft_sha256" in record:
            prior = context / "Blob_Weld_Investigative_PCP_v0.2_DRAFT.txt"
            assert hashlib.sha256(prior.read_bytes()).hexdigest() == record["prior_draft_sha256"]
    print(f"{len(sources)} inputs matched the local manifest, including {members} package members.")
    if upstream:
        print(f"{direct} files also matched their upstream bytes; {members} members matched those packages.")
    if shelf is not None:
        print(f"{author} author-supplied files also matched the supplied source shelf.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", action="store_true", help="Compare the deposited files and pinned public source online.")
    parser.add_argument("--shelf", type=Path, help="Compare author-supplied files with the original Corpus directory.")
    args = parser.parse_args()
    check(args.upstream, args.shelf)
