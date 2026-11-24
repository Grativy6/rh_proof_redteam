"""Verify the deposited research inputs. The default check works offline."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen


def check(upstream=False):
    corpus = Path(__file__).resolve().parents[1] / "corpus"
    manifest = json.loads((corpus / "sources.json").read_text(encoding="utf-8"))
    for source in manifest["sources"]:
        data = (corpus / source["file"]).read_bytes()
        assert len(data) == source["bytes"], source["file"]
        assert hashlib.sha256(data).hexdigest() == source["sha256"], source["file"]
        if "git_blob" in source:
            header = b"blob " + str(len(data)).encode() + b"\0"
            assert hashlib.sha1(header + data).hexdigest() == source["git_blob"]
        else:
            assert "md5:" + hashlib.md5(data).hexdigest() == source["deposited_checksum"]
        if upstream:
            req = Request(source["upstream_url"], headers={"User-Agent": "PAL-RH-source-check"})
            with urlopen(req, timeout=60) as response:
                assert response.read() == data, source["file"]
    count = len(manifest["sources"])
    print(f"{count} inputs matched the local manifest.")
    if upstream:
        print("All ten original files also matched their upstream bytes.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", action="store_true", help="Also compare the original deposit bytes.")
    check(parser.parse_args().upstream)
