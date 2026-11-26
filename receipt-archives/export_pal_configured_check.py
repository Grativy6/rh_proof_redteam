"""Rebuild an independently specified local proof check from its compare.json.
Run lake build in pal-rh first. The reference sees only the pinned stock packages.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from export_pal_check import LEAN, MATHLIB, PROJECT
from replay_p_vs_np import EXPORT_FILES, EXPORT_PIN, PRIMITIVES, pinned_bytes


def export_fixed(config, project, lake, output):
    spec = json.loads(config.read_text(encoding="utf8"))
    stock = project/".lake/packages"
    rev = subprocess.check_output(["git","-C",str(stock/"mathlib"),"rev-parse","HEAD"],text=True).strip()
    assert rev == MATHLIB
    probe = "import os,shutil,json;print(json.dumps([shutil.which('lean'),os.environ['LEAN_PATH']]))"
    result = subprocess.check_output([str(lake),"env",sys.executable,"-c",probe],cwd=project,text=True)
    compiler,paths = json.loads(result.strip().splitlines()[-1])
    compiler = Path(compiler).resolve()
    search = [(project/p).resolve() for p in paths.split(os.pathsep) if p]
    stock_search = [p for p in search if p.is_relative_to(stock.resolve())]
    build = (project/".lake/build/lib/lean").resolve()
    assert stock_search and build in search and (build/"PALRH.olean").is_file()
    env = dict(os.environ,PATH=str(compiler.parent)+os.pathsep+os.environ.get("PATH",""))
    assert LEAN in subprocess.check_output([str(compiler),"--version"],env=env,text=True)
    output.mkdir(parents=True,exist_ok=True)
    receipts = {}
    with tempfile.TemporaryDirectory(prefix="pal-fixed-export-") as tmp:
        work = Path(tmp)
        exporter = work/"exporter"
        exporter.mkdir()
        for name,digest in EXPORT_FILES.items():
            (exporter/name).write_bytes(pinned_bytes("leanprover/lean4export",EXPORT_PIN,name,digest))
        subprocess.run([str(compiler),"-o","Export.olean","Export.lean"],cwd=exporter,
                       env=dict(env,LEAN_PATH=""),check=True)
        for role,libs in [("challenge",stock_search),("solution",search)]:
            module = spec[role+"_module"]
            stage = work/role
            stage.mkdir()
            shutil.copyfile(config.parent/(module+".lean"),stage/(module+".lean"))
            local = dict(env,LEAN_PATH=os.pathsep.join(map(str,[stage,*libs])))
            subprocess.run([str(compiler),"-j","2","-o",module+".olean",module+".lean"],
                           cwd=stage,env=local,check=True)
            qualified = dict(local,LEAN_PATH=str(exporter)+os.pathsep+local["LEAN_PATH"])
            with tempfile.NamedTemporaryFile(dir=output,delete=False) as stream:
                path = Path(stream.name)
                try:
                    subprocess.run([str(compiler),"-j","2","--run","Main.lean",module,"--",
                                    *spec["theorem_names"],*PRIMITIVES],cwd=exporter,env=qualified,
                                   stdout=stream,check=True)
                except BaseException:
                    stream.close()
                    path.unlink(missing_ok=True)
                    raise
            destination = output/(role+".ndjson")
            path.replace(destination)
            digest = hashlib.sha256()
            with destination.open("rb") as file:
                for block in iter(lambda:file.read(2**20),b""):
                    digest.update(block)
            receipts[role] = {"bytes":destination.stat().st_size,"sha256":digest.hexdigest()}
    print(json.dumps(receipts,indent=2))


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("config",type=Path)
    ap.add_argument("output",type=Path)
    ap.add_argument("--project",type=Path,default=PROJECT)
    ap.add_argument("--lake",default="lake")
    args=ap.parse_args()
    export_fixed(args.config.resolve(),args.project.resolve(),args.lake,args.output.resolve())
