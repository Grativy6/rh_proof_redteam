"""Plot the rigorous lower curves using the saved integer endpoint enclosures.
Requires matplotlib. All decisions about the sign are made by the rational replay.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
from check_pal_primitive_mesh import curvature


def draw(mesh,where):
    nodes = [(n,m,Q(l),Q(u)) for n,m,l,u in mesh["endpoint_receipts"]]
    xs=[]; floors=[]; chords=[]
    for (a,ma,la,ua),(b,mb,lb,ub) in zip(nodes,nodes[1:]):
        E=curvature(a,b,ma,mb)
        for k in range(65):
            h=Q(k,64)
            t=float(a+(b-a)*h)
            chord=(1-h)*la+h*lb
            xs.append(t)
            floors.append(float(chord-E*h*(1-h))/t**0.5)
            chords.append(float(chord)/t**0.5)
    fig,(main,zoom)=plt.subplots(1,2,figsize=(10.8,4.05),width_ratios=[1.65,1],layout="constrained")
    fig.patch.set_facecolor("#fbfaf7")
    for ax in (main,zoom):
        ax.set_facecolor("#fbfaf7")
        ax.fill_between(xs,0,floors,color="#b7d9ca",alpha=.82,linewidth=0)
        ax.plot(xs,floors,color="#17604c",linewidth=1.15,label="Proved lower bound")
        ax.plot(xs,chords,color="#795336",linestyle="--",linewidth=1.05,label="Straight chord between endpoint bounds")
        ax.axhline(0,color="#333833",linewidth=.85)
        ax.set_ylim(-4,200)
        ax.grid(axis="y",color="#dedfd7",lw=.6)
        ax.spines[["top","right","left"]].set_visible(False)
        ax.tick_params(length=0,labelsize=9)
        ax.set_axisbelow(True)
    main.set_xscale("log")
    main.set_xlim(nodes[0][0],nodes[-1][0])
    main.set_xticks([1e9,1e10,1e11,1e12],["1B","10B","100B","1T"])
    main.set_xlabel("Physical input, logarithmic scale")
    main.set_ylabel(r"Primitive in units of $\sqrt{t}$")
    main.set_title("Continuous coverage",loc="left",fontweight="bold",fontsize=12)
    a,b=mesh["weakest_panel"]
    zoom.set_xlim(a,b)
    zoom.set_xticks([a,(a+b)//2,b])
    zoom.xaxis.set_major_formatter(FuncFormatter(lambda x,_:f"{x/1e12:.3f}T"))
    zoom.set_title("Least margin, final interval",loc="left",fontweight="bold",fontsize=12)
    zoom.set_xlabel("Physical input, linear scale")
    zoom.text(.52,.20,"Above 9.50 throughout",transform=zoom.transAxes,
              fontsize=9,color="#124f3f",ha="center",
              bbox=dict(boxstyle="round,pad=.25",fc="#fbfaf7",ec="none"))
    main.legend(loc="lower left",fontsize=8,frameon=False)
    where.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(where,dpi=170)
    plt.close(fig)


if __name__ == "__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("record",type=Path)
    cli.add_argument("output",type=Path)
    args=cli.parse_args()
    draw(json.loads(args.record.read_text(encoding="utf8"))["continuum_mesh"],args.output)
