"""Rebuild the printable project history and its square-trace figure.

Run from any directory with Python, ReportLab and the DejaVu fonts installed.
Set DEJAVU_FONT_DIR if the fonts are outside these standard locations.
"""

from datetime import datetime, timezone
from html import escape
import os
from pathlib import Path
import posixpath
import re
from urllib.parse import quote, urlsplit, urlunsplit

from reportlab.graphics import renderSVG
from reportlab.graphics.shapes import Circle, Drawing, Line, Rect, String
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    BaseDocTemplate, Frame, KeepTogether, PageTemplate, Paragraph,
    Preformatted, Spacer, Table, TableStyle,
)

ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
STEM = "where-the-carry-goes"
FIGURE = "figures/board-eight-square-traces.svg"
SNAPSHOT = "2a1916e287b6276c43c753a9c304427df408a985"
SOURCE_ROOT = "https://github.com/Grativy6/rh_proof_redteam/blob/" + SNAPSHOT + "/"
TITLE = "Where the carry goes"
INK = colors.HexColor("#192c36")
TEAL = colors.HexColor("#17595b")
MUTED = colors.HexColor("#465a62")
RULE = colors.HexColor("#bccbcc")
PALE = colors.HexColor("#f1f6f5")
OCHRE = colors.HexColor("#9a542a")
PAGE_WIDTH, PAGE_HEIGHT = letter
MARGIN = 66
WIDTH = PAGE_WIDTH - 2 * MARGIN
BACKTICK = chr(96)
LINK = r"\[([^\]]+)\]\(([^)\s]+)\)"
END_SOURCES = re.compile(r" ((" + LINK + r")(?: · " + LINK + r")*)$")


def fonts():
    locations = [
        Path(os.environ.get("DEJAVU_FONT_DIR", ".")),
        Path("/usr/share/fonts/truetype/dejavu"),
        Path("/usr/local/share/fonts/dejavu"),
        Path(os.environ.get("WINDIR", "C:/Windows")) / "Fonts",
        Path.home() / "Library/Fonts", Path("/Library/Fonts"),
    ]
    root = next((p for p in locations if (p / "DejaVuSerif.ttf").is_file()), None)
    if root is None:
        raise SystemExit("Set DEJAVU_FONT_DIR to the directory containing the DejaVu TTF family.")
    for family, italic in [("DejaVuSerif", "Italic"), ("DejaVuSans", "Oblique"),
                           ("DejaVuSansMono", "Oblique")]:
        names = [family + suffix for suffix in ("", "-Bold", "-" + italic, "-Bold" + italic)]
        for name in names:
            pdfmetrics.registerFont(TTFont(name, str(root / (name + ".ttf"))))
        pdfmetrics.registerFontFamily(family, normal=names[0], bold=names[1],
                                      italic=names[2], boldItalic=names[3])


def public_link(target):
    if urlsplit(target).scheme or target.startswith("#"):
        return target
    parts = urlsplit(target)
    path = posixpath.normpath(posixpath.join("papers", parts.path))
    if path.startswith("../"):
        raise ValueError("Link leaves the repository: " + target)
    return SOURCE_ROOT + urlunsplit(("", "", quote(path), parts.query, parts.fragment))


def inline(raw):
    # Preserve literal code and link destinations when applying emphasis.
    objects = []

    def hold(html):
        objects.append(html)
        return f"\x1f{len(objects) - 1}\x1f"

    raw = re.sub(BACKTICK + "([^" + BACKTICK + "]+)" + BACKTICK,
                 lambda m: hold('<font name="DejaVuSansMono" size="8.4">'
                                + escape(m[1]) + "</font>"), raw)
    raw = re.sub(LINK, lambda m: hold('<a color="#17595b" href="'
                                      + escape(public_link(m[2]), quote=True) + '">'
                                      + inline(m[1]) + "</a>"), raw)
    raw = escape(raw)
    for tag in ("sup", "sub", "/sup", "/sub"):
        raw = raw.replace("&lt;" + tag + "&gt;", "<" + tag + ">")
    raw = re.sub(r"\*\*(.+?)\*\*", r"<b>\1</b>", raw)
    raw = re.sub(r"(?<!\w)\*([^*]+)\*(?!\w)", r"<i>\1</i>", raw)
    raw = raw.replace("ℓ", '<font name="DejaVuSans">ℓ</font>')
    # Links can contain an inline-code label, which creates a nested slot.
    while "\x1f" in raw:
        raw = re.sub(r"\x1f(\d+)\x1f", lambda m: objects[int(m[1])], raw)
    return raw


def trace_figure():
    end = 4096
    start = 2 * end / 3

    def marks(center):
        return {center**2 - t**2 for t in range(1, center - 1)
                if 2 * end < 3 * (center**2 - t**2) <= 3 * end}

    a, b = marks(64), marks(65)
    assert (len(a), len(b), a & b, len(a | b)) == (36, 27, {3696}, 62)
    drawing = Drawing(WIDTH, 138)
    drawing.add(Rect(0, 0, WIDTH, 138, fillColor=colors.white, strokeColor=RULE, strokeWidth=0.65))
    x1, x2 = 63, WIDTH - 22

    def x(value):
        return x1 + (value - start) * (x2 - x1) / (end - start)

    def label(px, py, string, size=8, color=MUTED, align="start", bold=False):
        drawing.add(String(px, py, string, fontName="DejaVuSans-Bold" if bold else "DejaVuSans",
                           fontSize=size, fillColor=color, textAnchor=align))

    label(13, 118, "Composite positions on board eight", size=11, color=INK, bold=True)
    for h, name, entries, color in [(82, "64² − t²", a, TEAL), (54, "65² − t²", b, OCHRE)]:
        label(12, h - 3, name, size=9, color=color, bold=True)
        drawing.add(Line(x1, h, x2, h, strokeColor=RULE, strokeWidth=0.6))
        for mark in sorted(entries):
            drawing.add(Line(x(mark), h - 5, x(mark), h + 5, strokeColor=color, strokeWidth=1))
    common = x(3696)
    drawing.add(Line(common, 45, common, 101, strokeColor=INK, strokeWidth=0.75,
                     strokeDashArray=[2, 2]))
    for y in (54, 82):
        drawing.add(Circle(common, y, 3, strokeColor=INK, fillColor=colors.white, strokeWidth=1.2))
    label(common, 103, "3696", size=8, color=INK, align="middle", bold=True)
    drawing.add(Line(x1, 32, x2, 32, strokeColor=MUTED, strokeWidth=0.6))
    for tick in (2800, 3200, 3600, 4096):
        px = x(tick)
        drawing.add(Line(px, 28, px, 32, strokeColor=MUTED, strokeWidth=0.6))
        label(px, 15, str(tick), align="middle")
    return drawing


def style(name, **values):
    options = dict(fontName="DejaVuSerif", fontSize=10.6, leading=15.8, textColor=INK,
                   spaceAfter=7.5, alignment=TA_LEFT, allowWidows=0, allowOrphans=0)
    options.update(values)
    return ParagraphStyle(name, **options)


BODY = style("Body")
HEAD = style("Section", fontName="DejaVuSans-Bold", fontSize=17, leading=21,
             spaceBefore=13, spaceAfter=8, keepWithNext=1)
TITLE_STYLE = style("Title", fontName="DejaVuSerif-Bold", fontSize=35, leading=41,
                    spaceAfter=9, keepWithNext=1)
DECK = style("Deck", fontName="DejaVuSans", fontSize=14, leading=19,
             textColor=TEAL, spaceAfter=12, keepWithNext=1)
META = style("Credit", fontName="DejaVuSans", fontSize=9, leading=13,
             textColor=MUTED, spaceAfter=12, keepWithNext=1)
INTRO_FORMULA = style("Lead to a calculation", keepWithNext=1)
FORMULA = style("Formula", fontSize=12, leading=18, leftIndent=16,
                spaceBefore=3, spaceAfter=10)
CAPTION = style("Caption", fontName="DejaVuSans", fontSize=8.1, leading=11.8,
                textColor=MUTED, spaceBefore=5, spaceAfter=9)
CODE = style("Code", fontName="DejaVuSansMono", fontSize=8.8, leading=14,
             leftIndent=14, spaceBefore=3, spaceAfter=10)
CELL = style("Cell", fontName="DejaVuSans", fontSize=8.5, leading=12.4, spaceAfter=0)
CELL_HEAD = style("Column", fontName="DejaVuSans-Bold", fontSize=8.5, leading=12.4,
                  textColor=TEAL, spaceAfter=0)


class Paper(BaseDocTemplate):
    def afterFlowable(self, item):
        if getattr(item, "outline_title", None):
            key = item.outline_title.lower().replace(" ", "-")
            self.canv.bookmarkHorizontalAbsolute(key, self.frame._y + item.height)
            self.canv.addOutlineEntry(item.outline_title, key, 0, closed=False)


def running_head(canvas, doc):
    canvas.saveState()
    canvas.setTitle(TITLE)
    canvas.setAuthor("Christopher Daniel Pang and Hearthline (Codex)")
    canvas.setSubject("The PAL audit, its mathematical results and its independent RH construction")
    canvas.setFont("DejaVuSans", 8)
    canvas.setFillColor(MUTED)
    canvas.drawString(MARGIN, PAGE_HEIGHT - 35, "PAL  /  MATHEMATICAL REALIZATION ATLAS")
    canvas.drawRightString(PAGE_WIDTH - MARGIN, PAGE_HEIGHT - 35, "26 November 2026")
    canvas.setStrokeColor(RULE)
    canvas.setLineWidth(0.55)
    canvas.line(MARGIN, PAGE_HEIGHT - 43, PAGE_WIDTH - MARGIN, PAGE_HEIGHT - 43)
    canvas.line(MARGIN, 43, PAGE_WIDTH - MARGIN, 43)
    canvas.drawString(MARGIN, 29, "Where the carry goes")
    canvas.drawRightString(PAGE_WIDTH - MARGIN, 29, str(doc.page))
    canvas.restoreState()


def table(rows):
    data = [[Paragraph(inline(c), CELL_HEAD if i == 0 else CELL) for c in r]
            for i, r in enumerate(rows)]
    parts = (.20, .80) if len(data[0]) == 2 else (.225, .405, .37)
    t = Table(data, colWidths=[WIDTH * w for w in parts], repeatRows=1, hAlign="LEFT")
    t.setStyle(TableStyle([
        ("VALIGN", (0, 0), (-1, -1), "TOP"),
        ("BACKGROUND", (0, 0), (-1, 0), PALE),
        ("LINEBELOW", (0, 0), (-1, 0), 0.9, TEAL),
        ("LINEBELOW", (0, 1), (-1, -1), 0.4, RULE),
        ("LEFTPADDING", (0, 0), (-1, -1), 6),
        ("RIGHTPADDING", (0, 0), (-1, -1), 6),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
    ]))
    return t


def content(source, chart):
    story = []
    lines = source.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        i += 1
        if not line:
            continue
        if line.startswith("# "):
            story.append(Paragraph(inline(line[2:]), TITLE_STYLE))
        elif line.startswith("## "):
            heading = Paragraph(inline(line[3:]), HEAD)
            heading.outline_title = line[3:]
            story.append(heading)
        elif i <= 5:
            story.append(Paragraph(inline(line.strip("*")), DECK if line.startswith("**") else META))
        elif line.startswith(BACKTICK * 3):
            end = lines.index(BACKTICK * 3, i)
            story.append(Preformatted("\n".join(lines[i:end]), CODE))
            i = end + 1
        elif line.startswith("|"):
            block = [line]
            while i < len(lines) and lines[i].startswith("|"):
                block.append(lines[i])
                i += 1
            rows = [[c.strip() for c in row[1:-1].split("|")] for row in block]
            story.extend([table([rows[0], *rows[2:]]), Spacer(1, 9)])
        elif line.startswith("!["):
            if not line.endswith("(" + FIGURE + ")"):
                raise ValueError("Unknown illustration: " + line)
            while i < len(lines) and not lines[i].strip():
                i += 1
            caption = lines[i].strip().strip("*")
            if not caption.startswith("Figure 1."):
                raise ValueError("Missing square-trace caption")
            story.append(KeepTogether([chart, Paragraph(inline(caption), CAPTION)]))
            i += 1
        elif line.startswith("> "):
            story.append(Paragraph(inline(line[2:]), FORMULA))
        else:
            sources = END_SOURCES.search(line)
            if sources:
                source_line = '<br/><font name="DejaVuSans" size="7.8" color="#17595b">'
                paragraph = inline(line[:sources.start()]) + source_line + inline(sources[1]) + "</font>"
                story.append(Paragraph(paragraph, BODY))
            else:
                next_is_formula = i + 1 < len(lines) and lines[i + 1].startswith("> ")
                story.append(Paragraph(inline(line), INTRO_FORMULA if next_is_formula else BODY))
    return story


def main():
    epoch = datetime(2026, 11, 26, tzinfo=timezone.utc).timestamp()
    os.environ.setdefault("SOURCE_DATE_EPOCH", str(int(epoch)))
    fonts()
    chart = trace_figure()
    target = PAPERS / FIGURE
    target.parent.mkdir(exist_ok=True)
    renderSVG.drawToFile(chart, str(target))
    svg = target.read_text(encoding="utf-8")
    svg = svg.replace("<title>...</title>", "<title>Composite positions on board eight</title>")
    svg = svg.replace("<desc>...</desc>", "<desc>36 marks from 64 squared and 27 from 65 squared "
                      "share exactly one position, 3696.</desc>")
    target.write_text(svg, encoding="utf-8", newline="\n")
    source = (PAPERS / (STEM + ".md")).read_text(encoding="utf-8")
    doc = Paper(str(PAPERS / (STEM + ".pdf")), pagesize=letter,
                title=TITLE, author="Christopher Daniel Pang and Hearthline (Codex)")
    frame = Frame(MARGIN, 55, WIDTH, PAGE_HEIGHT - 113, leftPadding=0,
                  bottomPadding=0, rightPadding=0, topPadding=0, id="text")
    doc.addPageTemplates([PageTemplate(id="paper", frames=[frame], onPage=running_head)])
    doc.build(content(source, chart))


if __name__ == "__main__":
    main()
