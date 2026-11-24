#!/usr/bin/env python3
"""Render the mathematical companion with embedded fonts and vector mathematics.

Requires pandoc on PATH. No TeX installation or network connection is used.
Formula placeholders exist only in a temporary directory: the PDF canvas draws
the MathText glyphs and fraction rules directly as text and vector primitives.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

import matplotlib
from matplotlib.font_manager import FontProperties
from matplotlib.mathtext import MathTextParser
from PIL import Image
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas
from reportlab.platypus import (
    BaseDocTemplate, Flowable, Frame, ListFlowable, ListItem, PageTemplate,
    Paragraph, Spacer, Table, TableStyle, KeepTogether,
)


# Fixed document date makes the publication artifact reproducible.
os.environ['SOURCE_DATE_EPOCH'] = '1795478400'  # 2026-11-24 00:00:00 UTC

matplotlib.rcParams['mathtext.fontset'] = 'dejavuserif'
matplotlib.rcParams['mathtext.default'] = 'it'
matplotlib.rcParams['mathtext.fallback'] = 'stix'
FONTS = Path(matplotlib.get_data_path()) / 'fonts' / 'ttf'
FONT_PATHS: dict[str, str] = {}


def register_font(path: str | Path, name: str | None = None) -> str:
    path = str(path)
    if path in FONT_PATHS:
        return FONT_PATHS[path]
    name = name or 'Math' + hashlib.sha256(path.encode()).hexdigest()[:16]
    pdfmetrics.registerFont(TTFont(name, path))
    FONT_PATHS[path] = name
    return name


for label, filename in [
    ('Body', 'DejaVuSerif.ttf'), ('BodyBold', 'DejaVuSerif-Bold.ttf'),
    ('BodyItalic', 'DejaVuSerif-Italic.ttf'),
    ('BodyBoldItalic', 'DejaVuSerif-BoldItalic.ttf'),
    ('Code', 'DejaVuSansMono.ttf'),
]:
    register_font(FONTS / filename, label)
pdfmetrics.registerFontFamily(
    'Body', normal='Body', bold='BodyBold', italic='BodyItalic',
    boldItalic='BodyBoldItalic',
)
pdfmetrics.registerFontFamily('Code', normal='Code', bold='Code', italic='Code')


def math_syntax(value: str) -> str:
    """Normalize equivalent TeX spellings accepted by Matplotlib MathText."""
    value = re.sub(r'\\(mathbb|mathcal|mathrm|mathbf|mathit|overline|widetilde)\s+([A-Za-z])',
                   lambda m: '\\' + m[1] + '{' + m[2] + '}', value)
    value = re.sub(r'\\(?:bigl|bigr|Bigl|Bigr|big|Big|bigg|Bigg)\b', '', value)
    for before, after in [
        ('lVert', 'Vert'), ('rVert', 'Vert'), ('lvert', 'vert'), ('rvert', 'vert'),
        ('ne', 'neq'), ('le', 'leq'), ('ge', 'geq'), ('to', 'rightarrow'),
    ]:
        value = re.sub(r'\\' + before + r'(?![A-Za-z])', r'\\' + after, value)
    return value.replace('\n', ' ')


class MathCache:
    def __init__(self, directory: Path):
        self.directory = directory
        self.parser = MathTextParser('path')
        self.records: dict[str, object] = {}
        self.expressions: list[dict] = []

    def get(self, text: str, size: float):
        normalized = math_syntax(text)
        key = hashlib.sha256(f'{size}:{normalized}'.encode()).hexdigest()
        filename = str(self.directory / (key + '.png'))
        if filename not in self.records:
            parsed = self.parser.parse('$' + normalized + '$', dpi=72,
                                       prop=FontProperties(size=size))
            for font, _, _, _, _ in parsed.glyphs:
                register_font(font.fname)
            self.records[filename] = parsed
            Image.new('RGBA', (1, 1), (255, 255, 255, 0)).save(filename)
            self.expressions.append({'source': text, 'normalized': normalized,
                                     'size': size, 'width': float(parsed.width),
                                     'height': float(parsed.height),
                                     'depth': float(parsed.depth)})
        return filename, self.records[filename]

    def inline(self, text: str, size: float) -> str:
        filename, parsed = self.get(text, size)
        return (f'<img src="{html.escape(filename, quote=True)}" '
                f'width="{parsed.width:.4f}" height="{parsed.height:.4f}" '
                f'valign="{-parsed.depth:.4f}"/>')

    @staticmethod
    def draw(canvas: Canvas, parsed, x: float, y: float, scale: float = 1):
        canvas.saveState()
        canvas.translate(x, y)
        canvas.scale(scale, scale)
        canvas.setFillColor(colors.black)
        for font, fontsize, number, ox, oy in parsed.glyphs:
            canvas.setFont(register_font(font.fname), fontsize)
            canvas.drawString(float(ox), float(parsed.depth + oy), chr(number))
        for ox, oy, width, height in parsed.rects:
            canvas.rect(float(ox), float(parsed.depth + oy),
                        float(width), float(height), stroke=0, fill=1)
        canvas.restoreState()


class VectorCanvas(Canvas):
    math_cache: MathCache

    def drawImage(self, image, x, y, width=None, height=None, **kwargs):
        name = image if isinstance(image, str) else getattr(image, 'fileName', None)
        if name in self.math_cache.records:
            parsed = self.math_cache.records[name]
            sx = float(width) / float(parsed.width) if parsed.width else 1
            sy = float(height) / float(parsed.height) if parsed.height else 1
            if abs(sx - sy) > 1e-4:
                raise ValueError('Formula must retain its aspect ratio')
            self.math_cache.draw(self, parsed, x, y, sx)
            return float(parsed.width), float(parsed.height)
        return super().drawImage(image, x, y, width=width, height=height, **kwargs)


class DisplayMath(Flowable):
    def __init__(self, cache: MathCache, text: str, size: float = 11.2):
        super().__init__()
        _, self.parsed = cache.get(text, size)
        self.cache = cache
        self.spaceBefore = 5
        self.spaceAfter = 7

    def wrap(self, available_width, available_height):
        self.scale = min(1, available_width / float(self.parsed.width))
        if self.scale < .78:
            raise ValueError('Display formula too wide; split it in the source')
        self.width = available_width
        self.height = float(self.parsed.height) * self.scale + 4
        return self.width, self.height

    def draw(self):
        width = float(self.parsed.width) * self.scale
        self.cache.draw(self.canv, self.parsed, (self.width - width) / 2, 2, self.scale)


class MathParagraph(Paragraph):
    """Include full image ascent/descent when an inline formula starts a line.

    ReportLab 4.4.9 can retain the previous text bounds in that branch of
    breakLines. Recomputing the formula bounds prevents tall sums from
    overlapping the preceding line; ordinary text metrics are unchanged.
    """
    def breakLines(self, width):
        from reportlab.platypus.paragraph import imgNormV, imgVRange
        result = super().breakLines(width)
        if result.kind == 1:
            for line in result.lines:
                for fragment in line.words:
                    callback = getattr(fragment, 'cbDefn', None)
                    if callback is not None and callback.kind == 'img':
                        descent, ascent = imgVRange(
                            imgNormV(callback.height, fragment.fontSize),
                            callback.valign, fragment.fontSize)
                        line.ascent = max(line.ascent, ascent)
                        line.descent = min(line.descent, descent)
        return result


class Document(BaseDocTemplate):
    def afterFlowable(self, flowable):
        if isinstance(flowable, Paragraph) and hasattr(flowable, 'bookmark'):
            key, label, level = flowable.bookmark
            self.canv.bookmarkPage(key)
            self.canv.addOutlineEntry(label, key, level, closed=False)


class Renderer:
    def __init__(self, cache: MathCache):
        self.cache = cache
        self.styles = {
            'body': ParagraphStyle('body', fontName='Body', fontSize=10.5,
                leading=14.0, spaceAfter=5.0, alignment=TA_LEFT,
                autoLeading='max', allowWidows=0, allowOrphans=0,
                splitLongWords=1),
            'title': ParagraphStyle('title', fontName='BodyBold', fontSize=20,
                leading=25, spaceAfter=12, keepWithNext=True),
            'h2': ParagraphStyle('h2', fontName='BodyBold', fontSize=13,
                leading=17, spaceBefore=13, spaceAfter=7, keepWithNext=True,
                autoLeading='max'),
            'h3': ParagraphStyle('h3', fontName='BodyBold', fontSize=11,
                leading=14.5, spaceBefore=10, spaceAfter=6, keepWithNext=True,
                autoLeading='max'),
            'code': ParagraphStyle('code', fontName='Code', fontSize=8,
                leading=11, spaceAfter=7, splitLongWords=1),
            'reference': ParagraphStyle('reference', fontName='Body', fontSize=9.3,
                leading=12.6, spaceAfter=7, leftIndent=14, firstLineIndent=-14,
                autoLeading='max', splitLongWords=1),
            'list': ParagraphStyle('list', fontName='Body', fontSize=9.3,
                leading=12.6, spaceAfter=5, autoLeading='max', splitLongWords=1),
        }
        self.heading_count = 0

    def inline(self, items, size=10.5):
        output = []
        for node in items:
            kind, value = node['t'], node.get('c')
            if kind == 'Str': output.append(html.escape(value))
            elif kind in ('Space', 'SoftBreak'): output.append(' ')
            elif kind == 'LineBreak': output.append('<br/>')
            elif kind == 'Math': output.append(self.cache.inline(value[1], size))
            elif kind == 'Strong': output.append('<b>' + self.inline(value, size) + '</b>')
            elif kind == 'Emph': output.append('<i>' + self.inline(value, size) + '</i>')
            elif kind == 'Code':
                output.append(f'<font name="Code" size="{size * .79:.2f}">' +
                              html.escape(value[1]) + '</font>')
            elif kind == 'Link':
                label = self.inline(value[1], size)
                url = value[2][0]
                if url.startswith(('https://', 'http://')):
                    output.append('<link href="' + html.escape(url, quote=True) +
                                  '" color="#213f67">' + label + '</link>')
                else: output.append(label)
            elif kind == 'Quoted':
                output.append('“' + self.inline(value[1], size) + '”')
            elif kind == 'Span': output.append(self.inline(value[1], size))
            elif kind == 'Superscript':
                output.append('<super>' + self.inline(value, size * .8) + '</super>')
            elif kind == 'Subscript':
                output.append('<sub>' + self.inline(value, size * .8) + '</sub>')
            else: raise ValueError('Unsupported inline AST node: ' + kind)
        return ''.join(output)

    def blocks(self, blocks, in_list=False):
        output = []
        for node in blocks:
            kind, value = node['t'], node.get('c')
            if kind in ('Para', 'Plain'):
                style = self.styles['list' if in_list else 'body']
                pending = []
                for item in value:
                    if item['t'] == 'Math' and item['c'][0]['t'] == 'DisplayMath':
                        if pending:
                            output.append(MathParagraph(self.inline(pending, style.fontSize), style))
                            pending = []
                        output.append(DisplayMath(self.cache, item['c'][1]))
                    else:
                        pending.append(item)
                if pending:
                    output.append(MathParagraph(self.inline(pending, style.fontSize), style))
            elif kind == 'Header':
                level, _, content = value
                style = self.styles['title' if level == 1 else 'h2' if level == 2 else 'h3']
                paragraph = MathParagraph(self.inline(content, style.fontSize), style)
                if level > 1:
                    self.heading_count += 1
                    label = ''.join(x.get('c', '') if x['t'] == 'Str' else ' '
                                    for x in content)
                    paragraph.bookmark = (f'section-{self.heading_count}', label, level - 2)
                output.append(paragraph)
            elif kind == 'BulletList':
                references = all(
                    item and item[0]['t'] in ('Para', 'Plain') and item[0]['c']
                    and item[0]['c'][0]['t'] == 'Strong'
                    and item[0]['c'][0]['c'][0].get('c', '').startswith('[')
                    for item in value)
                if references:
                    style = self.styles['reference']
                    for item in value:
                        if len(item) != 1:
                            raise ValueError('A bibliography entry must remain one paragraph')
                        output.append(KeepTogether([MathParagraph(
                            self.inline(item[0]['c'], style.fontSize), style)]))
                else:
                    output.append(ListFlowable(
                        [ListItem(self.blocks(item, in_list=True)) for item in value],
                        bulletType='bullet', start='bulletchar', bulletFontName='Body',
                        bulletFontSize=7, leftIndent=12, spaceAfter=7))
            elif kind == 'OrderedList':
                output.append(ListFlowable(
                    [ListItem(self.blocks(item, in_list=True)) for item in value[1]],
                    bulletType='1', start=value[0][0], bulletFontName='Body',
                    bulletFontSize=9, leftIndent=16, spaceAfter=7))
            elif kind == 'CodeBlock':
                output.append(MathParagraph(html.escape(value[1]).replace('\n', '<br/>'), self.styles['code']))
            elif kind == 'HorizontalRule': output.append(Spacer(1, 8))
            elif kind == 'BlockQuote': output.extend(self.blocks(value, in_list))
            else: raise ValueError('Unsupported block AST node: ' + kind)
        return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[1] / 'PROOF_COMPANION.md')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--report', type=Path)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    source = args.source.resolve()
    parsed = subprocess.run(['pandoc', '--from',
        'markdown+tex_math_single_backslash+tex_math_dollars', '--to', 'json', str(source)],
        check=True, text=True, capture_output=True)
    ast = json.loads(parsed.stdout)
    with tempfile.TemporaryDirectory(prefix='akopyan-math-') as directory:
        cache = MathCache(Path(directory))
        VectorCanvas.math_cache = cache
        renderer = Renderer(cache)
        story = renderer.blocks(ast['blocks'])
        width, height = A4
        margin = 53
        document = Document(str(args.output), pagesize=A4,
            leftMargin=margin, rightMargin=margin, topMargin=50, bottomMargin=48,
            title='Convex six-partition obstructions in dimensions greater than seventeen',
            author='', subject='Companion to the completed Lean formalization',
            creator='ReportLab with Matplotlib vector mathematics',
            pageCompression=1, invariant=1)
        frame = Frame(margin, 48, width - 2 * margin, height - 98,
                      leftPadding=0, rightPadding=0, topPadding=0, bottomPadding=0)

        def page(canvas, doc):
            canvas.saveState()
            canvas.setStrokeColor(colors.HexColor('#9a9a9a'))
            canvas.setLineWidth(.35)
            canvas.line(margin, 35, width - margin, 35)
            canvas.setFont('Body', 8)
            canvas.setFillColor(colors.HexColor('#555555'))
            canvas.drawString(margin, 23, 'Akopyan project · proof companion · 24 November 2026')
            canvas.drawRightString(width - margin, 23, str(doc.page))
            canvas.restoreState()

        document.addPageTemplates(PageTemplate(id='main', frames=[frame], onPage=page))
        document.build(story, canvasmaker=VectorCanvas)
        report = {'source': source.name,
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'renderer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'output': args.output.name,
            'output_sha256': hashlib.sha256(args.output.read_bytes()).hexdigest(),
            'output_bytes': args.output.stat().st_size,
            'unique_formula_renders': len(cache.expressions),
            'formula_rendering': 'embedded TrueType glyphs and native PDF vector rules',
            'font_sha256': {Path(path).name: hashlib.sha256(Path(path).read_bytes()).hexdigest()
                            for path in FONT_PATHS},
            'matplotlib_version': matplotlib.__version__,
            'pandoc_version': subprocess.run(['pandoc', '--version'], check=True,
                text=True, capture_output=True).stdout.splitlines()[0],
            'formulas': cache.expressions}
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
        print(json.dumps({k: v for k, v in report.items() if k not in ('formulas', 'font_sha256')}, indent=2))


if __name__ == '__main__':
    main()
