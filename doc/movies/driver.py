#!/usr/bin/env python3
import re
from collections import namedtuple
from itertools import zip_longest, groupby
from pathlib import Path

from alectryon import cli, core, transforms
from alectryon.core import Text
from alectryon.latex import ASSETS

def pair(*iterable):
    iters = [iter(iterable)] * 2
    return zip_longest(*iters, fillvalue=None)

Snippet = namedtuple("Snippet", "name io_annots s")

SNIPPET_DELIM_RE = re.compile(r"""
  [(][*]\s*
    (?P<kind>begin|end)\s+ snippet\s+ (?P<name>[^ ]+)
    (?:[:][:]\s+ (?P<io_flags>.*?))?
  \s*[*][)]
""", re.VERBOSE)

SNIPPET_IO_FLAGS_RE = re.compile(r"""
  (?:\n\s*)? # As if flags were at end of last non-empty line
  [(][*][|]\s*
    (?:..\s+ coq::\s+ (.*?))?
  \s*[|]?[*][)]
""", re.VERBOSE)

class NoSnippets(Exception):
    pass

def check_snippet_boundaries(before, after):
    assert before
    if not after:
        MSG = "Missing final ``(* end snippet {} *)`` delimiter"
        raise ValueError(MSG.format(before.group("before_name")))
    if before.group("kind") != "begin":
        raise ValueError("Unexpected delimiter ``{}``".format(before.group()))
    if after.group("kind") != "end":
        raise ValueError("Unexpected delimiter ``{}``".format(before.group()))
    if before.group("name") != after.group("name"):
        MSG = "Mismatched delimiters: (* begin snippet {} *) and (* end snippet {} *)"
        raise ValueError(MSG.format(before.group("name"), after.group("name")))

def split_snippet(name, io_flags, contents):
    for substr, subsnippet in pair(io_flags, *SNIPPET_IO_FLAGS_RE.split(contents)):
        io_annots = transforms.read_all_io_flags(substr or "")
        yield Snippet(name, io_annots, subsnippet)

def parse_coq_snippets(coq, ctx):
    end, chunks = 0, []
    for before, after in pair(*SNIPPET_DELIM_RE.finditer(coq)):
        check_snippet_boundaries(before, after)
        if before.start() > end:
            chunks.append(coq[end:before.start()])
        name, io_flags = before.group("name", "io_flags")
        chunks.extend(split_snippet(name, io_flags, coq[before.end():after.start()]))
        end = after.end()
    if not chunks:
        raise NoSnippets()
    if end < len(coq):
        chunks.append(coq[end:])
    ctx["chunks"] = chunks
    return [(c.s if isinstance(c, Snippet) else c) for c in chunks]

def _prepare_snippets(annotated, chunks):
    for chunk, frs in zip(chunks, annotated):
        if isinstance(chunk, Snippet):
            frs = transforms.inherit_io_annots(frs, chunk.io_annots)
            yield chunk, list(frs)

def prepare_snippets(annotated, chunks, ctx):
    ctx["snippets"], annotated = zip(*_prepare_snippets(annotated, chunks))
    return annotated

def drop_hidden(annotated, snippets):
    for snippet, frs in zip(snippets, annotated):
        yield [] if transforms.all_hidden(frs, snippet.io_annots) else frs

def _group_subsnippets(annotated, snippets):
    for name, group in groupby(zip(snippets, annotated), lambda p: p[0].name):
        frs = transforms.coalesce_text(fr for _, frs in group for fr in frs)
        yield name, list(frs)

def group_subsnippets(annotated, snippets, ctx):
    ctx["names"], annotated = zip(*_group_subsnippets(annotated, snippets))
    return annotated

def trim_annotated(annotated):
    for frs in annotated:
        yield transforms.strip_text(frs)

class Dedenter:
    """Strip up to ``n`` leading spaces from each source line of a snippet.

    A source line can straddle several fragments (a sentence's prefix, its
    contents, a trailing comment…), so the number of spaces left to remove on
    the current line is carried over from one call to the next.
    """

    def __init__(self, n):
        self.n = self.left = n

    def __call__(self, s):
        out = []
        for idx, part in enumerate(s.split("\n")):
            if idx:
                out.append("\n")
                self.left = self.n
            if self.left and part:
                cut = 0
                while cut < min(len(part), self.left) and part[cut] == " ":
                    cut += 1
                self.left, part = self.left - cut, part[cut:]
                if part: # Reached the code itself: stop eating spaces
                    self.left = 0
            out.append(part)
        return "".join(out)

def snippet_parts(fr):
    if isinstance(fr, Text):
        yield fr.contents
    else:
        yield from fr.prefixes
        if fr.input is not None:
            yield fr.input.contents
        yield from fr.suffixes

def dedent_snippet(frs):
    """Remove the indentation that enclosing sections add to a snippet."""
    text = "".join(part for fr in frs for part in snippet_parts(fr))
    n = core.measure_min_indentation(text.split("\n"))
    if not n:
        return frs
    dedent, dedented = Dedenter(n), []
    for fr in frs:
        if isinstance(fr, Text):
            fr = fr._replace(contents=dedent(fr.contents))
        else:
            fr.prefixes[:] = [dedent(p) for p in fr.prefixes]
            if fr.input is not None:
                fr = fr._replace(input=fr.input._replace(
                    contents=dedent(fr.input.contents)))
            fr.suffixes[:] = [dedent(s) for s in fr.suffixes]
        dedented.append(fr)
    return dedented

def dedent_snippets(annotated):
    return [dedent_snippet(frs) for frs in annotated]

# Textual substitutions applied to the LaTeX generated by Alectryon, in
# order, before writing it out.  This used to be done with a `sed` script
# in the Makefile (a `SED` variable used to post-process the `.tex` files);
# it is reproduced here so that `driver-new.py` emits ready-to-use LaTeX
# directly, without needing a separate post-processing pass.
LATEX_SUBSTITUTIONS = [
    ("{exists}", "{\\(\\exists\\)}"),
    ("{forall}", "{\\(\\forall\\)}"),
    ("⊥", "\\(\\bot\\)"),
    ("Δ", "\\(\\Delta\\)"),
    ("{/\\PYZbs{}", "{\\(\\,\\wedge\\,\\)"),
    ("\\PY{o}{\\PYZbs{}}\\PY{k+kr}{in}", "\\(\\in\\)"),
    ("\\PY{o}{[\\PYZbs{}}\\PY{k+kr}{in}\\PY{o}{]}", "\\([{\\in}]\\)"),
    ("[\\PYZbs{}in]", "\\([{\\in}]\\)"),
    ("`;`", ";"),
    ("`|`", "\\(\\cup\\)"),
    ("`&`", "\\(\\cap\\)"),
    ("{\\PYZbs{}/", "{\\(\\,\\vee\\,\\)"),
    ("{\\PYZlt{}\\PYZhy{}\\PYZgt{}}", "{\\(\\leftrightarrow\\)}"),
    ("{\\PYZhy{}\\PYZgt{}}", "{\\(\\rightarrow\\)}"),
    ("{`\\PYZam{}`}", "{\\(\\cap\\)}"),
    ("~\\PY{o}{;}~", "\\PY{o}{;}"),
    ("Suc\\PYZbs{}in", "Suc{\\(\\in\\)}"),
    ("L\\PYZbs{}in", "L{\\(\\in\\)}"),
    ("\\begin{alectryon}", "%"),
    ("\\end{alectryon}", ""),
    ("{\\PYZti{}", "{\\(\\neg\\)"),
    ("`\\PYZlt{}=`", "\\(\\subset\\)"),
]

def apply_latex_substitutions(tex):
    for find, replace in LATEX_SUBSTITUTIONS:
        tex = tex.replace(find, replace)
    return tex

def render_snippets(latex):
    return [apply_latex_substitutions(ltx.render()) for ltx in latex]

def write_snippets(rendered, names, fpath, output_directory):
    for name, tex in zip(names, rendered):
        target = (Path(output_directory) / name).with_suffix(".tex")
        print(">> {} → {}".format(fpath, target))
        target.write_text(tex)

def record_assets(v, assets):
    cli._record_assets(assets, ASSETS.PATH, ASSETS.ALECTRYON_STY + ASSETS.PYGMENTS_STY)
    return v

cli.PIPELINES['coq']['snippets-hydras'] = (
    cli.read_plain, parse_coq_snippets, cli.annotate_chunks, prepare_snippets,
    # Transforms applied twice: once to prepare comments for drop_hidden, once
    # to add comments and newlines to sentences after grouping subsnippets.
    cli.apply_transforms, drop_hidden, group_subsnippets,
    cli.apply_transforms, trim_annotated, dedent_snippets,
    cli.gen_latex_snippets, render_snippets, write_snippets
)

cli.PIPELINES['coq']['assets'] = (record_assets, cli.copy_assets)

if __name__ == '__main__':
    try:
        cli.main()
    except NoSnippets:
        pass
