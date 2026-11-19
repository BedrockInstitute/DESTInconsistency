#!/usr/bin/env python3
"""Generate the code links and the Lean appendix of the paper.

Run from this directory after any change to the code:

    python3 gen_codelinks.py

It writes
  codelinks.tex       \\defcode{key}{agda line}{lean line} for every key in KEYS, and
                      \\defline{key}{file}{line} for every key in EXTRA (additional code);
  agda-statements.tex the theorem statements of the Agda file (Section 4);
  lean-statements.tex the trusted part of the Lean file (Part I and the
                      statements of Part III), without doc comments.
The two code excerpts are syntax-highlighted code blocks (environments
`codebox` and `codeblock`, macros \\kw, \\fn, \\ty; see the paper's preamble).
It fails if a declaration is missing or ambiguous, so a stale link cannot
be produced silently.
"""
import io
import re
import sys

AGDA = "../agda/DESTInconsistency.agda"
LEAN = "../lean/DESTInconsistency.lean"

# key: (regex for the Agda declaration, regex for the Lean declaration)
KEYS = {
    "asym":      (r"^Asymmetric : ",            r"^def Asymmetric "),
    "thm1":      (r"^diagonal : ",              r"^theorem diagonal \("),
    "thm2":      (r"^inconsistent : ",          r"^theorem inconsistent \("),
    "xor":       (r"^xor-lemma : ",             r"^theorem xor_lemma "),
    "same":      (r"^  same : ",                r"^theorem same "),
    "ordflip":   (r"^  ord-flip : ",            r"^theorem ord_flip "),
    "singreg":   (r"^  sing-reg : ",            r"^theorem sing_reg "),
    "ordf":      (r"^ord-f : ",                 r"^def ordF "),
    "memberord": (r"^  member-ord : ",          r"^theorem member_ord "),
    "seg":       (r"^  seg : ",                 r"^theorem seg "),
    "compare":   (r"^  compare : ",             r"^theorem compare "),
    "one":       (r"^  one : ",                 r"^theorem one "),
    "both":      (r"^  both : ",                r"^theorem both "),
}

# Declarations of the additional code. key: (file, relative to the repository root;
# regex for the declaration)
EXTRA = {
    "intagda":   ("agda/Intuitionistic.agda",   r"^inconsistent : "),
    "intlean":   ("lean/Intuitionistic.lean",   r"^theorem inconsistent \("),
    "kstrict":   ("agda/Supplement.agda",       r"^kisielewicz-strict : "),
    "melocal":   ("agda/Supplement.agda",       r"^me-localized : "),
    "irrord":    ("agda/Supplement.agda",       r"^irregular-ordinals : "),
}


def read(path):
    return io.open(path, encoding="utf-8").read().split("\n")


def find(lines, pattern, path):
    hits = [n + 1 for n, line in enumerate(lines) if re.search(pattern, line)]
    if len(hits) != 1:
        sys.exit(f"{path}: pattern {pattern!r} matched lines {hits}")
    return hits[0]


def lean_statements(lines):
    """Part I of the Lean file and the statements of Part III."""
    text = "\n".join(lines)
    part1 = text[text.index("/-! ## Part I."):text.index("/-! ## Part II.")]
    part3 = text[text.index("/-! ## Part III."):text.index("end DEST")]
    # Part III: keep each theorem up to its ":=", drop the proofs.
    stmts = []
    for block in re.split(r"\n(?=/--|theorem )", part3):
        if block.startswith("theorem ") and "'" not in block.split()[1]:
            stmts.append(block[:block.index(":=")].rstrip())
    part1 = re.sub(r"/-[-!].*?-/\n?", "", part1, flags=re.S)  # doc comments
    part1 = re.sub(r"\n{3,}", "\n\n", part1).strip()
    # The doc comments include the file's part headings; mark the parts with
    # comment lines instead, so the appendix shows where Parts I and III begin.
    # Part III is kept as one unbreakable chunk: its statements are separated
    # by lines holding a single space, which codeblock() does not split at.
    body = ("-- Part I. Trusted part\n" + part1 + "\n\n"
            "-- Part III. The theorems, statements only (Part II, the proofs, is omitted)\n"
            + "\n \n".join(stmts))
    return "namespace DEST\n\n" + body + "\n"


# Syntax highlighting for the code blocks.  Inside the blocks § « » are the
# command characters, so the code itself needs no escaping.
LEAN_KW = {"def", "theorem", "structure", "inductive", "where", "namespace", "fun"}
LEAN_TY = {"Prop", "Type", "Nat", "Fin", "Side", "Opp", "Fm", "Sat", "Regular",
           "Comp", "DESTminus", "DEST", "Asymmetric", "False"}
LEAN_DECL = {"def", "theorem", "structure", "inductive"}
AGDA_KW = {"data", "record", "field", "module", "where", "open"}
AGDA_TY = {"Set", "Rel", "Comp", "Fm", "Fin", "Regular", "Side", "Opp", "Asymmetric",
           "DEST⁻", "DEST", "DNE", "ℕ", "⊥"}
TOKEN = re.compile(r"[\w'⁻.-]+|\s+|.", re.U)


def highlight(text, kws, tys, decl_after=None):
    assert not set("§«»") & set(text)
    out = []
    for line in text.split("\n"):
        if line.lstrip().startswith("--"):
            out.append("§cm«%s»" % line)
            continue
        toks = TOKEN.findall(line)
        words = [t for t in toks if not t.isspace()]
        res, prev = [], None
        for t in toks:
            if t.isspace():
                res.append(t)
                continue
            if t in kws:
                res.append("§kw«%s»" % t)
            elif decl_after is not None and prev in decl_after:
                res.append("§fn«%s»" % t)
            elif decl_after is None and words and t is words[0] and len(words) > 1 \
                    and words[1] == ":" and not line[:1].isspace():
                res.append("§fn«%s»" % t)
            elif t in tys:
                res.append("§ty«%s»" % t)
            else:
                res.append(t)
            prev = t
        out.append("".join(res))
    return "\n".join(out)


def codeblock(text, size="\\footnotesize", env="codeblock"):
    """A shaded code block. The page-breakable `codeblock` is set as one unbreakable
    Verbatim per declaration (chunks separated by blank lines), so a page can only
    break between declarations; a lone `namespace` line is kept with the next chunk."""
    opts = "[fontsize=" + size + ", commandchars=\\§\\«\\»"
    head = "% Generated by gen_codelinks.py; do not edit.\n\\begin{" + env + "}\n"
    if env != "codeblock":
        return (head + "\\begin{Verbatim}" + opts + "]\n" + text.rstrip("\n")
                + "\n\\end{Verbatim}\n\\end{" + env + "}\n")
    chunks = text.rstrip("\n").split("\n\n")
    if len(chunks) > 1 and "\n" not in chunks[0] and "namespace" in chunks[0]:
        chunks[:2] = [chunks[0] + "\n\n" + chunks[1]]
    # No list spacing around each chunk, so consecutive declarations are separated by
    # exactly one blank code line, as in a single listing.
    flat = ", samepage=true, listparameters={\\setlength{\\topsep}{0pt}\\setlength{\\partopsep}{0pt}}]\n"
    parts = []
    for i, chunk in enumerate(chunks):
        gap = "\n" if i < len(chunks) - 1 else ""   # keep the blank line between declarations
        parts.append("\\begin{Verbatim}" + opts + flat + chunk + "\n" + gap + "\\end{Verbatim}\n")
    # Set the whole run in the code size, so the step from one chunk to the next uses the
    # code line spacing rather than the body text's (which differs in the Chinese version).
    # \parskip must not stretch: framed splits the block to the exact page height, which
    # would otherwise spread the declarations apart on a full page.
    return head + "{" + size + "\\parskip=0pt\\relax\n" + "".join(parts) + "\\par}\n\\end{" + env + "}\n"


def agda_statements(lines):
    """The type signatures in Section 4 of the Agda file."""
    start = next(n for n, l in enumerate(lines) if l.startswith("-- 4. The theorems"))
    blocks, cur = [], None
    for l in lines[start + 1:]:
        if re.match(r"^[^\s-]\S* : ", l):
            cur = [l]
            blocks.append(cur)
        elif cur is not None and l[:1].isspace() and l.strip():
            cur.append(l)
        else:
            cur = None
    return "\n\n".join("\n".join(b) for b in blocks)


def main():
    agda, lean = read(AGDA), read(LEAN)
    out = ["% Generated by gen_codelinks.py; do not edit."]
    for key, (pa, pl) in KEYS.items():
        out.append("\\defcode{%s}{%d}{%d}" % (key, find(agda, pa, AGDA), find(lean, pl, LEAN)))
    for key, (path, pattern) in EXTRA.items():
        out.append("\\defline{%s}{%s}{%d}" % (key, path, find(read("../" + path), pattern, path)))
    io.open("codelinks.tex", "w", encoding="utf-8").write("\n".join(out) + "\n")
    io.open("agda-statements.tex", "w", encoding="utf-8").write(
        codeblock(highlight(agda_statements(agda), AGDA_KW, AGDA_TY), "\\codesize", "codebox"))
    io.open("lean-statements.tex", "w", encoding="utf-8").write(
        codeblock(highlight(lean_statements(lean), LEAN_KW, LEAN_TY, LEAN_DECL), "\\codesize"))
    print("wrote codelinks.tex (%d keys), agda-statements.tex and lean-statements.tex"
          % (len(KEYS) + len(EXTRA)))


if __name__ == "__main__":
    main()
