"""Copy the PrimeNumberTheoremAnd files needed for `chebyshev_asymptotic` into Zeta5/PNTPort,
stripping the `Architect` blueprint annotations and wrapping each file in `namespace Zeta5.PNTPort`."""
import re, sys, os
SRC = "/tmp/claude-1000/-home-cesar-code-zeta5/9eb4c2dc-09c3-4411-ab1a-19c26a13be23/scratchpad/pnt/PrimeNumberTheoremAnd/"
DST = "/home/cesar/code/zeta5/Zeta5/Zeta5/PNTPort/"
COMMIT = "a5154676af9aa3095150ee410cdda80555aa0642"
FILES = {  # source path -> module name
    "SmoothExistence.lean": "SmoothExistence",
    "Sobolev.lean": "Sobolev",
    "Fourier.lean": "Fourier",
    "Wiener.lean": "Wiener",
    "Consequences.lean": "Consequences",
}
MODMAP = {"PrimeNumberTheoremAnd." + k[:-5].replace("/", "."): "Zeta5.PNTPort." + v for k, v in FILES.items()}

def skip_comment(s, i):
    # s[i:i+2] == '/-'; return index after matching '-/' (nested)
    depth = 0
    while i < len(s):
        if s.startswith("/-", i): depth += 1; i += 2
        elif s.startswith("-/", i):
            depth -= 1; i += 2
            if depth == 0: return i
        else: i += 1
    raise ValueError("unterminated comment")

def skip_balanced(s, i, open_, close):
    # s[i] == open_; return index after the matching close, skipping comments and strings
    depth = 0
    while i < len(s):
        c = s[i]
        if s.startswith("/-", i): i = skip_comment(s, i); continue
        if s.startswith("--", i): i = s.index("\n", i); continue
        if c == '"':
            i += 1
            while s[i] != '"':
                i += 2 if s[i] == "\\" else 1
            i += 1; continue
        if c in "([{": depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0: return i + 1
        i += 1
    raise ValueError("unbalanced")

def strip(s):
    out = []; i = 0
    while i < len(s):
        if s.startswith("blueprint_comment", i) and (i == 0 or s[i-1] == "\n"):
            j = s.index("/-", i); j = skip_comment(s, j)
            while j < len(s) and s[j] == "\n": j += 1
            i = j; continue
        if s.startswith("@[blueprint", i):
            j = skip_balanced(s, i + 1, "[", "]")
            inner = s[i+2:j-1]
            # the blueprint item is the whole attribute unless followed by a top-level comma
            k = len("blueprint"); d = 0; rest = None
            while k < len(inner):
                if inner.startswith("/-", k): k = skip_comment(inner, k); continue
                c = inner[k]
                if c in "([{": d += 1
                elif c in ")]}": d -= 1
                elif c == "," and d == 0: rest = inner[k+1:].strip(); break
                elif c == '"':
                    k += 1
                    while inner[k] != '"': k += 2 if inner[k] == "\\" else 1
                k += 1
            if rest: out.append("@[" + rest + "]")
            while j < len(s) and s[j] in " \n": j += 1
            if rest: out.append("\n")
            i = j; continue
        out.append(s[i]); i += 1
    return "".join(out)

HEADER = """/-
Ported from PrimeNumberTheoremAnd (A. Kontorovich, T. Tao, et al.),
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit {commit},
file `PrimeNumberTheoremAnd/{src}`. Licensed under the Apache License 2.0 (see `LICENSE` in this
directory). Changes: blueprint annotations removed, declarations wrapped in
`namespace Zeta5.PNTPort`, unused declarations removed, and adaptations to a newer Mathlib.
-/
"""

START = re.compile(r"^(/--|@\[|(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance)\b)")
CONT = re.compile(r"^(termination_by|decreasing_by|where|deriving|with)\b")
NAME = re.compile(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|instance)\s+(\S+)", re.M)

PRUNE = True  # only theorems/lemmas are pruned; defs, instances, notation are always kept
THM = re.compile(r"^(?:private |protected )*(?:theorem|lemma)\s")

def first_decl_line(c):
    return next((l for l in c if not l.startswith(("/--", "@[", " ")) and l.strip()), "")

def select(body, keep=None, drop=None):
    """Keep the preamble and the top-level declarations whose name is in `keep` (default: all)
    and not in `drop`."""
    lines = body.split("\n"); chunks = [[]]
    in_doc = False; glue = False  # glue: the next declaration line belongs to the current chunk
    for l in lines:
        if in_doc:
            chunks[-1].append(l)
            if l.rstrip().endswith("-/"): in_doc = False; glue = True
            continue
        if l[:1] not in ("", " ", "|", ")", "-") and not CONT.match(l):
            if not glue: chunks.append([])
            glue = False
            if l.startswith("/--"):
                if l.rstrip().endswith("-/"): glue = True
                else: in_doc = True
            elif l.startswith("@["): glue = True
        elif l.strip():
            glue = False
        chunks[-1].append(l)
    info = []  # (text, short name or None, droppable by pruning)
    for c in chunks[1:]:
        m = NAME.search("\n".join(l for l in c if not l.startswith(("/--", "@[", " "))))
        full = m.group(1) if m else None
        name = full.split(".")[-1] if m else None
        text = "\n".join(c).rstrip("\n") + "\n"
        if name is not None and ((keep is not None and name not in keep) or (drop and name in drop)):
            continue
        prunable = PRUNE and name is not None and THM.match(first_decl_line(c)) and not reached(full)
        info.append([text, name, prunable])
    # also keep pruned lemmas that are mentioned in kept text (uses the kernel term may not show)
    changed = True
    while changed:
        changed = False
        kept_text = "\n".join(t for t, n, p in info if not p)
        for e in info:
            if e[2] and re.search(r"(?<![\w'])" + re.escape(e[1]) + r"(?![\w'])", kept_text):
                e[2] = False; changed = True
    out = ["\n".join(chunks[0])] + [t for t, n, p in info if not p]
    return "\n".join(out)

def port(src, mod, keep_upto=None, keep=None, drop=None):
    s = open(SRC + src).read()
    if keep_upto:
        k = s.index(keep_upto); k = s.index("\n\n", k)
        s = s[:k] + "\n"
    s = strip(s)
    lines = s.split("\n")
    imps = []; body_start = 0
    for n, l in enumerate(lines):
        if l.startswith("import "):
            m = l.split()[1]
            if m == "Architect": pass
            else: imps.append("import " + MODMAP.get(m, m))
            body_start = n + 1
        elif l.strip() == "" : continue
        else: break
    body = "\n".join(lines[body_start:]).strip("\n")
    body = select(body, keep, drop)
    # Lemmas extending Mathlib namespaces (used with dot notation) stay in those namespaces.
    body = re.sub(r"^((?:private |protected |noncomputable )*(?:theorem|lemma) )((?:Finset|Filter|Asymptotics|Real|Set)\.)",
                  r"\1_root_.\2", body, flags=re.M)
    text = HEADER.format(commit=COMMIT, src=src) + "\n".join(imps) + "\n\nnamespace Zeta5.PNTPort\n\n" + body + "\n\nend Zeta5.PNTPort\n"
    open(DST + mod + ".lean", "w").write(text)

# Source-level adaptations: (module, old, new). Each `old` must occur exactly once.
PATCHES = [
    # the two small `PrimeNumberTheoremAnd/Mathlib/*` helper files are not ported
    ("SmoothExistence", "import PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support\n", ""),
    ("Wiener", "import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics\n", ""),
    ("Wiener", "(nnabla_bound C hx).natCast", "(nnabla_bound C hx).comp_tendsto tendsto_natCast_atTop_atTop"),
    # `Multiplicative.ofAdd` is no longer unfolded usefully by `simp`; prove measurability by hand
    ("Wiener", """    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      Multiplicative.ofAdd, Equiv.coe_fn_mk, smul_eq_mul]
    fun_prop""", """    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      smul_eq_mul]
    have hc : Continuous fun v : ℝ => (𝐞 (Multiplicative.ofAdd v) : ℂ) :=
      (continuous_subtype_val.comp Real.continuous_fourierChar).comp continuous_ofAdd
    have hg : Measurable fun p : ℝ × ℝ => (𝐞 (Multiplicative.ofAdd (-(p.2 * (p.1 / (2 * π))))) : ℂ) :=
      hc.measurable.comp (by fun_prop)
    exact (by fun_prop : Measurable fun p : ℝ × ℝ => cexp (-(↑p.1 * (↑σ' - 1)))).mul
      (hg.mul (hcont.comp measurable_snd))"""),
    ("Wiener", "simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1]",
     "simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1]"),
    ("Wiener", "(nnabla_bound C hx).comp_tendsto tendsto_natCast_atTop_atTop ; simp [nnabla, a]",
     "(nnabla_bound C hx).comp_tendsto tendsto_natCast_atTop_atTop <;>\n      first | (funext n; simp [nnabla, a]) | simp [nnabla, a, Function.comp_def]"),
    ("Wiener", """    simp [ae, this]
""", """    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp
"""),
    ("Wiener", """  have haux :
    (fun σ' ↦""", """  have haux :
    (fun (σ' : ℝ) ↦"""),
    ("Consequences", "import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic\n", ""),
    ("Consequences", "exact sub_isLittleO huv hwu", "exact Asymptotics.IsEquivalent.sub_isLittleO huv hwu"),
    # from `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`
    ("Consequences", "theorem WeakPNT' :", """/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

theorem WeakPNT' :"""),
    ("Consequences", "Real.tendsto_pow_log_div_pow_atTop", "tendsto_pow_log_div_pow_atTop"),
    ("Consequences", "import PrimeNumberTheoremAnd.Defs\n", ""),
]

def apply_patches():
    for mod, old, new in PATCHES:
        p = DST + mod + ".lean"; t = open(p).read()
        assert t.count(old) <= 1, (mod, old, t.count(old))
        if t.count(old) == 0: print("patch not needed (pruned):", mod, old.splitlines()[0][:60])
        open(p, "w").write(t.replace(old, new))

# unused by `chebyshev_asymptotic`; the two `prelim_decay_*` lemmas are `sorry` upstream
WIENER_DROP = {"prelim_decay_2", "AbsolutelyContinuous", "prelim_decay_3", "decay_alt"}

# `pnt_reach.txt` lists the constants of the port reachable from `chebyshev_asymptotic`
# (computed by a small Lean script); every other theorem/lemma/def is dropped.
REACH = [l.split()[1] for l in open(os.path.join(os.path.dirname(__file__), "pnt_reach.txt"))
         if l.startswith("Zeta5.PNTPort.")]

def reached(name):
    name = name.removeprefix("_root_.")
    return any(r == name or r.endswith("." + name) or ("." + name + ".") in ("." + r) for r in REACH)

os.makedirs(DST, exist_ok=True)
for src, mod in FILES.items():
    if mod == "Consequences":
        port(src, mod, keep_upto="theorem chebyshev_asymptotic :", keep={"add_isLittleO''", "WeakPNT'",
             "WeakPNT''", "isLittleO_sqrt_mul_log", "chebyshev_asymptotic"})
    elif mod == "Wiener":
        port(src, mod, drop=WIENER_DROP)
    else:
        port(src, mod)
apply_patches()
