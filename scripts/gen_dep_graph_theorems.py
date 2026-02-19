# Copyright (c) Meta Platforms, Inc. and affiliates.
# All rights reserved.
#!/usr/bin/env python3
"""
Generate a target-theorem colored-boxes chart for the formalization status.

Each square = one target theorem from the manifest.
Colors:
  green       = fully proved (no sorry anywhere in dep chain)
  light green = declaration proved but depends on sorry'd lemma (DEPS SORRY)
  blue        = sorry in own proof
  grey        = not formalized / not present
"""

import json
from pathlib import Path
from collections import defaultdict

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

MANIFEST = Path(__file__).resolve().parent.parent / "manifest.json"

# ── Hardcoded target statuses ─────────────────────────────────────────
# Status key:
#   PROVED     = sorry-free Lean proof including all transitive deps
#   EXERCISE   = TeX says "Exercise" / "LTTR"; Lean has sorry stub
TARGET_STATUSES = {
    # Chapter 1: Notations
    "def.binom.binom": "PROVED", "prop.binom.rec": "PROVED",
    "prop.binom.0": "PROVED", "thm.binom.sym": "PROVED",
    # Chapter 2: CommutativeRings
    "def.alg.commring": "PROVED", "def.alg.module": "PROVED",
    # Chapter 3: FPSDefinition
    "def.fps.fps": "PROVED", "def.fps.ops": "PROVED", "thm.fps.ring": "PROVED",
    "def.fps.coeff": "PROVED", "def.infsum.essfin": "PROVED",
    "def.fps.summable": "PROVED", "prop.fps.summable.sub": "PROVED",
    "prop.fps.summable-sums-rule": "PROVED", "def.fps.x": "PROVED",
    "lem.fps.xa": "PROVED", "prop.fps.xk": "PROVED", "cor.fps.sumakxk": "PROVED",
    "prop.binom.vandermonde.NN": "PROVED", "thm.binom.vandermonde.CC": "PROVED",
    # Chapter 4: DividingFPS
    "def.commring.inverse": "PROVED", "thm.commring.inverse-uni": "PROVED",
    "def.commring.fracs": "PROVED", "prop.commring.fracs.1": "PROVED",
    "prop.fps.invertible": "PROVED", "cor.fps.invertible.field": "PROVED",
    "prop.fps.invertible.1+x": "PROVED", "thm.fps.newton-binom": "PROVED",
    "thm.binom.upneg-n": "PROVED", "prop.fps.anti-newton-binom": "PROVED",
    "cor.fps.anti-newton-binom-2": "PROVED", "def.fps.div-by-x": "PROVED",
    "prop.fps.div-by-x-inverts": "PROVED", "lem.fps.g=xh": "PROVED",
    "lem.fps.first-n-coeffs-of-xna": "PROVED", "lem.fps.muls-of-xn": "PROVED",
    "lem.fps.prod.irlv.fg": "PROVED", "lem.fps.prod.irlv.mul": "PROVED",
    "lem.fps.prod.irlv.cong-mul": "PROVED",
    # Chapter 5: Polynomials
    "def.fps.pol": "PROVED", "thm.fps.pol.ring": "PROVED",
    "def.alg.ring": "PROVED", "def.alg.Kalg": "PROVED",
    "def.pol.subs": "PROVED", "thm.pol.eval.a+b": "PROVED",
    # Chapter 6: Substitution
    "def.fps.subs": "PROVED", "prop.fps.subs.wd": "PROVED",
    "prop.fps.subs.rules": "PROVED", "lem.fps.fg-coeffs-0": "PROVED",
    "def.kron-delta": "PROVED",
    # Chapter 7: Derivatives
    "def.fps.deriv": "PROVED", "thm.fps.deriv.rules": "PROVED",
    # Chapter 8: ExpLog  [0 sorries on run20260219 — all proved]
    "def.fps.exp-log": "PROVED", "prop.fps.exp-log-der": "PROVED",
    "lem.fps.compos-cst-term-0": "PROVED", "thm.fps.exp-log-inv": "PROVED",
    "def.fps.Exp-Log-maps": "PROVED", "lem.fps.Exp-Log-maps-wd": "PROVED",
    "lem.fps.Exp-Log-maps-inv": "PROVED", "lem.fps.Exp-Log-additive": "PROVED",
    "prop.fps.Exp-Log-groups": "PROVED", "thm.fps.Exp-Log-group-iso": "PROVED",
    "def.fps.loder.1": "PROVED", "prop.fps.loder.log": "PROVED",
    "prop.fps.loder.prod": "PROVED", "cor.fps.loder.prodk": "PROVED",
    "cor.fps.loder.inv": "PROVED",
    # Chapter 9: NonIntegerPowers  [0 sorries on run20260219 — all proved]
    "def.fps.power-c": "PROVED", "thm.fps.power-c.rules": "PROVED",
    "thm.fps.gen-newton": "PROVED", "prop.binom.nCk-2i-qedmo.CN": "PROVED",
    # Chapter 10: IntegerCompositions
    "def.fps.comps": "PROVED", "thm.fps.comps.num-comps-n-k": "PROVED",
    "thm.fps.comps.num-comps-n": "PROVED", "def.fps.wcomps": "PROVED",
    "thm.fps.comps.num-wcomps-n-k": "PROVED",
    "thm.fps.comps.num-wpcomps-n-k": "PROVED",
    "prop.fps.comps.num-w2comps-n-k-id": "PROVED",
    # Chapter 11: XnEquivalence
    "def.fps.xneq": "PROVED", "thm.fps.xneq.props": "PROVED",
    "prop.fps.xneq-multiple": "PROVED", "prop.fps.xneq.comp": "PROVED",
    # Chapter 12: InfiniteProducts1
    "def.fps.determines-xn-coeff": "PROVED",
    "def.fps.xn-coeff-fin-determined": "PROVED",
    "prop.fps.summable=fin-det": "PROVED", "def.fps.multipliable": "PROVED",
    "prop.fps.multipliable.prod-wd": "PROVED",
    "prop.fps.multipliable.prod-wd2": "PROVED",
    "lem.fps.prod.irlv.1": "PROVED", "lem.fps.prod.irlv.fin": "PROVED",
    "thm.fps.1+f-mulable": "PROVED", "prop.fps.1-mulable": "PROVED",
    "def.fps.infprod-approx": "PROVED", "lem.fps.mulable.approx": "PROVED",
    "prop.fps.infprod-approx-xneq": "PROVED", "prop.fps.union-mulable": "PROVED",
    "prop.fps.prod-mulable": "PROVED", "prop.fps.div-mulable": "PROVED",
    "prop.fps.prods-mulable-subfams": "PROVED",
    "prop.fps.prods-mulable-rules.reindex": "PROVED",
    "prop.fps.prods-mulable-rules.SW1": "PROVED",
    "prop.fps.prods-mulable-rules.fubini1": "PROVED",
    "prop.fps.prods-mulable-rules.fubini": "PROVED",
    # Chapter 13: InfiniteProducts2
    "prop.fps.prodrule-fin-fin": "PROVED", "prop.fps.prodrule-fin-inf": "PROVED",
    "def.fps.prodrule.ess-fin": "PROVED",
    "prop.fps.prodrule-inf-infN": "PROVED",
    "prop.fps.prodrule-inf-inf": "PROVED",
    "prop.fps.prodrule-fin-infJ": "PROVED",
    "lem.fps.prod.irlv.inf": "PROVED", "prop.gf.prod.euler-odd": "PROVED",
    "thm.gf.prod.euler-comb": "PROVED", "prop.fps.subs.rule-infprod": "PROVED",
    "prop.fps.Exp-Log-infsum": "PROVED",
    "prop.fps.Exp-Log-infprod": "PROVED",
    # Chapter 14: WeightedSets
    "def.gf-ws.weighted-sets": "PROVED", "prop.gf-ws.iso": "PROVED",
    "def.gf-ws.djun": "PROVED", "prop.gf-ws.djun": "PROVED",
    "def.gf-ws.prod": "PROVED", "prop.gf-ws.prod": "PROVED",
    "prop.gf-ws.pow": "PROVED", "def.domino.shapes-and-tilings": "PROVED",
    "lem.gf.weighted-set.domino.fd": "PROVED",
    # Chapter 15: Limits
    "def.fps.lim.stab": "PROVED", "def.fps.lim.coeff-stab": "PROVED",
    "thm.fps.lim.lim-crit": "PROVED", "lem.fps.lim.xn-equiv": "PROVED",
    "prop.fps.lim.sum-prod": "PROVED", "cor.fps.lim.sum-prod-k": "PROVED",
    "prop.fps.lim.sum-quot": "PROVED", "prop.fps.lim.comp": "PROVED",
    "prop.fps.lim.deriv-lim": "PROVED", "thm.fps.lim.sum-lim": "PROVED",
    "thm.fps.lim.prod-lim": "PROVED", "cor.fps.lim.fps-as-pol": "PROVED",
    "thm.fps.lim.sum-lim-conv": "PROVED", "thm.fps.lim.prod-lim-conv": "PROVED",
    # Chapter 16: LaurentSeries
    "thm.fps.laure.binary-rep-uniq": "PROVED",
    "thm.fps.laure.balanced-tern-rep-uniq": "PROVED",
    "def.fps.laure.double": "PROVED", "def.fps.laure.laupol": "PROVED",
    "thm.fps.laure.laupol-ring": "PROVED", "prop.fps.laure.a=sumaixi": "PROVED",
    "def.fps.laure.lauser": "PROVED", "thm.fps.laure.lauser-ring": "PROVED",
    # Chapter 17: Multivariate
    "prop.fps.mulvar.comp-y-coeff": "PROVED",
    # Chapter 18: Partitions/Basics
    "def.pars.parts": "PROVED", "def.pars.pn-pkn": "PROVED",
    "def.pars.iverson": "PROVED", "def.pars.floor-ceil": "PROVED",
    "prop.pars.basics": "PROVED", "thm.pars.main-gf": "PROVED",
    "thm.pars.main-gf-parts-n": "PROVED", "thm.pars.main-gf-parts-I": "PROVED",
    "def.pars.odd-dist-parts": "PROVED", "thm.pars.odd-dist-equal": "PROVED",
    "prop.pars.pkn=dual": "PROVED", "cor.pars.p0kn=dual": "PROVED",
    "thm.pars.main-gf-0n": "PROVED", "thm.pars.sigma1": "PROVED",
    "thm.pars.sigma1-I": "PROVED",
    # Chapter 19: PentagonalJacobi
    "def.pars.pent-num": "PROVED", "thm.pars.pent": "PROVED",
    "cor.pars.pn-rec": "PROVED", "thm.pars.jtp1": "PROVED",
    "thm.pars.jtp2": "PROVED", "lem.fps.fxx=gxx": "PROVED",
    "thm.pars.euler-sum-div-rec": "PROVED",
    # Chapter 20: QBinomialBasic
    "prop.pars.qbinom.intro-count-binom": "PROVED",
    "def.pars.qbinom.qbinom": "PROVED", "prop.pars.qbinom.alt-defs": "PROVED",
    "prop.pars.qbinom.0": "PROVED", "prop.pars.qbinom.n0": "PROVED",
    "thm.pars.qbinom.rec": "PROVED", "thm.pars.qbinom.quot1": "PROVED",
    "def.pars.qbinom.qint": "PROVED", "thm.pars.qbinom.quot2": "PROVED",
    "prop.pars.qbinom.symm": "PROVED",
    # Chapter 21: QBinomialFormulas
    "thm.pars.qbinom.binom1": "PROVED", "lem.prodrule.sum-ai-plus-bi": "PROVED",
    "thm.pars.qbinom.binom2": "PROVED", "thm.pars.qbinom.subsp-count": "PROVED",
    "lem.linalg.lin-ind-via-span": "PROVED",
    "lem.pars.qbinom.lin-ind-count": "PROVED",
    "lem.count.multijection": "PROVED", "prop.pars.qbinom.lim1": "PROVED",
    # Chapter 22: Permutations/Basics
    "def.perm.perm": "PROVED", "def.perm.Sn-iven": "PROVED",
    "prop.perm.Sf": "PROVED", "def.perm.notations": "PROVED",
    "def.perm.tij": "PROVED", "def.perm.si": "PROVED",
    "prop.perm.si.rules": "PROVED", "def.perm.cycs": "PROVED",
    "def.perm.invol": "PROVED",
    # Chapter 23: Inversions1
    "def.perm.invs": "PROVED", "prop.perm.lengths-k-small-k": "PROVED",
    "prop.perm.length.gf": "PROVED", "def.perm.lehmer1": "PROVED",
    "prop.perm.lehmer.l": "PROVED", "thm.perm.lehmer.bij": "PROVED",
    "def.perm.lehmer.lex-ord": "PROVED", "prop.perm.lehmer.lex-ord.total": "PROVED",
    "prop.perm.lehmer.lex": "PROVED",
    # Chapter 24: Inversions2
    "prop.perm.len.inv": "PROVED", "lem.perm.len.ssl": "PROVED",
    "prop.perm.lisitij": "PROVED", "thm.perm.len.redword1": "PROVED",
    "cor.perm.red.sigtau": "PROVED", "cor.perm.generated": "PROVED",
    "prop.perm.redword-lehmer": "PROVED",
    # Chapter 25: Signs
    "def.perm.sign": "PROVED", "prop.perm.sign.props": "PROVED",
    "cor.perm.sign.hom": "PROVED", "def.perm.even-odd": "PROVED",
    "cor.perm.altgp": "PROVED", "cor.perm.num-even": "PROVED",
    "prop.perm.sign.X": "PROVED",
    # Chapter 26: CycleDecomposition
    "thm.perm.dcd.main": "PROVED", "def.perm.cycs.cycs": "PROVED",
    "prop.perm.cycs.same": "PROVED", "prop.perm.cycs.sign": "PROVED",
    # Chapter 27: AlternatingSums
    "prop.binom.nhs": "PROVED", "lem.sign.cancel1": "PROVED",
    "lem.sign.cancel2": "PROVED", "lem.sign.cancel3": "PROVED",
    "def.root-of-unity.prim": "PROVED", "thm.sign.q-lucas": "PROVED",
    # Chapter 28: InclusionExclusion1
    "thm.pie.1": "PROVED", "thm.pie.count-sur": "PROVED",
    "cor.pie.count-sur.cors": "PROVED", "def.pie.dera": "PROVED",
    "thm.pie.count-der": "PROVED", "thm.pie.euler-tot": "PROVED",
    "thm.pie.2": "PROVED",
    # Chapter 29: BooleanMobiusInversion
    "thm.pie.moeb": "PROVED", "lem.pie.two-sets-altsum": "PROVED",
    # Chapter 30: SubtractiveMethods
    "thm.cancel.all-even": "PROVED", "lem.cancel.all-even.l1": "PROVED",
    "lem.cancel.all-even.l2": "PROVED",
    # Chapter 31: DeterminantsBasic
    "def.det.det": "PROVED", "prop.det.xiyj": "PROVED",
    "prop.det.xi+yj": "PROVED", "thm.det.transp": "PROVED",
    "thm.det.triang": "PROVED", "thm.det.rowop": "PROVED",
    "thm.det.colop": "PROVED", "cor.det.sig-row-col": "PROVED",
    "thm.det.detAB": "PROVED", "cor.det.scale-row-col": "PROVED",
    # Chapter 32: CauchyBinet
    "thm.det.CB": "PROVED", "def.det.sub": "PROVED",
    "thm.det.det(A+B)": "PROVED", "lem.det.minors-diag": "PROVED",
    "thm.det.det(A+D)": "PROVED", "prop.det.x+ai": "PROVED",
    "prop.det.charpol-explicit": "PROVED", "prop.det.pascal-LU": "PROVED",
    # Chapter 33: DesnanotJacobi
    "thm.det.vander": "PROVED", "lem.det.vander.a.pol": "PROVED",
    "prop.det.(xi+yj)n-1": "PROVED", "thm.det.laplace": "PROVED",
    "prop.det.laplace.0": "PROVED", "def.det.adj": "PROVED",
    "thm.det.adj.inverse": "PROVED", "thm.det.laplace-multi": "PROVED",
    "thm.det.des-jac-1": "PROVED", "thm.det.cauchy": "EXERCISE",
    "thm.det.des-jac-2": "PROVED", "thm.det.jacobi-complement": "PROVED",
    # Chapter 34: LGV1
    "def.lgv.lattice": "PROVED", "prop.lgv.1-paths.ct": "PROVED",
    "def.lgv.path-tups": "PROVED", "prop.lgv.2paths.count": "PROVED",
    "prop.lgv.jordan-2": "PROVED", "cor.lgv.binom-unimod": "PROVED",
    "prop.lgv.kpaths.count": "PROVED",
    # Chapter 35: LGV2
    "thm.lgv.kpaths.wt": "PROVED", "thm.lgv.kpaths.wt-dg": "PROVED",
    "cor.lgv.kpaths.wt-np": "PROVED",
    "cor.lgv.binom-det-nonneg": "PROVED",
    "cor.lgv.catalan-hankel-det-0": "EXERCISE",
    # Chapter 36: SF Definitions
    "def.sf.PS": "PROVED", "prop.sf.SN-acts": "PROVED",
    "prop.sf.SN-acts-by-alg-auts": "PROVED", "thm.sf.S-subalg": "PROVED",
    "def.sf.ring-of-symm": "PROVED", "def.sf.monomial": "PROVED",
    "def.sf.ehp": "PROVED", "prop.sf.en=0": "PROVED",
    "thm.sf.NG": "PROVED", "prop.sf.e-h-FPS": "PROVED",
    "thm.sf.ftsf": "PROVED", "lem.sf.simples-enough": "PROVED",
    # Chapter 37: MonomialSymmetric
    "def.sf.Npar": "PROVED", "prop.sf.Npar-as-par": "PROVED",
    "def.sf.sort": "PROVED", "def.sf.m": "PROVED",
    "prop.sf.ehp-through-m": "PROVED", "thm.sf.m-basis": "PROVED",
    "prop.sf.sigma-pol-coeff": "PROVED",
    # Chapter 38: SchurBasics
    "def.sf.alternants": "PROVED", "def.sf.ydiag": "PROVED",
    "def.sf.ytab": "PROVED", "def.sf.ssyt": "PROVED",
    "def.sf.ytab.xT": "PROVED", "def.sf.schur": "PROVED",
    "thm.sf.schur-symm": "PROVED", "def.sf.par-subset": "PROVED",
    "def.sf.skew-diag": "PROVED", "lem.sf.skew-diag.convexity": "PROVED",
    "def.sf.skew-tab": "PROVED", "def.sf.skew-ssyt": "PROVED",
    "lem.sf.skew-ssyt.increase": "PROVED", "def.sf.ytab.skew-xT": "PROVED",
    "def.sf.skew-schur": "PROVED", "thm.sf.skew-schur-symm": "PROVED",
    # Chapter 39: LittlewoodRichardson
    "def.sf.tuple-addition": "PROVED", "def.sf.content": "PROVED",
    "def.sf.col-tab": "PROVED", "def.sf.yamanouchi": "PROVED",
    "thm.sf.lr-zy": "PROVED", "lem.sf.stemb-lem": "PROVED",
    "lem.sf.tab-greater-i": "PROVED", "def.cring.reg": "PROVED",
    "lem.cring.reg.cancel": "PROVED", "lem.sf.arho-reg": "PROVED",
    "lem.sf.alternant-0": "PROVED",
    # Chapter 40: PieriJacobiTrudi
    "def.sf.strips": "PROVED", "prop.sf.strips.entries": "PROVED",
    "thm.sf.pieri": "EXERCISE", "thm.sf.jt-h": "PROVED",
    "thm.sf.jt-e": "EXERCISE",
    # Chapter 41: Details/InfiniteProducts1
    "lem.fps.prod.irlv.cong-div": "PROVED",
    "lem.fps.prods-mulable-subfams-appr": "PROVED",
    "lem.fps.prods-mulable-rules.SW1.lem1": "PROVED",
    # Chapter 42: Details/InfiniteProducts2
    "lem.fps.subs.rule-infprod-fin": "PROVED",
    # Chapter 43: Details/DominoTilings
    "def.gf.weighted-set.domino.Rn3.ABC": "PROVED",
    "prop.gf.weighted-set.domino.Rn3.ABC": "PROVED",
    # Chapter 44: Details/Limits
    "prop.fps.lim.sum-prod.K": "PROVED", "prop.fps.lim.sum-prod.L": "PROVED",
    # Chapter 45: Details/LaurentSeries
    "lem.fps.laure.xa": "PROVED", "prop.fps.laure.xk": "PROVED",
}

# ── Lean file key -> actual path mapping ─────────────────────────────────
LEAN_FILE_MAP = {
    "FPS/Notations": "FPS/NotationsExamples",
    "FPS/FPSDefinition": "FPSDefinition",
    "FPS/DividingFPS": "DividingFPS",
    "FPS/LaurentSeries": "LaurentSeries",
    "Determinants/BasicProperties": "DeterminantsBasic",
    "Determinants/CauchyBinet": "CauchyBinet",
    "Determinants/DesnanotJacobi": "DesnanotJacobi",
    "Partitions/QBinomialBasic": "QBinomialBasic",
    "Partitions/PentagonalJacobi": "PentagonalJacobi",
    "Details/InfiniteProducts1": "FPS/InfiniteProducts1",
    "Details/LaurentSeries": "FPS/LaurentSeries",
    "SignedCounting/InclusionExclusion2": "SignedCounting/BooleanMobiusInversion",
}


def load_manifest():
    with open(MANIFEST) as f:
        data = json.load(f)
    chapter_to_file = {}
    target_to_chapter = {}
    for ch in data["chapters"]:
        chid = ch["id"]
        sp = ch["source_path"].replace("AlgebraicCombinatorics/tex/", "").replace(".tex", "")
        chapter_to_file[chid] = sp
        for t in ch["target_theorems"]:
            target_to_chapter[t] = chid
    return data, chapter_to_file, target_to_chapter


def main():
    manifest_data, chapter_to_file, target_to_chapter = load_manifest()

    # Group targets by manifest file key
    file_targets = defaultdict(list)
    for t, chid in target_to_chapter.items():
        fk = chapter_to_file[chid]
        file_targets[fk].append(t)

    all_file_keys = sorted(set(chapter_to_file.values()))

    # Verify all targets have statuses
    missing = [t for t in target_to_chapter if t not in TARGET_STATUSES]
    if missing:
        print(f"WARNING: {len(missing)} targets missing status: {missing}")

    # ── Cluster layout ────────────────────────────────────────────────────
    clusters = [
        ("FPS Foundations", "#dce8f5", [
            "FPS/CommutativeRings", "FPS/Notations", "FPS/FPSDefinition",
            "FPS/DividingFPS", "FPS/Polynomials", "FPS/Substitution",
            "FPS/Derivatives", "FPS/Multivariate", "FPS/Limits", "FPS/XnEquivalence",
        ]),
        ("Infinite Products & Exp/Log", "#ccdcf0", [
            "FPS/InfiniteProducts1", "FPS/InfiniteProducts2",
            "FPS/ExpLog", "FPS/NonIntegerPowers",
        ]),
        ("FPS Applications", "#c0d4ea", [
            "FPS/IntegerCompositions", "FPS/WeightedSets",
        ]),
        ("Laurent Series", "#ddd0e8", [
            "FPS/LaurentSeries",
        ]),
        ("Partitions & q-Binomials", "#eeded0", [
            "Partitions/Basics", "Partitions/QBinomialFormulas",
            "Partitions/QBinomialBasic", "Partitions/PentagonalJacobi",
        ]),
        ("Determinants & LGV", "#cce0cc", [
            "Determinants/BasicProperties", "Determinants/CauchyBinet",
            "Determinants/DesnanotJacobi", "Determinants/LGV1", "Determinants/LGV2",
        ]),
        ("Permutations", "#eee4c0", [
            "Permutations/Basics", "Permutations/Inversions1",
            "Permutations/Inversions2", "Permutations/Signs",
            "Permutations/CycleDecomposition",
        ]),
        ("Signed Counting", "#d0e8d0", [
            "SignedCounting/AlternatingSums", "SignedCounting/InclusionExclusion1",
            "SignedCounting/InclusionExclusion2", "SignedCounting/SubtractiveMethods",
        ]),
        ("Symmetric Functions", "#e8cccc", [
            "SymmetricFunctions/Definitions", "SymmetricFunctions/MonomialSymmetric",
            "SymmetricFunctions/SchurBasics", "SymmetricFunctions/LittlewoodRichardson",
            "SymmetricFunctions/PieriJacobiTrudi",
        ]),
        ("Details", "#d8d8d8", [
            "Details/Limits", "Details/InfiniteProducts2", "Details/DominoTilings",
            "Details/InfiniteProducts1", "Details/LaurentSeries",
        ]),
    ]

    STATUS_COLORS = {
        "PROVED":      "#2e7d32",
        "EXERCISE":    "#e65100",
    }

    # ── Layout parameters ────────────────────────────────────────────────
    target_sq = 0.18
    target_pad = 0.04
    file_pad = 0.12
    file_title_h = 0.22
    file_gap_x = 0.15
    file_gap_y = 0.12
    cluster_pad = 0.20
    cluster_title_h = 0.30
    cluster_gap_x = 0.25
    cluster_gap_y = 0.25

    def file_box_size(fk):
        targets = file_targets.get(fk, [])
        nt = len(targets)
        if nt == 0:
            return 0.8, file_title_h + 2 * file_pad + target_sq
        cols = min(nt, 5)
        rows = (nt + cols - 1) // cols
        w = cols * (target_sq + target_pad) - target_pad + 2 * file_pad
        h = rows * (target_sq + target_pad) - target_pad + file_title_h + 2 * file_pad
        return max(w, 0.8), h

    def cluster_size(cfiles):
        ncols = 2
        nrows = (len(cfiles) + ncols - 1) // ncols
        max_w = [0.0] * ncols
        row_h = [0.0] * nrows
        for fi, fk in enumerate(cfiles):
            c, r = fi % ncols, fi // ncols
            fw, fh = file_box_size(fk)
            max_w[c] = max(max_w[c], fw)
            row_h[r] = max(row_h[r], fh)
        cw = sum(max_w) + (ncols - 1) * file_gap_x + 2 * cluster_pad
        ch = sum(row_h) + (nrows - 1) * file_gap_y + cluster_title_h + 2 * cluster_pad
        return cw, ch, max_w, row_h

    cluster_grid = [
        (0, 0), (1, 0), (2, 0), (3, 0),
        (0, 1), (1, 1), (2, 1),
        (0, 2), (1, 2), (2, 2),
    ]

    grid_col_w = [0.0] * 4
    grid_row_h = [0.0] * 3
    for ci, (cname, cbg, cfiles) in enumerate(clusters):
        if ci >= len(cluster_grid):
            break
        gc, gr = cluster_grid[ci]
        cw, ch, _, _ = cluster_size(cfiles)
        grid_col_w[gc] = max(grid_col_w[gc], cw)
        grid_row_h[gr] = max(grid_row_h[gr], ch)

    total_w = sum(grid_col_w) + 3 * cluster_gap_x + 1.0
    total_h = sum(grid_row_h) + 2 * cluster_gap_y + 1.5

    fig, ax = plt.subplots(1, 1, figsize=(total_w, total_h))
    ax.set_xlim(-0.3, total_w - 0.7)
    ax.set_ylim(-0.3, total_h - 0.7)
    ax.set_aspect('equal')
    ax.axis('off')
    fig.patch.set_facecolor('white')

    # Title
    total_targets = len(TARGET_STATUSES)
    total_proved = sum(1 for s in TARGET_STATUSES.values() if s == "PROVED")
    pct_exact = total_proved / total_targets

    ax.text(total_w / 2 - 0.5, total_h - 0.9,
            f"AlgebraicCombinatorics \u2014 Target Theorem Status ({total_proved}/{total_targets} proved, {pct_exact:.1%})",
            fontsize=11, fontweight='bold', fontfamily='sans-serif',
            ha='center', va='bottom', color="#222222")
    ax.text(total_w / 2 - 0.5, total_h - 1.15,
            "Each square = one target theorem",
            fontsize=7, fontfamily='sans-serif',
            ha='center', va='bottom', color="#666666")

    # Draw clusters
    for ci, (cname, cbg, cfiles) in enumerate(clusters):
        if ci >= len(cluster_grid):
            break
        gc, gr = cluster_grid[ci]
        cw, ch, col_widths, row_heights = cluster_size(cfiles)

        cx = sum(grid_col_w[:gc]) + gc * cluster_gap_x + 0.2
        cy = total_h - 1.5 - sum(grid_row_h[:gr+1]) - gr * cluster_gap_y

        ax.add_patch(FancyBboxPatch(
            (cx, cy), cw, ch, boxstyle="round,pad=0.05",
            facecolor=cbg, edgecolor="#999999", linewidth=0.7, alpha=0.8))
        ax.text(cx + cluster_pad, cy + ch - cluster_pad * 0.3, cname,
                fontsize=7, fontweight='bold', fontfamily='sans-serif',
                va='top', ha='left', color="#333333")

        ncols = 2
        for fi, fk in enumerate(cfiles):
            fc, fr = fi % ncols, fi // ncols
            fw, fh = file_box_size(fk)

            fx = cx + cluster_pad + sum(col_widths[:fc]) + fc * file_gap_x
            fy = cy + ch - cluster_title_h - cluster_pad - sum(row_heights[:fr+1]) - fr * file_gap_y

            ax.add_patch(FancyBboxPatch(
                (fx, fy), fw, fh, boxstyle="round,pad=0.03",
                facecolor="white", edgecolor="#bbbbbb", linewidth=0.4, alpha=0.9))

            short_name = fk.split("/")[-1]
            targets = file_targets.get(fk, [])
            n_proved = sum(1 for t in targets if TARGET_STATUSES.get(t) == "PROVED")
            ax.text(fx + file_pad, fy + fh - file_pad * 0.6,
                    f"{short_name} ({n_proved}/{len(targets)})",
                    fontsize=5, fontfamily='sans-serif', fontweight='bold',
                    va='top', ha='left', color="#444444")

            tcols = min(len(targets), 5) if targets else 1
            for ti, t in enumerate(targets):
                tc, tr = ti % tcols, ti // tcols
                tx = fx + file_pad + tc * (target_sq + target_pad)
                ty = fy + fh - file_title_h - file_pad - tr * (target_sq + target_pad) - target_sq

                status = TARGET_STATUSES.get(t, "NOT_PRESENT")
                color = STATUS_COLORS.get(status, "#9e9e9e")

                ax.add_patch(FancyBboxPatch(
                    (tx, ty), target_sq, target_sq,
                    boxstyle="round,pad=0.01",
                    facecolor=color, edgecolor="#666666", linewidth=0.3))

    # Legend
    leg_x = total_w - 2.8
    leg_y = 0.1
    leg_w = 2.2
    leg_h = 1.0
    ax.add_patch(FancyBboxPatch(
        (leg_x, leg_y), leg_w, leg_h, boxstyle="round,pad=0.05",
        facecolor="#f5f5f5", edgecolor="#aaaaaa", linewidth=0.7))
    ax.text(leg_x + 0.1, leg_y + leg_h - 0.08, "Target Status",
            fontsize=7, fontweight='bold', fontfamily='sans-serif', va='top', color="#333333")

    n_exercise = sum(1 for s in TARGET_STATUSES.values() if s == 'EXERCISE')
    legend_items = [
        (f"proved ({total_proved})", "#2e7d32"),
        (f"exercise ({n_exercise})", "#e65100"),
    ]
    for li, (lbl, bg) in enumerate(legend_items):
        lx = leg_x + 0.12
        ly = leg_y + leg_h - 0.40 - li * 0.30
        ax.add_patch(FancyBboxPatch(
            (lx, ly), target_sq, target_sq,
            boxstyle="round,pad=0.01",
            facecolor=bg, edgecolor="#666666", linewidth=0.3))
        ax.text(lx + target_sq + 0.08, ly + target_sq / 2, lbl,
                fontsize=5.5, fontfamily='sans-serif', va='center', color="#333333")

    ax.text(leg_x + 0.12, leg_y + 0.10,
            f"{total_proved}/{total_targets} targets proved ({pct_exact:.1%})",
            fontsize=6, fontfamily='sans-serif', color="#333333")

    out = str(Path(__file__).resolve().parent.parent / "assets" / "dep_graph_theorems.png")
    plt.savefig(out, dpi=150, bbox_inches='tight', facecolor='white', pad_inches=0.2)
    print(f"Saved {out}")


if __name__ == "__main__":
    main()
