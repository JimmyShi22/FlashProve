-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJohn.lean: proximity tests for Reed-Solomon codes over the field
with p = 2^64 - 2^32 + 1 elements, at radii below the Johnson radius (`GlJ` does not ask a radius
within half the distance:
Cb/Gl/GlLdJ.lean): most hypotheses on codes that the generic theorems on these tests take are
derived under the hypotheses below, mutual correlated agreement from one named hypothesis, the
others without it.

Towers and tests on groups below the Johnson radius, over p = 2^64 - 2^32 + 1 with plain
Reed-Solomon codes: in the records "below the Johnson radius" every clause on a code is a theorem,
but for `G.Fits` and `Sh.view.Laws`, which speak of the codes' words and stay asked: lists proved,
agreement from the one hypothesis BCHKS46F F.

Definitions, statements (in `Cb.Gl.Spec`) and proofs (an assembly).
A tower (`LdTowJ`) is a base case, or a fold and a code switch followed by a tower; a test on a
group is a record `LdRunD` (Cb/Ld/LdLinCloseRuns.lean); e is below the Johnson radius if
`InJohnson` n d e holds: n (n - d) < (n - e)^2 (Cb/Gen/JohnsonList.lean).
"Lists" are bounds of list decoding (`LdCode.ListAt e L`: every word has at most L codewords within
e long positions); "agreement" is mutual correlated agreement on lines (`LdCode.MCAat e b`: for any
two words at most b values θ are exceptional); both in Cb/Ld/LdRel.lean; of a fold's codes agreement
is asked for every number of rows: `LdCode.MCArows`, Cb/Ld/LdRelRows.lean.
`Cb.BCHKS46F` is defined in Cb/Gen/CodeListRSF.lean.
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
The records: Cb/Obj/LdObjectTowerJohn.lean. F, E: Cb/Gl/GlField.lean. The codes: Cb/Gl/GlLdJ.lean
(`GlJ C d t e bad`: built from families of plain Reed-Solomon codes; the counts bad are in the
towers as data) and Cb/Gl/GlLd.lean (`GlC C d t`) where no agreement is asked. The analogue within a
third of the distances: Cb/GlVal/GlThird.lean (`TowGl`, `TowGGl`), `RunGl` (Cb/Gl/GlOff.lean).

Main names:
  `Spec.glJ_fold`: a fold: `Y.John d e t bC bZ bW` from `GlJ` of its three codes. Under BCHKS46F F.
    Stays: `InJohnson` |P| d e; challenges, degree, packing (`Y.PackOK`, `Y.QwDeg`).
  `Spec.glJ_switch`: a code switch: `D.John d' e' t'` from `GlC` of its two codes: a list only:
    nothing assumed beyond the hypotheses of the statement and whatever the arguments hold as
    proofs. Stays: P, P' are not empty; `InJohnson`
    |P'| d' e'; samples, the batching's zero-evader (`D.Zb.OK`), privacy.
  `TowGlJ T`, `Spec.glJ_tower`: a whole tower, any number of stages, by the recursion of `T.John`:
    the three codes of each fold are `GlJ` with the counts that are in T; each new code is `GlC`;
    the last code is `GlJ`; the Johnson condition at every joint; challenges, degree, packing
    (`PackOK`, `QwDeg`), samples, the batching's zero-evader (`Zb.OK`), privacy. BCHKS46F F →
    `TowGlJ T` → `T.John`.
  `TowGGlJ T`, `Spec.glJ_towerG`: on a group's complex: plain (the complex itself: `GlJ.fam`), or
    shaped (base code, mask code and the fresh mask's code `GlJ`; asked of the shape: the law of its
    re-arrangement, where rows stand, at least one variable; the laws of base and mask code, the
    fold's main code, the switch's input code are derived). G.P is not empty. BCHKS46F F →
    `TowGGlJ T` → `T.John`.
  `RunGlJ D`, `Spec.glJ_run`: a test on a group: its whole test is such a tower, its number of
    positions the tower's; its bound on lists is `listMax` |G.P| d G.e; each member's code at the
    group's positions is `GlC` with distance d; `InJohnson` |G.P| d G.e; `Fits`; the bridge's
    evader.
    BCHKS46F F → `RunGlJ D` → ∃ T d, `D.PreJ T d`.

Where BCHKS46F F enters: agreement of the folds' three codes at all stages, and of the last code.
Nowhere else: every list is the proved Johnson bound.

Limits: this file does not say that the conditions can be met (of `GlJ` alone, a toy: `glJ8`,
Cb/GlVal/GlGuardJohn.lean: at the radius 3 of the distance 6: not within half the distance), or
that the counts are below the size of the field. It says nothing beyond the Johnson radius, and
nothing on lengths above 2^32.


Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlLdJProofs
import Cb.Obj.LdObjectTowerJohn
import Cb.GlVal.GlThird

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- All codes of a tower are built from plain Reed-Solomon families; the Johnson condition at every
joint; what does not speak of codes. By recursion, as `LdTowJ.John`. -/
def TowGlJ : {a : LdJoint E} → LdTowJ a → Prop
  | _, .base a _ _ d b => GlJ a.C d 0 a.e b ∧ InJohnson (Fintype.card a.P) d a.e
  | _, @LdTowJ.step _ _ _ P P' _ _ _ _ _ Y sl e S d bC bZ bW e' d' rest =>
      (GlJ Y.C d 0 e bC ∧ GlJ Y.Z d 0 e bZ ∧ GlJ Y.Zw d S.ts e bW ∧
        InJohnson (Fintype.card P) d e ∧ Function.Injective (Y.reform sl).val ∧
        2 ≤ (Y.reform sl).n ∧ (Y.reform sl).PackOK ∧ (Y.reform sl).QwDeg) ∧
      (GlC S.Cnew d' rest.toC.q ∧ InJohnson (Fintype.card P') d' e' ∧ (S.D e).Zo.OK ∧
        (S.D e).Zb.OK ∧ (S.D e).Zo.PrivateSim E) ∧
      TowGlJ rest

/-- The same on a group's complex. -/
def TowGGlJ {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
    {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} : LdTowGJ G Sb sl Z → Prop
  | .plain T => TowGlJ T
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ P' _ _ Sh Sw d bC bZ bW e' d' rest =>
      (Sh.view.Laws ∧
        (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
        (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
        (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
        1 ≤ Sh.h + Sh.g) ∧
      (GlJ Sh.Cb d 0 G.e bC ∧ GlJ Sh.Zb d 0 G.e bZ ∧ GlJ Sh.par.Zw d Sw.ts G.e bW ∧
        InJohnson (Fintype.card G.P) d G.e ∧ Function.Injective Sh.par.val ∧ 2 ≤ Sh.par.n ∧
        Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
      (GlC (Sw.D G.e).Cout d' rest.toC.q ∧ InJohnson (Fintype.card P') d' e' ∧ (Sw.D G.e).Zo.OK ∧
        (Sw.D G.e).Zb.OK ∧ (Sw.D G.e).Zo.PrivateSim E) ∧
      TowGlJ rest

/-- A test on a group, all of whose codes are built from plain Reed-Solomon families, below the
Johnson radius. -/
def RunGlJ {S : Sig E} (D : LdRunD S) : Prop :=
  ∃ (Tw : D.TowJ) (d : ℕ), D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧
    D.L = listMax (Fintype.card D.G.P) d D.G.e ∧
    (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
    InJohnson (Fintype.card D.G.P) d D.G.e ∧ D.G.Fits ∧ D.Z.OK ∧ TowGGlJ Tw

namespace Spec

/-- A fold of a tower, under the premise `Cb.BCHKS46F F`, which this file does not prove. -/
def glJ_fold : Prop :=
  Cb.BCHKS46F F →
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t bC bZ bW : ℕ), GlJ Y.C d 0 e bC →
    GlJ Y.Z d 0 e bZ → GlJ Y.Zw d t e bW → InJohnson (Fintype.card P) d e →
    Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg → Y.John d e t bC bZ bW

/-- A code switch of a tower: nothing assumed beyond the hypotheses of the statement and whatever
the arguments hold as proofs. -/
def glJ_switch : Prop :=
  ∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (d' e' t' : ℕ),
    GlC D.Cout d' t' → GlC D.Cin 0 0 → InJohnson (Fintype.card P') d' e' → D.Zo.OK → D.Zb.OK →
    D.Zo.PrivateSim E → D.John d' e' t'

/-- A whole tower, any number of stages, under the premise `Cb.BCHKS46F F`, which this file does not
prove. -/
def glJ_tower : Prop := Cb.BCHKS46F F → ∀ (a : LdJoint E) (T : LdTowJ a), TowGlJ T → T.John

/-- The same on a group's complex, under the same premise `Cb.BCHKS46F F`. -/
def glJ_towerG : Prop :=
  Cb.BCHKS46F F →
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    TowGGlJ T → T.John

/-- A test on a group, under the premise `Cb.BCHKS46F F`, which this file does not prove. -/
def glJ_run : Prop :=
  Cb.BCHKS46F F → ∀ (S : Sig E) (D : LdRunD S), RunGlJ D → ∃ (T : D.TowJ) (d : ℕ), D.PreJ T d

end Spec

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_fold : Spec.glJ_fold := fun H P _ Y d e t bC bZ bW hC hZ hW hJ hi hn hp hq =>
  have gC := glC_code P _ d 0 (glJ_glC P _ d 0 e bC hC)
  have gZ := glC_code P _ d 0 (glJ_glC P _ d 0 e bZ hZ)
  have gW := glC_code P _ d t (glJ_glC P _ d t e bW hW)
  { lawsC := gC.1, lawsZ := gZ.1, lawsW := gW.1, distC := gC.2.2.2.1, distZ := gZ.2.2.2.1,
    distW := gW.2.2.2.1, john := hJ
    mcaC := glJ_rows H P _ d 0 e bC hC hJ,
      mcaZ := glJ_rows H P _ d 0 e bZ hZ hJ,
      mcaW := glJ_rows H P _ d t e bW hW hJ
    inj := hi, deg := hn, pack := hp, qw := hq,
      zk := (glC_code P Y.Cw d t (.il _ (glJ_glC P _ d t e bW hW))).2.2.2.2 }

theorem glJ_switch : Spec.glJ_switch := fun P P' _ _ _ _ _ _ d' _ t' hO hI hJ hZo hZb hp =>
  ⟨(glC_code P' _ d' t' hO).1, (glC_code P' _ d' t' hO).2.2.2.1, hJ, (glC_code P _ 0 0 hI).1,
    (glC_code P' _ d' t' hO).2.2.1, hZo, hZb, hp, (glC_code P' _ d' t' hO).2.2.2.2⟩

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_tower : Spec.glJ_tower := by
  intro H a T
  induction T with
  | base a t cov d b =>
    rintro ⟨h, hJ⟩
    have g := glC_code a.P a.C d 0 (glJ_glC a.P a.C d 0 a.e b h)
    exact ⟨g.1, g.2.2.2.1, hJ, (glJ_mca H a.P a.C d 0 a.e b h hJ).2, g.2.1⟩
  | step Y sl e S d bC bZ bW e' d' rest ih =>
    rintro ⟨⟨hC, hZ, hW, hJ, hi, hn, hp, hq⟩, ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩
    refine ⟨glJ_fold H _ (Y.reform sl) d e S.ts bC bZ bW hC hZ hW hJ hi hn hp hq,
      glJ_switch _ _ _ (S.D e) d' e' rest.toC.q hN ?_ hJ' hZo hZb hP,
      ih hr⟩
    exact glC_mono _ _ d 0 0 0
      (.pair (glJ_glC _ _ d 0 e bC hC)
        (.pair (glJ_glC _ _ d 0 e bZ hZ)
          (glC_mono _ _ d S.ts d 0 (glJ_glC _ _ d S.ts e bW hW) le_rfl (Nat.zero_le _))))
      (Nat.zero_le _) le_rfl

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_towerG : Spec.glJ_towerG := by
  intro H B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact glJ_tower H _ T h
  | shaped Sh Sw d bC bZ bW e' d' rest =>
    obtain ⟨⟨hv, hm1, hm2, hz, h1⟩, ⟨hB, hZ, hW, hJ, hi, hn, hp, hq⟩,
        ⟨hN, hJ', hZo, hZb, hP⟩, hr⟩ := h
    have hC : GlJ Sh.par.C d 0 G.e bC := .il _ hB
    have hI : GlC (Sw.D G.e).Cin 0 0 :=
      glC_mono _ _ d 0 0 0
        (.pair (glJ_glC _ _ d 0 G.e bC hC)
          (.pair (glJ_glC _ _ d 0 G.e bZ hZ)
            (glC_mono _ _ d Sw.ts d 0 (glJ_glC _ _ d Sw.ts G.e bW hW) le_rfl (Nat.zero_le _))))
        (Nat.zero_le _) le_rfl
    exact ⟨⟨hv,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bC hB)).1,
      (glC_code _ _ d 0 (glJ_glC _ _ d 0 G.e bZ hZ)).1,
      fun r => by
        split
        · next b hb => exact hm1 r b hb
        · next j hj => exact hm2 r j hj, hz, h1⟩, glJ_fold H _ Sh.par d G.e Sw.ts bC bZ bW hC hZ hW hJ hi hn hp hq, glJ_switch _ _ _ (Sw.D G.e) d' e' rest.toC.q hN hI hJ' hZo hZb hP, glJ_tower H _ rest hr⟩

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_run : Spec.glJ_run := by
  rintro H S D ⟨Tw, d, h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨Tw, d,
    ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
      fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, hJ, hZ, hF,
      glJ_towerG H _ S D.G D.Sb D.sl D.Z Tw hT⟩⟩

end Cb.Gl
