-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/StageJ.lean: a stage of a proximity test below the Johnson radius: the tests on its
numbers, the one condition on counts, and what follows for lists and counts of its tables.

A stage is given in numbers (`Sg`, OnBytes/Slice/Stage.lean). Its codes have the laws and a
distance if its sizes are in order (OnBytes/Slice/Numbers.lean). The list sizes come from the
Johnson bound, which the proof library proves from the distance alone (`ld_list_johnson`,
Cb/Ld/LdRelJohnsonProofs.lean). Definitions, statements and proofs.
Main names:
  `stageOf g t`: the stage with the sizes of a group of the planner, and t draws.
  `radiusOf σ g`: the planner's radius of a group, as a function of the setting and the group.
  `InJ s e`, `lstJ s e`: the radius e is below the stage's distance and below the Johnson radius
    for its positions and distance; the Johnson bound on a list there.
  `CountsAt s e bC bZ`: the condition that is asked: at the radius e a line through two words has
    at most bC exceptional points for one main row, and at most bZ for one mask row repeated to
    the main rows' length.
  `sizedB`, `inJB`, `sized_of`, `inJ_of`: tests that can be evaluated for `Sg.Sized` and `InJ`.
  `listJ`, `listJ_of`: the Johnson bound for a code with the laws and a distance; at a stage.
  `errOK_joh`, `foldNums_joh`: the numbers of a folding: lists by the Johnson bound, counts as
    given.
  `counts_cIn`, `baseCodes_joh`: the tables before a fold; what the last step asks of its codes.
  `decCsFit`: whether the sizes of two stages fit can be evaluated.
Limits: `CountsAt` is not proved here. Below half a stage's distance
OnBytes/Slice/BlocksJohnson.lean proves it, for sizes in order and codes that each have a
coefficient, at the counts `Sg.cntC` and `Sg.cntZ` (`Sg.countsAt_src`). At a radius other than 0
below the Johnson radius OnBytes/Slice/CountsFloor.lean derives it, for sizes in order and codes
of at least two coefficients, at counts of its own, from the theorem on codes, taken as given
(`Sg.countsAt_floor`, under the hypothesis `Cb.BCHKS46At`). A main code over the base field is
read as a code over the extension field. A group's number of slots is not read: the stage is the
group's only where that number is 1.
See also: OnBytes/Slice/BlocksJohnson.lean states `InJ`, `lstJ`, `CountsAt` and the seven lemmas
from `listJ` to `baseCodes_joh` over the same terms, under the names `Sg.InJ`, `Sg.lstJ`,
`Sg.CountsAt`, `Fit.listJ` and so on. They are stated here so that this file imports nothing
beyond the files named below.

-/
import Cb.Gen.JohnsonListProofs
import Cb.Ld.LdRelJohnsonProofs
import OnBytes.Slice.NumbersHalf
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.CsData
import OnBytes.Slice.Base
import OnBytes.Params.Group

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Params OnBytes.Slice Cb

/-- A stage with the sizes of a group of the planner, and t draws. -/
def stageOf (g : GroupSize) (t : ℕ) : Sg :=
  ⟨⟨g.main.logN, g.main.ell, g.main.r⟩, ⟨g.mask.logN, g.mask.ell, g.mask.r⟩, g.h, g.k - g.h, t⟩

/-- The planner's radius of a group under the rule of the Johnson radius: the upper end of the
group's distance times the main code's length, rounded down. -/
def radiusOf (σ : Setting) (g : GroupSize) : ℕ :=
  ((analysisOfM σ g).mainAt.delta * Bound.ofNat (wordOf g.main).n).hi.floor

/-- The radius is below the stage's distance and below the Johnson radius. -/
def InJ (s : Sg) (e : ℕ) : Prop := e < s.d ∧ InJohnson (2 ^ s.C.a) s.d e

/-- The Johnson bound on a list at the stage's number of positions and its distance. -/
def lstJ (s : Sg) (e : ℕ) : ℕ := listMax (2 ^ s.C.a) s.d e

/-- The counts of exceptional points of a line, for one main row and one mask row. -/
structure CountsAt (s : Sg) (e bC bZ : ℕ) : Prop where
  main : s.cM.MCAat e bC
  mask : s.cZ.MCAat e bZ

/-- The sizes of a stage are in order: a test. -/
def sizedB (s : Sg) : Bool :=
  decide (s.C.a ≤ 32) && decide (s.Z.a ≤ s.C.a) && decide (s.C.r + s.C.l ≤ 2 ^ s.C.a) &&
    decide (s.Z.r + s.Z.l ≤ 2 ^ s.Z.a)

theorem sized_of {s : Sg} (h : sizedB s = true) : s.Sized := by
  simp only [sizedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The radius is below the distance and below the Johnson radius: a test. -/
def inJB (s : Sg) (e : ℕ) : Bool :=
  decide (e < s.d) && decide (2 ^ s.C.a * (2 ^ s.C.a - s.d) < (2 ^ s.C.a - e) ^ 2)

theorem inJ_of {s : Sg} {e : ℕ} (h : inJB s e = true) : InJ s e := by
  simp only [inJB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

/-- Whether the sizes of two stages fit can be evaluated. -/
instance decCsFit (s s' : Sg) : Decidable (CsFit s s') :=
  decidable_of_iff
    (2 ^ (s'.h + s'.g) * s'.C.l = s.C.l ∧ 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ s'.h * s'.Z.l ∧
      s'.C.l = 2 ^ Fmt.M1.lg s'.C.l ∧ s'.Z.l = 2 ^ Fmt.M1.lg s'.Z.l ∧ s.Z.a ≤ s.C.a)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P]

/-- The Johnson bound for a code with the laws and the distance d. -/
theorem listJ {C : LdCode E P} {d : ℕ} (h : Fit C d) {e : ℕ}
    (hj : InJohnson (Fintype.card P) d e) : C.ListAt e (listMax (Fintype.card P) d e) :=
  ld_list_johnson E P C d e h.laws h.dist hj

/-- The numbers of a folding below the Johnson radius. -/
theorem errOK_joh (Y : SumPar E P) (d e bC bZ bW : ℕ) (h : Spec.CodesOK E P Y.C Y.Z Y.Zw d e)
    (hj : InJohnson (Fintype.card P) d e) (hbC : Y.C.MCAat e bC) (hbZ : Y.Z.MCAat e bZ)
    (hbW : Y.Zw.MCAat e bW) :
    Y.ErrOK e (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW) :=
  have hC : Fit Y.C d := ⟨h.1.1, h.2.1.1⟩
  have hZ : Fit Y.Z d := ⟨h.1.2.1, h.2.1.2.1⟩
  have hW : Fit Y.Zw d := ⟨h.1.2.2, h.2.1.2.2⟩
  { list := fun _ _ => listJ ((hC.il _).pair ((hZ.il _).pair (hW.il _))) hj
    mcaC := fun _ _ _ => hC.mcaRows hbC _
    mcaS := fun _ _ _ => hZ.mcaRows hbZ _
    mcaW := fun _ _ _ => hW.mcaRows hbW _ }

end

variable {s : Sg}

theorem card_Ps (s : Sg) : Fintype.card s.Ps = 2 ^ s.C.a := Fintype.card_fin _

/-- The Johnson bound for a code on the stage's positions with the stage's distance. -/
theorem listJ_of {C : LdCode GE s.Ps} (h : Fit C s.d) {e : ℕ} (hj : InJ s e) :
    C.ListAt e (lstJ s e) := by
  have h1 := listJ h (e := e) (by rw [card_Ps]; exact hj.2)
  rwa [card_Ps] at h1

/-- The numbers of a fold below the Johnson radius, under the condition on counts. -/
theorem foldNums_joh (hs : s.Sized) {e bC bZ : ℕ} (hj : InJ s e) (hc : CountsAt s e bC bZ) :
    (s.par 0).ErrOK e (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) := by
  have h := errOK_joh (s.par 0) s.d e bC bZ bZ (Sg.codesOK hs hj.1)
    (by rw [card_Ps]; exact hj.2) hc.main hc.mask hc.mask
  rwa [card_Ps] at h

/-- The tables before the fold: at most bC + bZ exceptional points. -/
theorem counts_cIn (h : s.Sized) {e bC bZ : ℕ} (hc : CountsAt s e bC bZ) :
    s.cIn.MCAat e (bC + bZ) :=
  ld_mca_pair GE s.Ps _ _ e _ _ ((Sg.fit_cM h).mcaRows hc.main _) ((Sg.fit_cZ h).mcaRows hc.mask _)

/-- What the last step asks of its codes. -/
theorem baseCodes_joh (h : s.Sized) {e bC bZ : ℕ} (hj : InJ s e) (hc : CountsAt s e bC bZ) :
    BaseCodes s e (bC + bZ) (lstJ s e) :=
  ⟨(Sg.fit_cIn h).laws, counts_cIn h hc, listJ_of ((Sg.fit_cIn h).il Bool) hj⟩

end Johnson.Top.H

#print axioms Johnson.Top.H.listJ_of
#print axioms Johnson.Top.H.foldNums_joh
#print axioms Johnson.Top.H.baseCodes_joh
