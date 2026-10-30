-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanPaid.lean: TWELVE OF K4's 24 CLOSED TESTS ARE NO TESTS ANY MORE. Where five
parts of the public parameters Z are the written values (`WrittenAt Z`,
Johnson/Road/K4/K4PlanTied.lean) and Z.p.X is the programs' public data of files with the public
core (the goals' scope gives both), `commonFastB Z` and the eleven `seamFastB Z g`
(Johnson/Road/K4/K4PlanFast.lean) accept: by the closed facts that Lean's kernel has decided at the
written values (K4PlanWritten.lean, K4PlanWrittenShapes.lean), three theorems in scope
(`nmFit_of_core`, `planFit_of_core`, `pairs_of_planFit`) and `seamArr_of_closed`. So
`K4PlanFit` takes one test, `firstFastB Z p.g`. Four theorems, without an evaluation.

  `shapesTied_at`: the tie of shapes accepts at Z's letters, in `commonFastB`'s own form.
  `common_paid`: `commonFastB Z = true`.
  `seam_paid`: `seamFastB Z g = true`, 0 < g < 12.
  `k4PlanFit_paid`: `K4PlanFit` as `k4PlanFit_fast` concludes it, with `firstFastB Z p.g` as its
    only test.

Limits. K04_law IS NOT PROVED BY THIS. `WrittenAt Z`, the return of `publicOf` and the public core
ARE PREMISES. The twelve tests `firstFastB Z g` stay tests here (`first_paid`,
Johnson/Road/K4/K4PlanAllPaid.lean, has them under two conditions more, `XNine Z.p.X` and `NamesTied
Z`): they read the public parameters' labels and sizes, and the built links (these not under
`names_tie`: Johnson/Road/K4/K4PlanLab.lean). BESIDE THE ONE TEST `k4PlanFit_paid` takes what
`k4PlanFit_fast` takes that is no test.
-/
import Johnson.Road.K4.K4PlanTied
import Johnson.Road.K4.K4PlanWrittenShapes
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.PlanWritten (PublicSteps proofSizedFull)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (szOf pubAt stepOf)
open Johnson.Road.K4.LayoutTies (shapesTiedB)
open Johnson.G (layoutFull)
open Meaning (seatBy fLay)

variable {Z : ProofFile.Pub} (W : WrittenAt Z)

include W in
/-- **The tie of shapes accepts at Z's letters**, in the form in which `commonFastB` asks it. -/
theorem shapesTied_at :
    shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout
      (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
      (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
        (seatKeys (allSeatsAt Z)).length)
      (lists0At Z)
      (fun k => ((List.range 25).map fun k => (numbersAt Z).group k).getD k []) = true := by
  rw [show (sentAt Z).codes = proofSizedFull.codes from W.codes,
    show (sentAt Z).shape = proofSizedFull.request from W.shape.trans shape_one,
    show (sentAt Z).layout = layoutFull from W.layout, allSeatsAt_written W,
    lists0At_written W, numbersAt_written W]
  exact shapesTied_written

variable {pol KL : ByteArray} {lay : Option ByteArray}

include W in
/-- **The common test accepts.** -/
theorem common_paid (h : publicOf pol KL lay = .ok Z.p.X) (C : Hd.PublicCore Z.p.X.P) :
    commonFastB Z = true := by
  obtain ⟨p1, p2, p3⟩ := programs_at W
  show ((sentAt Z).codes.lengthsOk && reqShapeOk (sentAt Z).shape &&
    reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout && Meaning.nmFit Z.p.X &&
    shapesTiedB (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout
      (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
      (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
        (seatKeys (allSeatsAt Z)).length)
      (lists0At Z)
      (fun k => ((List.range 25).map fun k => (numbersAt Z).group k).getD k []) &&
    VerifiableInference.Desc.First.groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z)) = true
  rw [p1, p2, p3, Meaning.nmFit_of_core h C, shapesTied_at W, groups_at W]
  rfl

include W in
/-- **The test at the seam in front of group g accepts.** -/
theorem seam_paid (h : publicOf pol KL lay = .ok Z.p.X) (C : Hd.PublicCore Z.p.X.P) {g : ℕ}
    (h0 : 0 < g) (hg : g < 12) : seamFastB Z g = true := by
  have a := (Meaning.pairs_of_planFit (Meaning.planFit_of_core h C)).1 g h0 hg
  have b := seamArr_of_closed h C h0 hg (seamClosed_at W h0 hg)
  show (Meaning.pairFit Z.p.X (2 * g) (Model.Layer.matIx Z.p.X.y).iXI (2 * (g - 1))
      (Model.Layer.matIx Z.p.X.y).iXO &&
    seamArrB Z.p.X (Meaning.sizesOf Z.p.X) (sentAt Z).layout
      (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
      (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
        (seatKeys (allSeatsAt Z)).length) (numbersAt Z) (2 * g) (2 * (g - 1))
      (Model.Layer.matIx Z.p.X.y).iXI) = true
  rw [arr_fast, num_fast, a, b]
  rfl

variable {rows cols : ℕ}

include W in
/-- **`K4PlanFit` with one test**: the group's. -/
theorem k4PlanFit_paid {polS KLS : ByteArray} {tk : Array Nat}
    (h : publicOf pol KL lay = .ok Z.p.X) (C : Hd.PublicCore Z.p.X.P) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (hf : firstFastB Z p.g = true) (hg0 : 0 < p.g) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps polS KLS Z.p.X)
    (B : RefPub Z.p.X p.g) (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFit (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  k4PlanFit_fast Z radM hs hi p (common_paid W h C) hf (seam_paid W h C hg0 hg) hg0 hg x hx hG rad
    posI oW enc wOf hd St B hP P0 hgr hhd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shapesTied_at
#print axioms OnBytes.Road.K4.common_paid
#print axioms OnBytes.Road.K4.seam_paid
#print axioms OnBytes.Road.K4.k4PlanFit_paid
