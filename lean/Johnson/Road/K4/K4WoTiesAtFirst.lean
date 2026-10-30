-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4WoTiesAtFirst.lean: THE FIRST GROUP's TWINS OF K4WoTiesAt.lean: TWO OF THE TIES OF
THE LINE wo (`k4_wo_core`, K4LinesWo.lean) AT TERMS, AT THE FIRST GROUP's REFERENCE VALUE.
Statements with proofs: unfoldings and calls; no new argument.

THE FIRST GROUP's VALUE `(A.seatN …).atRecF X p` extends the later groups' structure; the line's
core is general in that structure: it is called at the parent `toPlan4K`. The value's reader:
`PinPlan.Wn_partF` (K4PinsMatFirst.lean).

  `PinPlan.wo_zeroF`: the value's cells are 0 from row hRef on.
  `PinPlan.wo_matF`: `matOfCells hRef kRef w.cells i (lowBits kRef C)` is the value's cell at (i,
    C), for C < 2 ^ kRef.
  `PinPlan.woTiesF`: `WoTies lay hRef kRef …` at that value and the pinned part, from three
    equations on public numbers.

Limits. Those of K4WoTiesAt.lean: the three equations (lay = p.P.wsLay · hRef = lay.m0 · kRef =
lay.lk) and hrc stay premises; that the pile's reader's matrix is `matOfCells hRef kRef w.cells` is
not said here; the tie of the mask entry is not touched. Nothing on soundness.
-/
import Johnson.Road.K4.K4WoTiesAt
import Johnson.Road.K4.K4PinsMatFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2 WsLay)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open VerifiableInference.Desc.K13.Law (lowBits cellAtNo matOfCells matOfCells_low)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

/-- The two names of the value's committed matrix off a tuple, at any letters of the first group.
-/
theorem wn_two [scl : Scl] {M T : Type} (QK : Plan4KF M T) (t : M) (r c : ℕ) :
    QK.toPlan4K.toL.plan.full.Wn (QK.toPlan4K.toL.plan.full.msg t) r c =
      QK.toLF.planF.Wn (QK.toLF.planF.toPlan4.msg t) r c := rfl

/-- A test on two bounds that hold. -/
theorem ite_at {K : Type} {a b i j : ℕ} (x z : K) (h1 : i < a) (h2 : j < b) :
    (if i < a ∧ j < b then x else z) = x := if_pos ⟨h1, h2⟩

/-- A test on two bounds of which the first fails. -/
theorem ite_off {K : Type} {a b i j : ℕ} (x z : K) (h : a ≤ i) :
    (if i < a ∧ j < b then x else z) = z := if_neg fun c => absurd c.1 (Nat.not_lt.2 h)

/-- The two readings of cells that are a matrix are one. -/
theorem cell_rc (rows cols : ℕ) (c : Fin rows → Fin cols → Cb.Gl.E) (r j : ℕ) :
    cellAtNo c r j = rcQ rows cols c r j := rfl

section
variable [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers) (tl : HTailF2)
  (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)

/-- **The first group's value's cells are 0 from row hRef on.** -/
theorem PinPlan.wo_zeroF (w : Wit Cells Tok MsgT) (j : ℕ) (hj : hRef ≤ j) (C : ℕ) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.full.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.full.msg
          (partOf A.D.codes arr ms N m w)) j C = 0 :=
  (wn_two ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p)
      (partOf A.D.codes arr ms N m w) j C).trans
    ((PinPlan.Wn_partF A n N tl y nM nR nC n0 ns nx v7 X p arr ms m w j C).trans
      (ite_off (A.rc w.cells j C) 0 hj))

end

section
variable [scl : Scl] {Tok : Type} {rows cols : ℕ} (A : PinPlan (Fin rows → Fin cols → Cb.Gl.E))
  (hrc : A.rc = rcQ rows cols) (n : ℕ) (N : Numbers) (tl : HTailF2) (y : Lay)
  (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (m : ℕ)

include hrc in
/-- **The pile's matrix of the witness's cells is the first group's value's cells.** -/
theorem PinPlan.wo_matF (w : Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) (i : Fin hRef) (C : ℕ)
    (hC : C < 2 ^ kRef) :
    matOfCells hRef kRef w.cells i (lowBits kRef C) =
      ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.full.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.full.msg
          (partOf A.D.codes arr ms N m w)) i C :=
  (matOfCells_low hRef kRef w.cells i C hC).trans
    ((cell_rc rows cols w.cells i C).trans
      ((congrFun (congrFun (congrFun hrc w.cells) i) C).symm.trans
        ((ite_at (A.rc w.cells i C) 0 i.isLt hC).symm.trans
          ((PinPlan.Wn_partF A n N tl y nM nR nC n0 ns nx v7 X p arr ms m w i C).symm.trans
            (wn_two ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p)
              (partOf A.D.codes arr ms N m w) i C).symm))))

/-- **`WoTies` at the first group's value and the pinned part**, from three equations on public
numbers. -/
theorem PinPlan.woTiesF {lay : WsLay} (hlay : lay = p.P.wsLay) (hm0 : hRef = lay.m0)
    (hlk : kRef = lay.lk) :
    WoTies (W := Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) lay hRef kRef
      ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K
      (partOf A.D.codes arr ms N m) p :=
  ⟨hlay, hm0, hlk, fun w j hj C => PinPlan.wo_zeroF A n N tl y nM nR nC n0 ns nx v7 X p arr ms m
    w j hj C⟩

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.wn_two
#print axioms OnBytes.Road.K4.ite_at
#print axioms OnBytes.Road.K4.ite_off
#print axioms OnBytes.Road.K4.cell_rc
#print axioms OnBytes.Road.K4.PinPlan.wo_zeroF
#print axioms OnBytes.Road.K4.PinPlan.wo_matF
#print axioms OnBytes.Road.K4.PinPlan.woTiesF
