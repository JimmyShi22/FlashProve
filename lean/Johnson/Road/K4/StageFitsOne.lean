-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageFitsOne.lean: Johnson/Road/K4/StageFits.lean GOES ON: the first stage (the
product layer of the sums of squares). Glue over `stgFits_level` (StageFitsMore.lean) and
`ordE_val` (OnBytes/Tie/Pv/Lay/OrderE.lean). No draw, no count.

  `append_reads`: two typed points in a row read two arrays in a row.
  `stgFits_ordE`: for every stage with the pick of the constant coefficient and two scalars a round,
    whose weight at variable j is a point p at the place `ordE k order h j`, p reading rho place by
    place: `StgFits` at `levelWs k rho order`. So the order of the rounds drops out.
  `fits1`: at every `FullPar` whose order eS is the programs' default: at a state with the join's
    point jp and the token point tp: if jp reads rhoI, tp reads PV and 1/2 reads as the programs'
    half: `StgFits` at `levelWs k (rhoI ++ replicate lDd half ++ PV) (orderDefault k)`,
    k := lL + 1 + (lDd + lT).

Limits. The ties of jp, tp to what was heard are premises; that the value's order is the default is
a premise (it is so at Johnson/Road/K4/ValueSlots.lean's value). `OutIs` at a hearing is not
concluded here. The fifth, sixth and seventh stages are not treated.
-/
import Johnson.Road.K4.StageFitsMore
import OnBytes.Tie.Pv.Lay.OrderE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes
open OnBytes.Model (orderDefault)
open OnBytes.Tie.Pv.Lay (StgFits ordE ordE_val eDefault default_perm)
open OnBytes.Desc.First.P1 (gl levelWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

/-- Two typed points in a row read two arrays in a row. -/
theorem append_reads {a b : ℕ} (p : Fin a → Cb.Gl.E) (q : Fin b → Cb.Gl.E) (A B : Array E)
    (hA : A.size = a) (hp : ∀ i : Fin a, p i = gl.val (A.getD i.val zeroE))
    (hq : ∀ i : Fin b, q i = gl.val (B.getD i.val zeroE)) (i : Fin (a + b)) :
    Fin.append p q i = gl.val ((A ++ B).getD i.val zeroE) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left, hp, Fin.val_castAdd, Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by rw [hA]; exact i.isLt)]
  · rw [Fin.append_right, hq, Fin.val_natAdd, Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?,
      Array.getElem?_append_right (by rw [hA]; exact Nat.le_add_right _ _), hA,
      Nat.add_sub_cancel_left]

section Any
variable {M X : Type}

/-- The order of the rounds drops out. -/
theorem stgFits_ordE (S : Stg Cb.Gl.E M X) (st : S.L.St) (order : List ℕ)
    (h : order.Perm (List.range S.L.S.k)) (rho : Array E) (p : Fin S.L.S.k → Cb.Gl.E)
    (hF : S.F = TWhole.F₀ S.L.T.par) (hn : ∀ i, S.L.M.n i = 2)
    (hw : ∀ j, S.L.S.w st j = some (p (ordE S.L.S.k order h j)))
    (hp : ∀ i, p i = gl.val (rho.getD i.val zeroE)) :
    StgFits gl S st (levelWs S.L.S.k rho order) S.L.S.k S.L.M.DY := by
  have hl : order.length = S.L.S.k := by rw [h.length_eq, List.length_range]
  refine stgFits_level S st S.L.S.k rho order hF hn hl fun i => ?_
  rw [hw i, hp, ordE_val, List.getD_eq_getElem _ _ (by rw [hl]; exact i.isLt)]

end Any

variable [scl : Scl] {M Xs : Type}

/-- **The product layer of the sums of squares.** -/
theorem fits1 (P : FullPar Cb.Gl.E M Xs) (hS : P.eS = eDefault _)
    (st : P.own.toOwn.tail.s1.L.St) (jp : Fin (P.D.lL + 1) → Cb.Gl.E)
    (tp : Fin P.D.lT → Cb.Gl.E)
    (hst : ∀ i, P.own.toOwn.tail.s1.L.S.w st i =
      some (Fin.append jp (Fin.append (fun _ : Fin (lDd P.D) => (2⁻¹ : Cb.Gl.E)) tp) (P.eS i)))
    (rhoI PV : Array E) (half : E) (hI : rhoI.size = P.D.lL + 1)
    (hj : ∀ i, jp i = gl.val (rhoI.getD i.val zeroE))
    (ht : ∀ i, tp i = gl.val (PV.getD i.val zeroE)) (hh : gl.val half = 2⁻¹) :
    StgFits gl P.own.toOwn.tail.s1 st
      (levelWs (P.D.lL + 1 + (lDd P.D + P.D.lT))
        (rhoI ++ Array.replicate (lDd P.D) half ++ PV)
        (orderDefault (P.D.lL + 1 + (lDd P.D + P.D.lT))))
      (P.D.lL + 1 + (lDd P.D + P.D.lT)) 2 :=
  stgFits_ordE P.own.toOwn.tail.s1 st (orderDefault _) (default_perm _) _
    (Fin.append jp (Fin.append (fun _ : Fin (lDd P.D) => (2⁻¹ : Cb.Gl.E)) tp)) rfl (fun _ => rfl)
    (fun j => by rw [hst j, hS]; rfl)
    (fun i => by
      rw [Array.append_assoc]
      exact append_reads jp _ rhoI _ hI hj
        (append_reads _ tp (Array.replicate (lDd P.D) half) PV Array.size_replicate
          (fun i => by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos i.isLt]
            exact hh.symm) ht) i)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.append_reads
#print axioms OnBytes.Road.K4.stgFits_ordE
#print axioms OnBytes.Road.K4.fits1
