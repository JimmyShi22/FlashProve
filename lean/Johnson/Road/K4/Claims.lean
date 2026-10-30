-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Claims.lean: THE TYPED CHAIN's CLAIMED SUM IS THE READING OF THE TARGET OF K4's
SUMCHECK RECORD, at six of the seven sumchecks of a layers' sub-proof's own rounds, at the
library's value (`FullPar.own`; a sub-proof that is not the first). Statements and proofs. They are
meant as the first components of `TailH.Claims` (OnBytes/Tie/Pv/Lay/OwnTieL.lean): c1,
c2, c3, c5, c6 and c7. The fourth stands in Johnson/Road/K4/Claim4.lean.

How each is stated. A sumcheck's target in K4's text is the public part of its start form C. Here
t is an element whose reading is the value of C in a world W (premise ht;
`public_value`, OnBytes/Tie/Pv/Att/HearSaid.lean, gives it from `F.publicPart C = some t` at the
world of what was shown, `shownW ρ F`). C is written as K4's text writes it
(OnBytes/Desc/First/K4/Hear.lean; for the merge OnBytes/K/Kc/QuietLink.lean). The statement that
the stage finds is a letter; of its parts it is asked, as premises, that they are the readings of
what was heard: the sent scalars and the earlier sumcheck's end values are what W holds under the
slots that C names, the join's point is the reading of the drawn point, the powers are those of the
reading of the drawn element.

  `forkStart_fold`, `forkStart_value`: the value of the merge's start form (typed after
    `merge_target_fold`, `merge_target_start` of OnBytes/Tie/Pv/Lay/MergeTarget.lean, whose file
    stands above `verify-on-bytes`'s routines; no routine is named here).
  `eqTab_nat`: an entry of the program's table of equality weights reads as the library's kernel at
    a typed point that is the reading of the program's.
  `claim1` (the sums of squares) · `claim2` (the products of the rows) · `claim3` (the terms) ·
  `claim5` (the gated products) · `claim6` (the routed experts' gated products) · `claim7` (the
  merge).

Limits. EVERY TIE BETWEEN A PART OF THE TYPED STATEMENT AND WHAT WAS HEARD IS A PREMISE: nothing
here shows that a hearing's lists meet them. Sizes are premises too (paid in PlanSizes.lean):
the norms' number, nine sums, the bits of the width, the layers with experts; and the sizes of the
two joins' points (hz). The second component
of `cl`, the sumcheck's state, is not treated. The batched sumcheck's claim (c4) is not here.
Equations alone: nothing on soundness.
-/
import Johnson.Road.K4.ClaimsTyped
import Johnson.Road.FormsKeysIdnW
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay aff0 normsStart)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ### Two tools -/

/-- The loop of the merge's start form, on lists. -/
theorem forkStart_fold : ∀ (l : List Nat) (r : List E) (s : Aff),
    ((l.zip r).foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) s).value ρ W =
      s.value ρ W + ∑ i ∈ Finset.range l.length, ρ.val (r.getD i zeroE) * W.slot (l.getD i 0)
  | [], r, s => by simp
  | a :: l, [], s => by
    rw [List.zip_nil_right, List.foldl_nil]
    simp [ρ.zero]
  | a :: l, b :: r, s => by
    rw [List.zip_cons_cons, List.foldl_cons, forkStart_fold l r, Aff.value_addMul,
      Aff.value_slot, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The value of the merge's start form: a coefficient that is lacking counts as 0. -/
theorem forkStart_value (sv : Array Nat) (rho : Array E) :
    (wsForkStart sv rho).value ρ W =
      ∑ i ∈ Finset.range sv.size, ρ.val (rho.getD i zeroE) * W.slot (sv.getD i 0) := by
  unfold wsForkStart
  rw [← Array.foldl_toList, Array.toList_zip, forkStart_fold, Aff.value_empty, zero_add,
    Array.length_toList]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-- An entry of the program's table of equality weights, at a typed point that is the reading of
the program's. -/
theorem eqTab_nat {g : ℕ} (z : Array E) (hz : z.size = g) (p : Fin g → K)
    (hp : ∀ j : Fin g, p j = ρ.val (z.getD j.val zeroE)) (c : ℕ) (hc : c < 2 ^ g) :
    ρ.val ((eqTab z).getD c zeroE) = Blocks.eqN g 0 (Blocks.nat p) c := by
  subst hz
  rw [eqTab_value ρ z c hc]
  refine eqN_congr' _ 0 (fun j hj => ?_) c
  rw [Nat.zero_add]
  unfold pt Blocks.nat
  rw [dif_pos hj, hp ⟨j, hj⟩]

/-! ### The six claims -/

variable [Fintype K] [scl : Scl] {M X : Type} (P : FullPar K M X)

/-- **The sums of squares.** -/
theorem claim1 (y : ((P.XT × (Fin (P.D.nNu * 9) → K)) × K) × (Fin (P.D.lL + 1) → K))
    (r : Fin 0 → K) {yl : Lay} {sW : ℕ} {gp rhoI PV : Array E} {t : E}
    (ht : ρ.val t = (normsStart yl sW gp rhoI PV).1.value ρ W)
    (hNI : yl.NI = P.D.nNu) (hNS : ledNS yl.h.xl = 9) (hlPd : yl.lPd = lDd P.D)
    (hhalf : ρ.val (invE (ofNat 2)) * 2 = 1) (hz : rhoI.size = P.D.lL + 1)
    (hp : ∀ j : Fin (P.D.lL + 1), y.2 j = ρ.val (rhoI.getD j.val zeroE))
    (hg : ∀ s : Fin 9, ρ.val (gp.getD s.val zeroE) = y.1.2 ^ s.val)
    (hs : ∀ (i : Fin P.D.nNu) (s : Fin 9),
      y.1.1.2 (finProdFinEquiv (i, s)) = W.slot (sW + 9 * i.val + s.val)) :
    (P.own.toOwn.tail.s1.cl y r).1 = ρ.val t := by
  have hh : ρ.val (invE (ofNat 2)) = (2⁻¹ : K) := eq_inv_of_mul_eq_one_left hhalf
  have hn : P.D.nNu ≤ 2 ^ (P.D.lL + 1) := by
    unfold Inst.Model.FFSeg.Dim.nNu Inst.Model.FFSeg.Dim.nl
    rw [pow_succ, Nat.mul_comm]
  rw [cl1, ht, normsStart_value ρ W, hNI, hNS, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ρ.pow, hh, hlPd, eqTab_nat ρ rhoI hz y.2 hp i.val (lt_of_lt_of_le i.isLt hn), hg s, hs i s]
  ring

/-- **The products of the rows.** -/
theorem claim2 (x : ((P.own.toOwn.tail.s1.Nx × K) × (Fin P.own.toOwn.tail.nP → K)) × K)
    (r : Fin 1 → K) {sCl : ℕ} {t : E} (ht : ρ.val t = (Aff.slot sCl).value ρ W)
    (hr : r 0 = W.slot sCl) : (P.own.toOwn.tail.s2.cl x r).1 = ρ.val t := by
  rw [cl2, ht, Aff.value_slot, hr]

/-- **The terms.** -/
theorem claim3 (b : P.own.toOwn.tail.s2.Nx) (r : Fin 1 → K) {sCl : ℕ} {t : E}
    (ht : ρ.val t = (Aff.slot sCl).value ρ W) (hr : r 0 = W.slot sCl) :
    (P.own.toOwn.tail.s3.cl b r).1 = ρ.val t := by
  rw [cl3, ht, Aff.value_slot, hr]

/-- **The gated products.** -/
theorem claim5 (z : P.own.toOwn.tail.s4.Nx) (r : Fin 0 → K) {sH1 : ℕ} {t : E}
    (ht : ρ.val t = (Aff.slot sH1).value ρ W) (hv : (P.st5 z.2).v = W.slot sH1) :
    (P.own.toOwn.tail.s5.cl z r).1 = ρ.val t := by
  rw [cl5, ht, Aff.value_slot, hv]

/-- **The routed experts' gated products.** -/
theorem claim6 (y : (P.own.toOwn.tail.s5.Nx × K) × (Fin (P.D.lL - 1) → K)) (r : Fin 0 → K)
    {LamM sH1 : ℕ} {rhoM : Array E} {t : E}
    (ht : ρ.val t = ((List.range LamM).foldl
      (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE))
      aff0).value ρ W)
    (hL : LamM = P.D.ne) (hz : rhoM.size = P.D.lL - 1)
    (hp : ∀ j : Fin (P.D.lL - 1), y.2 j = ρ.val (rhoM.getD j.val zeroE))
    (hv : ∀ i : Fin P.D.ne, (P.st6 y.1.1.1.1.2).v i = W.slot (sH1 + 1 + i.val)) :
    (P.own.toOwn.tail.s6.cl y r).1 = ρ.val t := by
  have hn : P.D.ne ≤ 2 ^ (P.D.lL - 1) := P.fp.rt.hn
  rw [cl6, ht, foldAdds_value ρ W _
    (fun lm => ρ.val ((eqTab rhoM).getD lm zeroE) * W.slot (sH1 + 1 + lm))
    (fun a lm => by rw [Aff.value_addMul, Aff.value_slot]), aff0_value, zero_add,
    list_range_sumM, hL, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eqTab_nat ρ rhoM hz y.2 hp i.val (lt_of_lt_of_le i.isLt hn), hv i]

/-- **The merge.** -/
theorem claim7 (y : ((P.own.toOwn.tail.s6.Nx × K) × (Fin 0 → K)) × K) (r : Fin 0 → K)
    {sv : Array Nat} {rho : Array E} {t : E} (ht : ρ.val t = (wsForkStart sv rho).value ρ W)
    (hn : sv.size = P.nW) (hr : ∀ a : Fin P.nW, ρ.val (rho.getD a.val zeroE) = y.2 ^ a.val)
    (hv : ∀ a : Fin P.nW,
      (P.ip.st7 P.num y.1.1.1.1.1.1.1.1.1.2).v a = W.slot (sv.getD a.val 0)) :
    (P.own.toOwn.tail.s7.cl y r).1 = ρ.val t := by
  rw [cl7, ht, forkStart_value, hn, Finset.sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hr a, hv a]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.claim1
#print axioms OnBytes.Road.K4.claim2
#print axioms OnBytes.Road.K4.claim3
#print axioms OnBytes.Road.K4.claim5
#print axioms OnBytes.Road.K4.claim6
#print axioms OnBytes.Road.K4.claim7
