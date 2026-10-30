-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsFirst.lean: THE TYPED CHAIN's CLAIMED SUM IS THE READING OF THE TARGET OF K4's
SUMCHECK RECORD, at six of the seven sumchecks of THE FIRST layers' sub-proof's own rounds, at the
library's value (`FullFPar.ownF`). Statements and proofs. The twin of Johnson/Road/K4/Claims.lean,
which treats a sub-proof that is not the first, and whose head says how each is stated; its three
tools are used here.

  `claim1F` (the sums of squares) · `claim2F` (the products of the rows) · `claim3F` (the terms) ·
  `claim5F` (the gated products) · `claim6F` (the routed experts' gated products): the statements
    and proofs of `claim1` … `claim6`, at the first sub-proof's chain.
  `claim7F` (the merge): the start form names one slot more than the value has weight claims: the
    last is the slot of the embedding's hidden value, and the one scalar that was sent in the
    weights' round is what the world holds under it (premise he).

Limits. EVERY TIE BETWEEN A PART OF THE TYPED STATEMENT AND WHAT WAS HEARD IS A PREMISE. Sizes are
premises too. The second component of `cl`, the sumcheck's state, is not treated. The batched
sumcheck's claim (the fourth) is not here. Equations alone: nothing on soundness.
-/
import Johnson.Road.K4.Claims
import Johnson.Road.K4.ClaimsTypedFirst

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

/-! ### The six claims -/

variable [Fintype K] [scl : Scl] {M X : Type} (P : FullFPar K M X)

/-- **The sums of squares.** -/
theorem claim1F (y : ((P.ofp.fs.X3 × (Fin (P.D.nNu * 9) → K)) × K) × (Fin (P.D.lL + 1) → K))
    (r : Fin 0 → K) {yl : Lay} {sW : ℕ} {gp rhoI PV : Array E} {t : E}
    (ht : ρ.val t = (normsStart yl sW gp rhoI PV).1.value ρ W)
    (hNI : yl.NI = P.D.nNu) (hNS : ledNS yl.h.xl = 9) (hlPd : yl.lPd = lDd P.D)
    (hhalf : ρ.val (invE (ofNat 2)) * 2 = 1) (hz : rhoI.size = P.D.lL + 1)
    (hp : ∀ j : Fin (P.D.lL + 1), y.2 j = ρ.val (rhoI.getD j.val zeroE))
    (hg : ∀ s : Fin 9, ρ.val (gp.getD s.val zeroE) = y.1.2 ^ s.val)
    (hs : ∀ (i : Fin P.D.nNu) (s : Fin 9),
      y.1.1.2 (finProdFinEquiv (i, s)) = W.slot (sW + 9 * i.val + s.val)) :
    (P.ownF.toOwn.tail.s1.cl y r).1 = ρ.val t := by
  have hh : ρ.val (invE (ofNat 2)) = (2⁻¹ : K) := eq_inv_of_mul_eq_one_left hhalf
  have hn : P.D.nNu ≤ 2 ^ (P.D.lL + 1) := by
    unfold Inst.Model.FFSeg.Dim.nNu Inst.Model.FFSeg.Dim.nl
    rw [pow_succ, Nat.mul_comm]
  rw [cl1F, ht, normsStart_value ρ W, hNI, hNS, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ρ.pow, hh, hlPd, eqTab_nat ρ rhoI hz y.2 hp i.val (lt_of_lt_of_le i.isLt hn), hg s, hs i s]
  ring

/-- **The products of the rows.** -/
theorem claim2F (x : ((P.ownF.toOwn.tail.s1.Nx × K) × (Fin P.ownF.toOwn.tail.nP → K)) × K)
    (r : Fin 1 → K) {sCl : ℕ} {t : E} (ht : ρ.val t = (Aff.slot sCl).value ρ W)
    (hr : r 0 = W.slot sCl) : (P.ownF.toOwn.tail.s2.cl x r).1 = ρ.val t := by
  rw [cl2F, ht, Aff.value_slot, hr]

/-- **The terms.** -/
theorem claim3F (b : P.ownF.toOwn.tail.s2.Nx) (r : Fin 1 → K) {sCl : ℕ} {t : E}
    (ht : ρ.val t = (Aff.slot sCl).value ρ W) (hr : r 0 = W.slot sCl) :
    (P.ownF.toOwn.tail.s3.cl b r).1 = ρ.val t := by
  rw [cl3F, ht, Aff.value_slot, hr]

/-- **The gated products.** -/
theorem claim5F (z : P.ownF.toOwn.tail.s4.Nx) (r : Fin 0 → K) {sH1 : ℕ} {t : E}
    (ht : ρ.val t = (Aff.slot sH1).value ρ W) (hv : (P.st5 z.2).v = W.slot sH1) :
    (P.ownF.toOwn.tail.s5.cl z r).1 = ρ.val t := by
  rw [cl5F, ht, Aff.value_slot, hv]

/-- **The routed experts' gated products.** -/
theorem claim6F (y : (P.ownF.toOwn.tail.s5.Nx × K) × (Fin (P.D.lL - 1) → K)) (r : Fin 0 → K)
    {LamM sH1 : ℕ} {rhoM : Array E} {t : E}
    (ht : ρ.val t = ((List.range LamM).foldl
      (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE))
      aff0).value ρ W)
    (hL : LamM = P.D.ne) (hz : rhoM.size = P.D.lL - 1)
    (hp : ∀ j : Fin (P.D.lL - 1), y.2 j = ρ.val (rhoM.getD j.val zeroE))
    (hv : ∀ i : Fin P.D.ne, (P.st6 y.1.1.1.1.2).v i = W.slot (sH1 + 1 + i.val)) :
    (P.ownF.toOwn.tail.s6.cl y r).1 = ρ.val t := by
  have hn : P.D.ne ≤ 2 ^ (P.D.lL - 1) := P.fp.rt.hn
  rw [cl6F, ht, foldAdds_value ρ W _
    (fun lm => ρ.val ((eqTab rhoM).getD lm zeroE) * W.slot (sH1 + 1 + lm))
    (fun a lm => by rw [Aff.value_addMul, Aff.value_slot]), aff0_value, zero_add,
    list_range_sumM, hL, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eqTab_nat ρ rhoM hz y.2 hp i.val (lt_of_lt_of_le i.isLt hn), hv i]

/-- **The merge, with the embedding's claim.** -/
theorem claim7F (y : ((P.ownF.toOwn.tail.s6.Nx × K) × (Fin 1 → K)) × K) (r : Fin 0 → K)
    {sv : Array Nat} {rho : Array E} {t : E} (ht : ρ.val t = (wsForkStart sv rho).value ρ W)
    (hn : sv.size = P.nW + 1)
    (hr : ∀ a, a < P.nW + 1 → ρ.val (rho.getD a zeroE) = y.2 ^ a)
    (hv : ∀ a : Fin P.nW,
      (P.ip.st7 P.num y.1.1.1.1.1.1.1.1.1.2).v a = W.slot (sv.getD a.val 0))
    (he : y.1.2 0 = W.slot (sv.getD P.nW 0)) :
    (P.ownF.toOwn.tail.s7.cl y r).1 = ρ.val t := by
  rw [cl7F, ht, forkStart_value, hn, Finset.sum_range_succ, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hr a.val (Nat.lt_succ_of_lt a.isLt), hv a]
  · rw [hr P.nW (Nat.lt_succ_self _), he]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.claim1F
#print axioms OnBytes.Road.K4.claim2F
#print axioms OnBytes.Road.K4.claim3F
#print axioms OnBytes.Road.K4.claim5F
#print axioms OnBytes.Road.K4.claim6F
#print axioms OnBytes.Road.K4.claim7F
