-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/NormsConsts.lean: the norms' stage of the layers' own rounds: the forms' half:
what the caller's own forms and end terms are worth by algebra.

The per-position bridge of a norm (OnBytes/Desc/First/NormBridge/BridgeWorld.lean) asks a group of
premises `Run.Consts`: seven equations without chance. Here they are paid for K4's own text, where
the run's letters are K4's (`ConstsTie`).

  `foldAdd_val`, `summand_val`, `rowsSummand_val`: K4's summand of the row products' sumcheck on
      what was shown, read in a ring: the sum over the 7 NI products.
  `consts_of_heard`: the law.

Limits. Algebra on forms and elements: no draw, no soundness. That the program's inverse of 2 reads
as a half (hhalf), that the two batchings returned powers (hgp, hom; see K4/BatchLaws.lean) and that
the verifier's two public numbers of each norm are the data's (N, hnp) are premises. The ties on the
two sumchecks' records are facts on the hearing, and are premises here.
-/
import Johnson.Road.K4.NormsFormsZero
import Johnson.Road.Rows.GatedStartsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4
open Finset
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim npOf)
open D6.Bridge (prTerms pairA pairB sumTerms_pr)

variable {K : Type} [Field K] (ρ : Reading K)

/-- A fold that adds f i for each member i, read. -/
theorem foldAdd_val (f : Nat → E) : ∀ (l : List Nat) (z : E),
    ρ.val (l.foldl (fun s i => addE s (f i)) z) = ρ.val z + (l.map fun i => ρ.val (f i)).sum
  | [], z => by simp
  | i :: l, z => by
    rw [List.foldl_cons, foldAdd_val f l, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- The summand of one norm, read: the seven products under their weights. -/
theorem summand_val (om s : Nat → E) :
    ρ.val (P6.summand om s) =
      ∑ r ∈ range 7, ρ.val (om r) * (ρ.val (s (pairA r)) * ρ.val (s (pairB r))) := by
  simp [P6.summand, P6.rowProducts, List.zipIdx, ρ.add, ρ.mul, ρ.zero, Finset.sum_range_succ,
    pairA, pairB]
  ring

/-- K4's summand of the row products' sumcheck on what was shown, read. -/
theorem rowsSummand_val (y : Lay) (H : Heard) (sh : Array E) (om : K)
    (hom : ∀ m, m < 7 * y.NI → ρ.val (H.omV.getD m zeroE) = om ^ m) :
    ρ.val (rowsSummand y H sh) =
      P1.sumTerms (prTerms y.NI om) fun e => ρ.val (sh.getD e zeroE) := by
  unfold rowsSummand
  rw [foldAdd_val, ρ.zero, zero_add, Road.list_range_sum, sumTerms_pr, Nat.mul_comm 7 y.NI,
    Alg.sum_range_mul_add]
  refine sum_congr rfl fun i hi => ?_
  rw [summand_val]
  refine sum_congr rfl fun r hr => ?_
  have hr' := mem_range.mp hr
  have hi' := mem_range.mp hi
  have d1 : (i * 7 + r) / 7 = i := by omega
  have d2 : (i * 7 + r) % 7 = r := by omega
  rw [d1, d2, hom (7 * i + r) (by omega), Nat.mul_comm 7 i]

/-- The letters of a run are K4's, as far as the seven equations read them. rhoI: the drawn point
over the norms' numbers. -/
structure ConstsTie (R : D6.Bridge.Run) (P : Pub) (o : Own) (sh rhoI : Array E) : Prop where
  half : R.half = invE (ofNat 2)
  sW : R.sW = o.H.sW
  startS : R.S.p.start = (normsStart P.y o.H.sW o.H.gp rhoI o.H.PV).1
  startP : R.Pr.p.start = Aff.slot R.sCl
  endS : R.S.S0 = mulE (R.shS 0) (R.shS 1)
  endP : R.Pr.S0 = rowsSummand P.y o.H sh
  shP : R.shP = fun e => sh.getD e zeroE
  eps : R.eps = epsOf o.v.y
  two : R.two = twoM o.v

theorem consts_of_heard (W : World K) (c : D6.Bridge.Data K) (hρ : Road.Numerals ρ) [scl : Scl]
    {D : Dim} {R : D6.Bridge.Run} {P : Pub} {o : Own} {sh rhoI : Array E}
    (T : ConstsTie R P o sh rhoI) (hy : P.y = o.v.y) (hNI : c.NI = o.v.y.NI)
    (hNS : ledNS P.y.h.xl = 9) (hhalf : ρ.val (invE (ofNat 2)) * 2 = 1)
    (hsz : rhoI.size = c.lNI) (hN : c.NI ≤ 2 ^ c.lNI)
    (haS : ∀ t, t < c.lNI → R.aS ρ t = Road.pt ρ rhoI t)
    (hgp : ∀ s, s < 9 → ρ.val (o.H.gp.getD s zeroE) = ρ.val R.gam ^ s)
    (hom : ∀ m, m < 7 * c.NI → ρ.val (o.H.omV.getD m zeroE) = ρ.val R.om ^ m)
    (N : Road.NormWords o.v D) (hD : c.NI ≤ D.nNu) (hnp : ∀ i, i < c.NI → c.np i = npOf D i) :
    R.Consts ρ c P.y.lPd W := by
  refine { half := ?_, eps := ?_, two := ?_, startS := ?_, startP := ?_, endS := ?_, endP := ?_ }
  · rw [T.half]
    linear_combination (-1 : K) * hhalf
  · intro i hi
    rw [T.eps, hnp i hi]
    unfold epsOf
    rw [hρ.ofNat, ← N.eps i (by omega)]
    norm_cast
  · intro i hi
    rw [T.two, hnp i hi]
    unfold twoM
    rw [Aff.value_ofConst, hρ.pw, N.M i (by omega)]
  · rw [T.startS, Road.normsStart_value]
    unfold D6.Bridge.Run.cvS
    rw [hNS, hy, ← hNI, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun s hs => ?_
    rw [ρ.pow, T.half, hgp s (mem_range.mp hs),
      Road.eqTab_value ρ rhoI i (by rw [hsz]; omega), hsz,
      Road.Rows.eqN_same c.lNI 0 (a := Road.pt ρ rhoI) (a' := R.aS ρ)
        (fun t ht => by rw [Nat.zero_add]; exact (haS t ht).symm) i]
    unfold D6.Bridge.Run.Wt
    rw [T.sW, Nat.add_assoc]
    ring
  · rw [T.startP, Aff.value_slot]
  · rw [T.endS, ρ.mul]
  · rw [T.endP, T.shP, hNI, ← hy]
    exact rowsSummand_val ρ P.y o.H sh (ρ.val R.om) (by rw [hy, ← hNI]; exact hom)

#print axioms rowsSummand_val
#print axioms consts_of_heard

end OnBytes.Desc.First.K4
