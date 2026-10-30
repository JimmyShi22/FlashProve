-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailJoinVal.lean.
The smallness test's claim on the key vectors of its lookup, written out by hand: its value.

OnBytes/Tie/Pv/Lookup/Ends/FoTailJoin.lean cuts a run of linJoin9 into one call of t2Lin on a form
and a list of runs. This file says what the form and the runs are worth together.

* natScale_val: x times a natural number, read in a ring.
* kfRun ρ W tl g q: what the runs of call q read, without the call's weight: the sum over the call's
  pieces of the piece's weight times the sum over its columns of weight times entry of the piece's
  virtual row.
* join9_value: the form and the runs are worth the sum over the two calls of e_q (alpha - q theta -
  kfRun q), plus the trees of padding alone, less the hidden value at the end of the key side.
  Under: the smallness test's shape is the record's (tl.f9 = g.shape).
* join9_claim: so they are worth claimJoin of OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean at the
  letter kf := kfRun, with its sign. Under: tl.f9 = g.shape; the shape is lawful (FoNums.ok) and has
  two calls; the record holds the flat function's end values endsOf (HeardIs) with a state F0; the
  values are read in the world (Fork.worldOf) of a state later than F0.
That kfRun q is the value of the digits' key form of call q is not shown here.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailJoin
import OnBytes.Tie.Pv.Lookup.Ends.FoTailBits

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun Cb.Fo.PlaneClaims Cb.Fo Finset

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- x times a natural number, read. -/
theorem natScale_val (x : E) (n : ℕ) : ρ.val (scaleNat x n) = (n : K) * ρ.val x := by
  have e : ρ.val (ofF (fOfNat n)) = (n : K) := natE_val ρ n
  unfold scaleNat
  rw [scale_val, ← ofF_val, e]

/-- What the runs of call q read, without the call's weight. -/
def kfRun (tl : HTailF2) (g : Heard) (q : ℕ) : K :=
  ((tl.zOf q).pieces.toList.map fun p =>
    ρ.val (eqOne ((g.zk.getD q #[]).extract 0 ((tl.zOf q).call.n - p.b)) (p.off / 2 ^ p.b)) *
      runSum (fun i => ρ.val ((eqTab (joinZc tl g q p)).getD i zeroE) *
        W.entry p.tree p.row (p.c0 + i)) p.Cp 0).sum

theorem joinRun_value (tl : HTailF2) (g : Heard) (q : ℕ) (p : Piece) :
    Run2.value ρ W (joinRun tl g q p) = -(ρ.val (g.e.getD q zeroE) *
      (ρ.val (eqOne ((g.zk.getD q #[]).extract 0 ((tl.zOf q).call.n - p.b)) (p.off / 2 ^ p.b)) *
        runSum (fun i => ρ.val ((eqTab (joinZc tl g q p)).getD i zeroE) *
          W.entry p.tree p.row (p.c0 + i)) p.Cp 0)) := by
  unfold Run2.value joinRun joinRunW
  simp only
  rw [ρ.sub, ρ.zero, ρ.mul,
    runSum_congr _ (fun i => ρ.val ((eqTab (joinZc tl g q p)).getD i zeroE) *
      W.entry p.tree p.row (p.c0 + i)) _ _ fun j => by rw [Nat.zero_add]]
  ring

theorem callRuns_value (tl : HTailF2) (g : Heard) (q : ℕ) :
    (((tl.zOf q).pieces.toList.map (joinRun tl g q)).map (Run2.value ρ W)).sum =
      -(ρ.val (g.e.getD q zeroE) * kfRun ρ W tl g q) := by
  unfold kfRun
  rw [List.map_map]
  induction (tl.zOf q).pieces.toList with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    show Run2.value ρ W (joinRun tl g q p) + _ = _
    rw [joinRun_value]
    ring

/-- The form and the runs together. -/
theorem join9_value (tl : HTailF2) (g : Heard) (hs : tl.f9 = g.shape) :
    (Aff.ofConst (joinConst tl g) - g.cEnd).value ρ W +
        ((joinRuns tl g).map (Run2.value ρ W)).sum =
      ∑ q ∈ range 2, ρ.val (g.e.getD q zeroE) *
          (ρ.val g.alpha - (q : K) * ρ.val g.theta - kfRun ρ W tl g q) +
        ∑ i ∈ range (2 ^ g.shape.rK - g.shape.NT),
          (eqTabK (rdL ρ g.zy)).getD (g.shape.NT + i) 0 *
            (ρ.val g.alpha - padKeyK g.shape (ρ.val g.theta) 0) -
        g.cEnd.value ρ W := by
  have hc : ρ.val (joinConst tl g) =
      ρ.val (g.e.getD 0 zeroE) * (ρ.val g.alpha - ((0 : ℕ) : K) * ρ.val g.theta) +
        ρ.val (g.e.getD 1 zeroE) * (ρ.val g.alpha - ((1 : ℕ) : K) * ρ.val g.theta) +
        ∑ i ∈ range (2 ^ g.shape.rK - g.shape.NT),
          (eqTabK (rdL ρ g.zy)).getD (g.shape.NT + i) 0 *
            (ρ.val g.alpha - padKeyK g.shape (ρ.val g.theta) 0) := by
    unfold joinConst
    rw [hs, foldl_add_val ρ _ (fun i => (eqTabK (rdL ρ g.zy)).getD (g.shape.NT + i) 0 *
      (ρ.val g.alpha - padKeyK g.shape (ρ.val g.theta) 0)) _ _ (fun i _ => by
        rw [ρ.mul, ρ.sub, rdL_getD, eqTab_val]
        show _ * (_ - ρ.val (Forest.padKeyOf g.shape g.theta 0)) = _
        rw [padKey_val ρ g.shape g.theta 0 (by norm_num)]), foldl_add, lsum]
    congr 1
    show ρ.val (addE (addE zeroE (mulE (g.e.getD 0 zeroE) (subE g.alpha (scaleNat g.theta 0))))
      (mulE (g.e.getD 1 zeroE) (subE g.alpha (scaleNat g.theta 1)))) = _
    rw [ρ.add, ρ.add, ρ.zero, ρ.mul, ρ.mul, ρ.sub, ρ.sub, natScale_val, natScale_val, zero_add]
  have hr : ((joinRuns tl g).map (Run2.value ρ W)).sum =
      -(ρ.val (g.e.getD 0 zeroE) * kfRun ρ W tl g 0) -
        ρ.val (g.e.getD 1 zeroE) * kfRun ρ W tl g 1 := by
    unfold joinRuns
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
      List.sum_append]
    rw [callRuns_value, callRuns_value]
    ring
  rw [Aff.value_sub, Aff.value_ofConst, hc, hr, Finset.sum_range_succ, Finset.sum_range_one]
  ring

end

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The hand-made claim on the key vectors is the flat list's, with its sign. -/
theorem join9_claim (tl : HTailF2) (g : Heard) (lm jLK : ℕ) (rsK : Rounds K) (F0 H : Fork)
    (hs : tl.f9 = g.shape) (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (hH : Later F0 H)
    (hok : FoNums.ok g.shape = true) (h2 : g.shape.NC = 2) (ν : Pl → K) (entry : ℕ → ℕ → ℕ → K) :
    (Aff.ofConst (joinConst tl g) - g.cEnd).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) +
        ((joinRuns tl g).map
          (Run2.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))).sum =
      claimJoin g.shape lm jLK rsK ν
        (kfRun ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) tl g) := by
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H hH).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  rw [join9_value ρ _ tl g hs]
  unfold claimJoin
  rw [val_joinK, h2, hcE, hI.theta, hI.alpha, show rdL ρ g.zy = _ from hI.zy]
  congr 2
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < g.shape.NC := by rw [h2]; exact Finset.mem_range.mp hq
  rw [rdL_getD, show rdL ρ g.e = _ from hI.e, ends_e g.shape hok lm jLK rsK q hq',
    AffK.val_ofConst]

end
end Fo
