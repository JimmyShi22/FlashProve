-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowHalf.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, ALL BUT THE NORMALIZATION's 17 ROW FORMS: WHAT THE BLOCK OPENS GIVES
WHAT IT CLOSES: STATED AND PROVED, at Head.lean's hear (the block's one hearing), under the block's rule by name, with the
reads read as the stated sums of the cells.
  block_parts   where hear returns and no draw is bad under blockRule: the two sumchecks, each at its own rounds, from a
                WellLaid ledger, canonical, with no bad draw under its own rule by name. (Its lines stand inside
                Law/OutBlock.lean's outBlock_at too.)
  RowHalfStatement   OPENED, behind the block, at any ledger G later than the one that the block lays: ALL 35 FORMS of the
                block's three runs (claims, by name) worth 0; the claim on the weights true. CLOSED, in front:
                  sums    meanAt c = 0 and countAt c = 0: the two plain sums of the relation's part "idn";
                  keys    each of the six calls' key vectors is worth the extension of the call's table at its key point;
                  rider   the two guests' corner values, summed under the weights of zt, are 0.
                With Law/JoinValue.lean's join_exchange "keys" turns the form of "join" at the caller's forms into the
                lookup's formula at the key vectors' true values.
NOT HERE: the 17 row forms at every corner (norm_rows, from the other 26 forms of "norm", under rules of its own on
the normalization's rounds); the planes. WHAT IT DOES NOT SAY: that the forms are 0; that the claim on the weights is
true; how probable a bad draw is.
IMPORTED, NOT PROVED HERE: Law/Clamp.lean (k06Core_at, k06Glue), K06Statement.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OutTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- **THE ROW, ALL BUT THE 17 ROW FORMS.** -/
def RowHalfStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork),
    planOk sT = true → Request.ok = true → y < V → WellLaid F → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∀ (rs : List Fmt.RoundView) (H : HeardAll) (F1 G : Fork),
      Canonical rs → hear F rs = some (H, F1, []) → Later F1 G → NoBad (Came.blockRule c mask F) rs →
      let _ : Norm.Heard := H.1
      let _ : FinalNorm.Heard := H.2.1
      let _ : Heard := H.2.2
      let _ : FinalNorm.Reads := normReadsAtCells c
      let _ : Reads := readsAt c.toCells
      WeightTrue c.toCells G mask noEnt →
      (∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) →
      (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
      (∀ call, call < 6 →
        rd (atWorld G mask noEnt
            (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
          = (Finset.range (2 ^ (zk call).size)).sum fun i =>
              rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
      (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
      (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0

namespace Came

/-- **Where the block's hearing returns and no draw is bad under its rule.** -/
theorem block_parts [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) (hWL : WellLaid F) {rs : List Fmt.RoundView} {H : HeardAll} {F1 : Fork}
    (hcan : Canonical rs) (hhear : hear F rs = some (H, F1, []))
    (hnb : NoBad (blockRule c mask F) rs) :
    ∃ (Fa Fb : Fork) (tN tL : List Fmt.RoundView), WellLaid Fa ∧ WellLaid Fb ∧ Canonical tN ∧ Canonical tL ∧
      sumcheck FinalNorm.zt 2 Fa tN = some (H.2.1.normed, Fb, []) ∧
      sumcheck (FinalNorm.zt ++ halves lPd) 2 Fb tL = some (H.2.2.logits, F1, []) ∧
      NoBad (normedRule c mask Fa) tN ∧ NoBad (badP c.toCells mask Fb) tL := by
  obtain ⟨Fa, Fb, l1, hNorm, hWa, hWb, hsN, hsL, hleft⟩ := hear_parts hWL hhear
  obtain ⟨pre0, hrs, eN⟩ := consumes_norm _ _ _ _ _ hNorm
  obtain ⟨pN, hpN, eS⟩ := consumes_sumcheck _ _ _ _ _ _ _ hsN
  rw [List.append_nil] at hpN
  -- the rounds, cut
  have hlenN : (l1.take ((FinalNorm.zt).size + 3)).length = (FinalNorm.zt).size + 3 := by
    have h0 : (l1.take ((FinalNorm.zt).size + 3)).length = (FinalNorm.zt).size + 3 := by
      obtain ⟨_, _, h3⟩ := sumcheck_cut hsN
      rw [List.length_take] at h3 ⊢
      omega
    exact h0
  have hL' : (l1.drop ((FinalNorm.zt).size + 3)).take
      ((FinalNorm.zt ++ halves Norm.lPd).size + 3) = l1.drop ((FinalNorm.zt).size + 3) := by
    apply List.take_of_length_le
    have h0 := congrArg List.length hleft
    rw [List.length_nil, List.length_drop] at h0
    omega
  rw [hL'] at hsL
  have hcut : rs = pre0 ++ l1.take ((FinalNorm.zt).size + 3) ++ l1.drop ((FinalNorm.zt).size + 3) := by
    rw [List.append_assoc, List.take_append_drop]
    exact hrs
  have hcanN : Canonical (l1.take ((FinalNorm.zt).size + 3)) := fun r hr =>
    hcan r (by rw [hcut]; exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hcanL : Canonical (l1.drop ((FinalNorm.zt).size + 3)) := fun r hr =>
    hcan r (by rw [hcut]; exact List.mem_append_right _ hr)
  -- no bad draw under either rule
  have hnbN : NoBad (normedRule c mask Fa) (l1.take ((FinalNorm.zt).size + 3)) := by
    have hnb0 : NoBad (tailRule (normedRule c mask) (badP c.toCells mask) F) rs := hnb
    rw [hcut] at hnb0
    refine noBad_sub (fun i r hi => ?_) hnb0
    have hil : i < (l1.take ((FinalNorm.zt).size + 3)).length :=
      (List.getElem?_eq_some_iff.mp hi).1
    unfold tailRule
    rw [eN]
    dsimp only
    rw [if_pos]
    rw [List.length_append, List.length_take, List.length_singleton]
    omega
  have hnbL : NoBad (badP c.toCells mask Fb) (l1.drop ((FinalNorm.zt).size + 3)) := by
    have hnb' : NoBad (tailRule (normedRule c mask) (badP c.toCells mask) F)
        ((pre0 ++ l1.take ((FinalNorm.zt).size + 3)) ++ l1.drop ((FinalNorm.zt).size + 3) ++ []) := by
      rw [List.append_nil, ← hcut]
      exact hnb
    refine noBad_sub (fun i r hi => ?_) hnb'
    unfold tailRule
    rw [List.append_assoc, eN]
    dsimp only
    rw [if_neg (by rw [List.length_append, hlenN, List.length_append, List.length_singleton]; omega),
      hpN, eS]
  exact ⟨Fa, Fb, _, _, hWa, hWb, hcanN, hcanL, hsN, hsL, hnbN, hnbL⟩

theorem rowHalf : RowHalfStatement := by
  intro _ _ _ _ nI hI sT floor zx zk c mask F hplan hreq hy hWL hP hn hh rs H F1 G hcan hhear hL hnb
    _ _ _ _ _ hwt hall
  have hlog : ∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0 :=
    fun fs h => hall "logits" fs h
  have hnorm : ∀ f, f ∈ FinalNorm.forms → atWorld G mask noEnt f = 0 :=
    hall "norm" FinalNorm.forms (by simp [claims, List.lookup])
  have hpol : ∀ f, f ∈ policy → atWorld G mask noEnt f = 0 :=
    hall "policy" policy (by simp [claims, List.lookup])
  have hnf : ∀ f, f ∈ FinalNorm.normedForms → atWorld G mask noEnt f = 0 := fun f hf =>
    hnorm f (by unfold FinalNorm.forms; exact List.mem_append_right _ hf)
  obtain ⟨hkeys, hclip, htable⟩ := outTrue sT floor zx zk c mask F hplan hreq hy hWL hP hn hh rs H F1 G
    hcan hhear hL hnb hwt hlog hnf
  -- the letters
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have L := fromLookup_law floor zx zk hV (lens_small hplan) hP
  have hS2 : ∀ k : Key, S2 ∣ len k := S2_dvd_len P
  have hw : WeightsOk := by
    subst hn
    subst hh
    letI : FinalNorm.In := (fromLookup floor zx zk).norm
    letI : In := (fromLookup floor zx zk).head
    exact ⟨fun k x hx => L.block (.inr k) (hS2 k) x hx, fun k => L.wsum (.inr k), L.wx, L.below⟩
  have hzt : (FinalNorm.zt).size = lt := by
    subst hn
    exact L.zt
  -- the core, at the head's sumcheck's own rounds
  obtain ⟨Fa, Fb, tN, tL, _, hWb, _, hcanL, _, hsL, _, hnbL⟩ := block_parts c mask F hWL hcan hhear hnb
  have hreads : TrueReads c.toCells G mask noEnt := fun _ _ _ => rfl
  have hcore := k06Core_at c.toCells mask Fb hreq hy hWb hzt F1 tL H.2.2.logits G noEnt hcanL hsL hL
    hreads hwt hlog hnbL
  obtain ⟨_, _, _, hmean, hcount⟩ := k06Glue c.toCells G mask noEnt hreq hy hw hzt hreads hcore
  refine ⟨⟨?_, ?_⟩, hkeys, ?_, ?_⟩
  · rw [← hmean]; exact hpol mean (by simp [policy])
  · rw [← hcount]; exact hpol count (by simp [policy])
  · rw [← hclip]; exact hpol clip (by simp [policy])
  · rw [← htable]; exact hpol table (by simp [policy])

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.block_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowHalf
