-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerGuards.lean

Guards on the relation pair with the cost ledger, modulo 2^64 - 2^32 + 1: "has a witness" is not
empty and not everything under a policy that is looser than exact match
(Policy/Rel/TrueGuards.lean), and it reads each of the policy's three numbers (C, θ, cap).

`HasWitness s pol i x`: x has a relaxed witness at i (`LedgerRel.Rno`; a strict witness is one of
`LedgerRel.Ryes`). `hasWitness_iff`, `trace_iff_true` (at a lawful table and a policy with
`PolCond`) and `guard_form` (at every table and policy) are for every index.

The other guards are for every lawful table of scales (there is one: `lawful_sRef`,
Cm/Rel2Guards.lean), at the index of the all-zero weights. There every logit is 0: token 0 is the
first choice everywhere, a checked token 0 costs 2^8, any other 2^8 + 1. `x1` has 1,023 counted
positions, none of which checks the first choice; `xOne` has 1,023, of which position 0 alone does
not (Inst/Model/RequestGuards2.lean, Inst/Model/ProgramRGuards.lean).

Limits:
* The policies at which `guard_budget`, `guard_cap`, `guard_mean` and `guard_clip` refuse have the
  relation of exact match (`rinfR_iff_rinfS`, Inst/Model/RequestGuards2.lean; at (2^8, 2^8 + 1, 0)
  by hand, no theorem); only `guard_refuses` refuses under a looser policy.
* All logits of the all-zero weights are equal: the gap 1 is a lost tie, and which position's logits
  meet which token is not seen. Policy/Rel/PosGuards.lean has weights with gaps of 2,047 and 2,048.
* Guards that read a layer's weights and the tokens before a position exist at exact match only
  (Cm/RelTrue.lean). No theorem states those on "has a witness" for this pair.
-/
import Policy.Rel.TrueGuards
import Policy.Rel.LedgerRelLaws

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerGuards

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity Inst.Model.ProgramRGuards
  Inst.Model.RequestGuards2

/-- The request x has a relaxed witness at the index i, modulo 2^64 - 2^32 + 1, at the table s of
scales and the policy pol. -/
def HasWitness (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) : Prop :=
  ∃ T, LedgerRel.Rno (2 ^ 64 - 2 ^ 32 + 1) (ppOf s pol) i x T

/-! In this section s is a lawful table of scales. The guards `guard_..` are at the index of the
all-zero weights. -/

section
variable {s : Cm.Scales} (hs : s.Lawful)
include hs

/-- For a policy with `PolCond`: a request has a relaxed witness if and only if it is true under the
policy. -/
theorem hasWitness_iff {pol : AcceptancePolicy} (hpol : PolCond pol) (i : Cm.Idx) (x : Instance ppref) :
    HasWitness s pol i x ↔ IsTrueUnder s pol i x :=
  (ledger_lang Code.pGold Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x).2

/-- For a policy with `PolCond`: the honest trace is a strict witness if and only if the request is
true under the policy. -/
theorem trace_iff_true {pol : AcceptancePolicy} (hpol : PolCond pol) (i : Cm.Idx) (x : Instance ppref) :
    LedgerRel.Ryes (2 ^ 64 - 2 ^ 32 + 1) (ppOf s pol) i x (Cm.trace (ppOf s pol) i x) ↔
      IsTrueUnder s pol i x :=
  ledger_trace_iff Code.pGold Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x

/-- for a policy with `PolCond`, at the index that holds given weights: a witness if and only if the
integer relation holds -/
theorem hasWitness_ofIndex {pol : AcceptancePolicy} (hpol : PolCond pol) (j : Index ppref)
    (x : Instance ppref) :
    HasWitness s pol (Cm.Idx.ofIndex j) x ↔ RinfR ppref s.kap s.nf (fun _ => tbRef) pol j x :=
  (hasWitness_iff hs hpol _ x).trans (isTrueUnder_ofIndex s pol j x)

/-- the table s with the policy of exact match is lawful in the sense of Inst/Model/Scales.lean;
the guards of Inst/Model/ read of it the scales alone -/
theorem lawful_exact : Lawful (ppOf s AcceptancePolicy.exact) := hs.toPP

/-- A policy that is not exact match admits what exact match rejects: a reply none of whose 1,023
tokens is the first choice has a witness at (512, 2^8 + 1, 0), and none at exact match. -/
theorem guard_budget :
    HasWitness s ⟨512, 257, 0⟩ (Cm.Idx.ofIndex iZero) x1 ∧
    ¬ HasWitness s AcceptancePolicy.exact (Cm.Idx.ofIndex iZero) x1 :=
  have h0 := budget (lawful_exact hs)
  ⟨(hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero x1).2 h0.1,
    fun h => h0.2 ((hasWitness_ofIndex hs AcceptancePolicy.exact_ok iZero x1).1 h)⟩

/-- A policy that is looser than exact match refuses: at (2^8, 2^8, 1) `xOne`, with one counted
position above the clip, has a witness; `x1`, with 1,023, has none. -/
theorem guard_refuses :
    HasWitness s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) xOne ∧
    ¬ HasWitness s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) x1 :=
  have hp : PolCond ⟨256, 256, 1⟩ := ⟨by norm_num, by norm_num, by norm_num⟩
  ⟨(hasWitness_iff hs hp _ _).2 (TrueGuards.two_replies hs).2.1,
    fun h => TrueGuards.looser_refuses hs ((hasWitness_iff hs hp _ _).1 h)⟩

/-- cap is read: one counted position is above the clip; a witness if the policy allows one, none
if it allows none. -/
theorem guard_cap :
    HasWitness s ⟨256, 256, 1⟩ (Cm.Idx.ofIndex iZero) xOne ∧
    ¬ HasWitness s AcceptancePolicy.exact (Cm.Idx.ofIndex iZero) xOne :=
  have h1 := one_cap (lawful_exact hs)
  have h0 := one_not_exact (lawful_exact hs)
  ⟨(hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero xOne).2 h1,
    fun h => h0 ((hasWitness_ofIndex hs AcceptancePolicy.exact_ok iZero xOne).1 h)⟩

/-- θ is read: the costs add up to 2^8 · 1,023 + 1; a witness at the bound 2^8 + 1 on the mean, none
at the bound 2^8. -/
theorem guard_mean :
    HasWitness s ⟨300, 257, 0⟩ (Cm.Idx.ofIndex iZero) xOne ∧
    ¬ HasWitness s ⟨300, 256, 0⟩ (Cm.Idx.ofIndex iZero) xOne :=
  have h1 := one_mean (lawful_exact hs)
  have h0 := one_mean_not (pp := ppOf s AcceptancePolicy.exact)
  ⟨(hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero xOne).2 h1,
    fun h => h0 ((hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero xOne).1 h)⟩

/-- C is read: `xOne` has no witness at two policies, each of which differs in the clip alone from
one at which it has a witness. In the count: at the clip 2^8, with `guard_mean`'s other two numbers,
position 0 is above the clip. In the sum: at the clip 300, with `guard_cap`'s other two numbers, the
cost 2^8 + 1 is not clipped. -/
theorem guard_clip :
    ¬ HasWitness s ⟨256, 257, 0⟩ (Cm.Idx.ofIndex iZero) xOne ∧
    ¬ HasWitness s ⟨300, 256, 1⟩ (Cm.Idx.ofIndex iZero) xOne :=
  have h0 := one_clip_not (pp := ppOf s AcceptancePolicy.exact)
  have h1 := one_clip_sum_not (pp := ppOf s AcceptancePolicy.exact)
  ⟨fun h => h0 ((hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero xOne).1 h),
    fun h => h1 ((hasWitness_ofIndex hs ⟨by norm_num, by norm_num, by norm_num⟩ iZero xOne).1 h)⟩

/-- `PolCond` reaches beyond `Lawful`: (2^8, 2^8 + 1, 1) meets it, the table with this policy is not
lawful (θ > C), and the honest trace of `xOne` is a strict witness there. -/
theorem guard_wider :
    PolCond ⟨256, 257, 1⟩ ∧ ¬ Lawful (ppOf s ⟨256, 257, 1⟩) ∧
    LedgerRel.Ryes (2 ^ 64 - 2 ^ 32 + 1) (ppOf s ⟨256, 257, 1⟩) (Cm.Idx.ofIndex iZero) xOne
      (Cm.trace (ppOf s ⟨256, 257, 1⟩) (Cm.Idx.ofIndex iZero) xOne) :=
  have hp : PolCond ⟨256, 257, 1⟩ := ⟨by norm_num, by norm_num, by norm_num⟩
  have h1 := one_cap (lawful_exact hs)
  ⟨hp, fun h => absurd h.pol.2.1 (by norm_num),
    (trace_iff_true hs hp _ _).2 ((isTrueUnder_ofIndex s _ iZero xOne).2
      ⟨h1.1, h1.2.1, TrueGuards.polOK_mono (pol := ⟨256, 256, 1⟩) (pol' := ⟨256, 257, 1⟩) rfl
        (by norm_num) (le_refl _) h1.2.2⟩)⟩

end

/-- A request with a witness has its form, at every table, policy and index. -/
theorem guard_form (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref)
    (h : HasWitness s pol i x) : Head3 x := by
  obtain ⟨T, hR⟩ := h
  haveI : Cm.TI.Big (2 ^ 64 - 2 ^ 32 + 1) := ⟨ledger_gl_big⟩
  haveI : Fact (Nat.Prime (2 ^ 64 - 2 ^ 32 + 1)) := ⟨Code.pGold_prime⟩
  exact (Cm.TP.form_iff (p := 2 ^ 64 - 2 ^ 32 + 1) x).1 ⟨hR.1, hR.2.2.yZero⟩

end Policy.LedgerGuards
