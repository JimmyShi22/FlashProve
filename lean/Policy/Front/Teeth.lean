-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/Teeth.lean

A guard on the claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean): a policy's clauses on the mean
cost (`meanCost`) and on the number of tokens above the clip (`aboveClip`) can refuse an output at
large numbers too. It carries Policy/Rel/Teeth.lean from a request to a prompt and output tokens,
through `isTrueUnder_iff_meetsPolicy` (Policy/Front/TrueUnderConverse.lean).

The prompt is the one token 0, the output n tokens 0, for 1 ≤ n ≤ 1,024. The weights are those that
the index `idxAB h` holds: under them every output token costs 2^8 + 2,047 (a + b).

Main names:
* `built_xz`: the request built from this prompt and output, without padding, is `xz` with r = 0 and
  e = n (Inst/Model/RequestGuards2.lean).
* `meetsPolicy_iff_xz`: the output meets a policy if and only if that request is true under it. With
  `xz_iff` (Policy/Rel/Teeth.lean) this says for which policies.
* `teeth_in_range_meetsPolicy`: at the weights of `iTeeth`, the output of 1,023 tokens 0
  does not meet any policy with θ < C and θ < 16,767,233, or with C < 16,767,233 and cap < 1,023.
  It meets (16,767,233, 16,767,233, 0). `HasScores` and `afterFullWindow` do not read the policy, so
  what refuses the output is `meanCost` or `aboveClip`.
  Outside this range nothing is shown here. With C ≤ θ and cap at least the number of counted
  tokens, the two clauses hold of every output that has scores (`meetsPolicy_iff_of_clip_le_mean`,
  Policy/Front/MeetsPolicyGuards.lean).
* `teeth_meetsPolicy`: for one output token and a, b with `Votes`, the output does not meet a policy
  with θ < C and θ < k, or with C < k and cap = 0, where k = 2^8 + 2,047 (a + b).

Limits: those of Policy/Rel/Teeth.lean. The weights are made up, with the same logits after every
context. The theorems show that the two clauses can refuse. They do not show that these clauses
refuse anything at a trained model, or how often. Every refusal shown here is of an output whose
counted tokens all have one cost: 2^8 + 2,047 (a + b). It runs from 2^8 at a = b = 0, where every
output token is the first choice, to 16,767,233 at `iTeeth`, where every output token is the token
of least logit. No output that has the first choice at some positions and another token at others is
shown refused here. At a policy with θ < C no theorem here shows `aboveClip` refusing an output that
`meanCost` admits; for requests Policy/Rel/TeethCount.lean does (`cap_alone_decides`); for outputs
compare `qExample_far_iff` (Policy/Front/MeetsPolicyAtGap.lean). The range is over all triples
(C, θ, cap), whether or not they pass `PolTests` (Inst/Model/ProgTests.lean). A cost is a gap plus
2^8 (`tokenCost`, Policy/Front/MeetsPolicy.lean; the constant is that of `Inst.Model.costOf`): no
other exponent than 8 is covered, and that the claim's clauses are what the programs test is no
theorem (the head of Inst/Model/ProgramR.lean). All statements are at the settings of the reference
scales (`settingsOf Cm.sRef`) alone. Nothing here speaks of a protocol, a prover or a verifier.

Terms: lean/GLOSSARY.md.

-/
import Policy.Rel.Teeth
import Policy.Front.TrueUnderConverse

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.Teeth

open VerifiableInference
open Inst.Model Inst.Model.RequestGuards2

/-- For 1 ≤ n ≤ 1,024 (the hypotheses `h0`, `hn`): the request built from the prompt of one token 0,
the output of n tokens 0 and no padding is `xz` with r = 0 and e = n. Token 0 fills the window. -/
theorem built_xz {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1024) :
    requestOfTokens ([0], List.replicate n 0) [] =
      some (xz ⟨0, by decide⟩ ⟨n, Nat.lt_succ_of_le hn⟩) := by
  have z1 : vocabularyTokens [0] = some [IntegerModel.tokenZero] :=
    vocabularyTokens_map_val [IntegerModel.tokenZero]
  have z2 : vocabularyTokens (List.replicate n 0) =
      some (List.replicate n IntegerModel.tokenZero) := by
    have := vocabularyTokens_map_val (List.replicate n IntegerModel.tokenZero)
    rwa [List.map_replicate] at this
  rw [requestOfTokens_eq z1 z2 rfl]
  unfold IntegerModel.requestOf
  rw [dif_pos ⟨by decide, by rw [List.length_replicate]; exact h0, by
    rw [List.length_replicate]
    show 1 + n ≤ 1024 + 1
    omega⟩]
  have all : ∀ j, ([IntegerModel.tokenZero] ++ List.replicate n IntegerModel.tokenZero).getD j
      IntegerModel.tokenZero = IntegerModel.tokenZero := fun j => by
    rw [List.singleton_append, ← List.replicate_succ, List.getD_eq_getElem?_getD,
      List.getElem?_replicate]
    split <;> rfl
  refine congrArg some ?_
  unfold xz
  congr 1
  · funext t
    rw [List.append_nil, all]
    rfl
  · rw [all]
    rfl
  · apply Fin.ext
    show 1 - 1 + (List.replicate n IntegerModel.tokenZero).length = n
    rw [List.length_replicate]
    omega

/-- For a, b with `Votes`, every policy and 1 ≤ n ≤ 1,024, at the settings of the reference scales
and the weights that `idxAB h` holds: after the prompt of one token 0 the output of n tokens 0 meets
the policy if and only if the request `xz` with r = 0 and e = n is true under it. -/
theorem meetsPolicy_iff_xz {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) {n : ℕ} (h0 : 0 < n)
    (hn : n ≤ 1024) :
    MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [0]
        (List.replicate n 0) ↔
      IsTrueUnder Cm.sRef pol (idxAB h) (xz ⟨0, by decide⟩ ⟨n, Nat.lt_succ_of_le hn⟩) := by
  rw [isTrueUnder_iff_meetsPolicy Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl
    pol (idxAB h) (built_xz h0 hn)]
  exact ⟨fun m => ⟨runsK_idxAB h _, m⟩, fun m => m.2⟩

/-- **Every policy in the range refuses one output that another policy admits.** The hypothesis `h`
is the range: θ < C and θ < 16,767,233, or C < 16,767,233 and cap < 1,023. At the settings of the
reference scales and the weights that `iTeeth` holds, after the prompt of one token 0, the output of
1,023 tokens 0 does not meet such a policy, and it meets (C, θ, cap) = (16,767,233, 16,767,233, 0).
Weights, prompt and output do not depend on the policy. The weights are made up: see the limits at
the top of this file. -/
theorem teeth_in_range_meetsPolicy (pol : AcceptancePolicy)
    (h : (pol.theta < pol.C ∧ pol.theta < 16767233) ∨ (pol.C < 16767233 ∧ pol.cap < 1023)) :
    ¬ MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeeth) [0]
        (List.replicate 1023 0) ∧
      MeetsPolicy (settingsOf Cm.sRef) ⟨16767233, 16767233, 0⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeeth) [0]
        (List.replicate 1023 0) :=
  ⟨fun m => (teeth_in_range pol h).1
      ((meetsPolicy_iff_xz _ pol (by norm_num) (by norm_num)).1 m),
    (meetsPolicy_iff_xz _ _ (by norm_num) (by norm_num)).2 (teeth_in_range pol h).2⟩

/-- One output token. For a, b with `Votes`, with k = 2^8 + 2,047 (a + b). The hypothesis `hp`:
θ < C and θ < k, or C < k and cap = 0. Then after the prompt of one token 0 the output of one token
0 does not meet the policy. -/
theorem teeth_meetsPolicy {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy)
    (hp : (pol.theta < pol.C ∧ (pol.theta : ℤ) < 2 ^ 8 + 2047 * (a + b)) ∨
      ((pol.C : ℤ) < 2 ^ 8 + 2047 * (a + b) ∧ pol.cap = 0)) :
    ¬ MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [0] [0] := by
  intro m
  have t := (meetsPolicy_iff_xz h pol (n := 1) (by norm_num) (by norm_num)).1 m
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact teeth_mean h pol h1 h2 _ _ (by decide) t
  · exact teeth_count h pol h1 _ _ (by rw [h2]; decide) t

end Policy.Teeth
