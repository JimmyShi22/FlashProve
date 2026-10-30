-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/TrueUnderConverse.lean

A guard on the claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean): the way back from the claim to
the relation on a built request. The way there is Policy/Front/TrueUnder.lean.

Main names, each for the request built from a prompt, output tokens and any padding:
`polOK_of_meetsPolicy` (the claim gives `PolOK`, Inst/Model/ProgramR.lean, on the request's window);
`isTrueUnder_iff_meetsPolicy` (true under the policy exactly if the program runs on the window and
the output meets the policy); `isTrueUnder_iff_meetsPolicy_of_full` (with 1,025 tokens in prompt and
output: exactly if the output meets the policy). So what the relation says beyond the claim lies in
one clause: the program runs on the whole window.

Sources: Policy/Front/TrueUnder.lean, IntegerModel/ReplyOnWindow.lean. Terms: lean/GLOSSARY.md:
index, table of scales, request, true request.

Limits: with fewer than 1,025 tokens that clause says more than the claim: no range condition fails
at the last output token's own position or at the padding's. That it says no more than this is an
argument from causality (IntegerModel/ReplyOnWindow.lean, part 1); no theorem states it. The way
back does not guard the clauses of `HasScores`: it has the built request and the run on the window
in hand (on these: `hasScores_iff`, `meetsPolicy_exact_iff`, Policy/Front/MeetsPolicyGuards.lean).
No statement of this file speaks of a prover or a verifier.
-/
import Policy.Front.TrueUnder

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference
open Inst.Model

section Feeds
variable (m : IntegerModel.Committed) {settings : IntegerTransformer.Settings}
  (weights : ModelWeights settings)
  (hF : IntegerModel.Readable.Feeds m settings lookupTables weights.val)
include hF

/-- At weights whose arrays hold the numbers of a committed model m: if the output meets the policy
under the weights' scores, the policy's three clauses hold of the logits of the program's pass over
the window of the built request, whatever the padding. -/
theorem polOK_of_meetsPolicy (policy : AcceptancePolicy) {x : IntegerModel.Request}
    {p o pad : List IntegerModel.Token} (hx : IntegerModel.requestOf p o pad = some x)
    (meets : MeetsPolicy settings policy weights (p.map Fin.val) (o.map Fin.val)) :
    PolOK (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt) policy
      x := by
  obtain ⟨⟨hp0, ho0, hlen⟩, hr, he, -⟩ := IntegerModel.requestOf_some hx
  have hpos : settings.positions = ppref.T := hF.same.sizes.positions
  have hcount : countedTokens settings (p.map Fin.val) (o.map Fin.val) = x.NB := by
    unfold countedTokens Instance.NB
    rw [List.length_map, List.length_map, hpos, hr, he]
    omega
  have inside : ∀ j, j < x.NB → j < o.length ∧ p.length + j ≤ ppref.T := by
    intro j hj
    unfold Instance.NB at hj
    rw [hr, he] at hj
    omega
  have cost : ∀ j, j < x.NB →
      outputCost settings weights (p.map Fin.val) (o.map Fin.val) j =
        costOf (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt) x
          (x.r + j) :=
    fun j hj => outputCost_eq_costOf m weights hF hx (inside j hj).1 (inside j hj).2
  refine ⟨?_, ?_, fun _ heT => ?_⟩
  · have ha := meets.meanCost
    rw [hcount] at ha
    unfold Instance.cnt
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j hj => ?_) ha
    rw [cost j (Finset.mem_range.1 hj)]
  · have hb := meets.aboveClip
    rw [hcount, Finset.card_filter] at hb
    unfold Instance.cnt
    rw [Finset.card_filter, Finset.sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j hj => ?_) hb
    have e := cost j (Finset.mem_range.1 hj)
    by_cases above : (policy.C : ℤ) <
        costOf (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt) x
          (x.r + j)
    · rw [if_pos above, if_pos (by rw [e]; exact above)]
    · rw [if_neg above, if_neg (by rw [e]; exact above)]
  · obtain ⟨j, hj, hfull⟩ : ∃ j, j < o.length ∧ p.length + j = ppref.T :=
      ⟨o.length - 1, by omega, by rw [he] at heT; omega⟩
    have hl := length_append_take p hj
    have h0 : 0 < (p ++ o.take j).length := by omega
    have hn : (p ++ o.take j).length ≤ ppref.T := by omega
    have hlast : (p ++ o.take j).length - 1 = ppref.T - 1 := by rw [hl, hfull]
    have hj' : j < (o.map Fin.val).length := by
      rw [List.length_map]
      exact hj
    have next := meets.afterFullWindow j hj' (by rw [hpos, List.length_map]; omega)
    rw [← List.map_take, ← List.map_append, modelNextToken_of_feeds m weights hF,
      List.getElem_map] at next
    obtain ⟨token, ht, hv⟩ := Option.map_eq_some_iff.1 next
    rw [Fin.ext hv] at ht
    obtain ⟨-, ha⟩ := IntegerModel.model_some ht
    have e : lgK (IntegerModel.arch (p ++ o.take j).length) m.settings.kap m.settings.nf
        (fun _ => tbRef) m.weights.val (fun i => (p ++ o.take j).get i)
        ((p ++ o.take j).length - 1) =
        lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt
          ((p ++ o.take j).length - 1) :=
      IntegerModel.lgK_prefix ppref _ hn m.settings.kap m.settings.nf (fun _ => tbRef)
        m.weights.val x.prompt (fun i => (p ++ o.take j).get i) (get_context hx hj hn)
        (Nat.sub_lt h0 Nat.one_pos)
    rw [e, hlast] at ha
    obtain ⟨-, b1, b2⟩ := argTo_spec
      (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt
        (ppref.T - 1)) (ppref.V - 1)
    rw [ha] at b1 b2
    rw [y_requestOf hx hj hfull]
    exact (gapOf_eq_zero_iff ppref.V _ (o[j]).isLt).2 ⟨fun v hv => b1 v (by omega), b2⟩

/-- With 1,025 tokens in prompt and output together, the context of the last output token is the
whole window of the built request: if the output meets a policy, the program at m runs on the
window. -/
theorem runs_of_meetsPolicy_full (policy : AcceptancePolicy) {x : IntegerModel.Request}
    {p o pad : List IntegerModel.Token} (hx : IntegerModel.requestOf p o pad = some x)
    (full : p.length + o.length = ppref.T + 1)
    (meets : MeetsPolicy settings policy weights (p.map Fin.val) (o.map Fin.val)) :
    RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt := by
  obtain ⟨⟨hp0, ho0, -⟩, -, -, -⟩ := IntegerModel.requestOf_some hx
  have hj : o.length - 1 < o.length := by omega
  have hl := length_append_take p hj
  have whole : (p ++ o.take (o.length - 1)).length = ppref.T := by omega
  have value := meets.defined (o.length - 1) (by rw [List.length_map]; exact hj)
  rw [← List.map_take, ← List.map_append, modelNextToken_of_feeds m weights hF,
    Option.isSome_map] at value
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 value
  exact IntegerModel.runs_of_full m x.prompt (p ++ o.take (o.length - 1)) whole
    (fun t _ ht' => (get_context hx hj (le_of_eq whole) t ht').symm)
    (IntegerModel.model_some hy).1.2.2

end Feeds

/-- At a lawful table of scales: the request built from a prompt, output tokens and a padding is
true under a policy at an index exactly if the integer program runs on its window of 1,024 tokens
(no range condition fails at any position, the padding's too) and the output meets the policy under
the scores of the weights that the index holds. `tie`: as in `meetsPolicy_of_isTrueUnder`. -/
theorem isTrueUnder_iff_meetsPolicy {scales : Cm.Scales} (lawful : scales.Lawful)
    {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (tie : settingsOf scales = settings) (policy : AcceptancePolicy) (index : Cm.Idx)
    {x : IntegerModel.Request} {prompt output padding : List ℕ}
    (built : requestOfTokens (prompt, output) padding = some x) :
    IsTrueUnder scales policy index x ↔
      RunsK ppref scales.kap scales.nf (fun _ => tbRef) index.index.val x.prompt ∧
        MeetsPolicy settings policy (weightsOfIndex valid index) prompt output := by
  refine ⟨fun holds => ⟨((isTrueUnder_iff_polOK scales policy index x).1 holds).1,
    meetsPolicy_of_isTrueUnder lawful valid tie policy index built holds⟩, ?_⟩
  rintro ⟨runs, meets⟩
  obtain ⟨p, o, pad, hp, ho, -, hx⟩ := requestOfTokens_some built
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  exact (isTrueUnder_iff_polOK scales policy index x).2 ⟨runs,
    IntegerModel.form_of_requestWellFormed (IntegerModel.requestWellFormed_requestOf hx),
    polOK_of_meetsPolicy (IntegerModel.committedOf scales lawful index)
      (weightsOfIndex valid index) (feeds_of_tie lawful valid tie index) policy hx meets⟩

/-- At a lawful table of scales, with 1,025 tokens in prompt and output together (no padding enters
the window): the built request is true under a policy at an index exactly if the output meets the
policy under the scores of the weights that the index holds. `tie`: as in
`meetsPolicy_of_isTrueUnder`. -/
theorem isTrueUnder_iff_meetsPolicy_of_full {scales : Cm.Scales} (lawful : scales.Lawful)
    {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (tie : settingsOf scales = settings) (policy : AcceptancePolicy) (index : Cm.Idx)
    {x : IntegerModel.Request} {prompt output padding : List ℕ}
    (built : requestOfTokens (prompt, output) padding = some x)
    (full : prompt.length + output.length = settings.positions + 1) :
    IsTrueUnder scales policy index x ↔
      MeetsPolicy settings policy (weightsOfIndex valid index) prompt output := by
  refine (isTrueUnder_iff_meetsPolicy lawful valid tie policy index built).trans
    ⟨fun h => h.2, fun meets => ⟨?_, meets⟩⟩
  obtain ⟨p, o, pad, hp, ho, -, hx⟩ := requestOfTokens_some built
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  have hF := feeds_of_tie lawful valid tie index
  rw [List.length_map, List.length_map, hF.same.sizes.positions] at full
  exact runs_of_meetsPolicy_full (IntegerModel.committedOf scales lawful index)
    (weightsOfIndex valid index) hF policy hx full meets

end Policy

#print axioms Policy.polOK_of_meetsPolicy
#print axioms Policy.runs_of_meetsPolicy_full
#print axioms Policy.isTrueUnder_iff_meetsPolicy
#print axioms Policy.isTrueUnder_iff_meetsPolicy_of_full
