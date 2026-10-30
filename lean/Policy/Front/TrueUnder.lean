-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/TrueUnder.lean

From a request that is true under a policy to the claim `MeetsPolicy`
(Policy/Front/MeetsPolicy.lean) on a prompt and output tokens.

The verifier checks a request: a window of 1,024 tokens (the prompt, the output, then a padding that
the prover chooses), a range and a reply token (`requestOfTokens`,
VerifiableInference/RequestOfTokens.lean). `IsTrueUnder` (Policy/Rel/True.lean) speaks of one pass
of the integer program over that window; the claim speaks of the prompt and the output alone. Main
names: `meetsPolicy_of_isTrueUnder` (the step: at a lawful table of scales and valid settings that
are the table's, `tie : settingsOf scales = settings`, for every index, padding and policy);
`meetsPolicy_zeroWeights`, `meetsPolicy_zeroWeights_one_iff`, `meetsPolicy_reads_policy` (guards on
the claim at the all-zero weights).

Sources: the files named here and Policy/Front/Logits.lean; the pattern is
`IntegerModel.isModelOutput_of_isTrueRequest` (IntegerModel/ModelOutput.lean). Terms:
lean/GLOSSARY.md: index, table of scales, request, true request.

Limits: the step loses the clause that the program runs on the whole window; the claim keeps of it
the contexts of the output tokens (`isTrueUnder_iff_meetsPolicy`,
Policy/Front/TrueUnderConverse.lean). Every example is at the all-zero weights, where a gap is 0 or
1 and comes from the rule for ties: no example has two different logits.
-/
import Policy.Rel.TrueGuards
import Policy.Front.Logits
import IntegerModel.ModelOutput
import IntegerModel.Arrays.OfIndex
import Inst.Model.ProgramRGuards

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference
open Inst.Model

/-! ## 1. A request that is true under a policy -/

/-- `IsTrueUnder` (Policy/Rel/True.lean), with the policy's three clauses as one record: the integer
program runs on the 1,024 tokens of the window (no range condition fails at any position, covered or
not); the request has its form (r < e ≤ 1,024, and y = 0 where e < 1,024); and `PolOK`
(Inst/Model/ProgramR.lean) holds of the program's logits on the window. By unfolding. With the
three clauses written out: `isTrueUnder_iff` (Policy/Rel/TrueGuards.lean). -/
theorem isTrueUnder_iff_polOK (s : Cm.Scales) (policy : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) :
    IsTrueUnder s policy i x ↔
      RunsK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt ∧ Head3 x ∧
        PolOK (lgK ppref s.kap s.nf (fun _ => tbRef) i.index.val x.prompt) policy x :=
  Iff.rfl

/-! ## 2. The built request: its contexts and its checked tokens -/

/-- Below position p.length + j, the list p followed by the first j entries of o reads as p followed
by o. -/
theorem getD_append_take {α : Type} (p o : List α) (d : α) {j t : ℕ} (hj : j ≤ o.length)
    (ht : t < p.length + j) : (p ++ o.take j).getD t d = (p ++ o).getD t d := by
  by_cases h : t < p.length
  · rw [IntegerModel.getD_app_left p (o.take j) d t h, IntegerModel.getD_app_left p o d t h]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
    have hk : k < (o.take j).length := by
      rw [List.length_take]
      omega
    rw [IntegerModel.getD_app_right p (o.take j) d k hk,
      IntegerModel.getD_app_right p o d k (by omega), List.getElem_take]

/-- The length of p followed by the first j entries of o. -/
theorem length_append_take {α : Type} (p : List α) {o : List α} {j : ℕ} (hj : j < o.length) :
    (p ++ o.take j).length = p.length + j := by
  rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]

section Built
variable {x : IntegerModel.Request} {p o pad : List IntegerModel.Token}
  (hx : IntegerModel.requestOf p o pad = some x)
include hx

/-- The context of output token j, the prompt and the output tokens before it, is a prefix of the
built request's window, whatever the padding. -/
theorem get_context {j : ℕ} (hj : j < o.length) (hn : (p ++ o.take j).length ≤ ppref.T) (t : ℕ)
    (ht : t < (p ++ o.take j).length) :
    (p ++ o.take j).get ⟨t, ht⟩ = x.prompt ⟨t, lt_of_lt_of_le ht hn⟩ := by
  obtain ⟨-, -, -, htok⟩ := IntegerModel.requestOf_some hx
  have hl := length_append_take p hj
  have hT : t < ppref.T := lt_of_lt_of_le ht hn
  have ht' : t < p.length + j := by omega
  have h1 : x.tok t = ((p ++ o).getD t IntegerModel.tokenZero).val := htok t (by omega)
  have h2 : x.tok t = (x.prompt ⟨t, hT⟩).val := by
    unfold Instance.tok
    rw [dif_pos hT]
  have h3 : (p ++ o.take j).get ⟨t, ht⟩ = (p ++ o).getD t IntegerModel.tokenZero :=
    (List.getD_eq_getElem _ IntegerModel.tokenZero ht).symm.trans
      (getD_append_take p o IntegerModel.tokenZero (Nat.le_of_lt hj) ht')
  exact Fin.ext ((congrArg Fin.val h3).trans (h1.symm.trans h2))

/-- The token that the built request checks at position r + j is output token j. -/
theorem w_requestOf {j : ℕ} (hj : j < o.length) : x.w (x.r + j) = (o[j]).val := by
  obtain ⟨hc, hr, -, htok⟩ := IntegerModel.requestOf_some hx
  show x.tok (x.r + j + 1) = (o[j]).val
  have e : x.r + j + 1 = p.length + j := by
    have h1 := hc.1
    rw [hr]
    omega
  rw [e, htok (p.length + j) (by omega),
    IntegerModel.getD_app_right p o IntegerModel.tokenZero j hj]

/-- With 1,025 tokens in all, the built request's reply token y is the last output token. -/
theorem y_requestOf {j : ℕ} (hj : j < o.length) (full : p.length + j = ppref.T) : x.y = o[j] := by
  obtain ⟨-, -, -, htok⟩ := IntegerModel.requestOf_some hx
  have h1 : x.tok (p.length + j) = (o[j]).val := by
    rw [htok (p.length + j) (by omega),
      IntegerModel.getD_app_right p o IntegerModel.tokenZero j hj]
  have h2 : x.tok (p.length + j) = x.y.val := by
    unfold Instance.tok
    rw [dif_neg (by omega)]
  exact Fin.ext (h2.symm.trans h1)

end Built

/-! ## 3. From the request to the claim -/

section Feeds
variable (m : IntegerModel.Committed) {settings : IntegerTransformer.Settings}
  (weights : ModelWeights settings)
  (hF : IntegerModel.Readable.Feeds m settings lookupTables weights.val)
include hF

/-- The cost of output token j in the claim is the relation's cost of position r + j of the built
request, for an output token whose context fits the window. `hF`: the arrays of the weights hold the
numbers of the committed model m (`Feeds`, IntegerModel/Readable/Tie.lean). -/
theorem outputCost_eq_costOf {x : IntegerModel.Request} {p o pad : List IntegerModel.Token}
    (hx : IntegerModel.requestOf p o pad = some x) {j : ℕ} (hj : j < o.length)
    (hn : p.length + j ≤ ppref.T) :
    outputCost settings weights (p.map Fin.val) (o.map Fin.val) j =
      costOf (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt) x
        (x.r + j) := by
  obtain ⟨⟨hp0, -, -⟩, hr, -, -⟩ := IntegerModel.requestOf_some hx
  have hl := length_append_take p hj
  have hj' : j < (o.map Fin.val).length := by
    rw [List.length_map]
    exact hj
  have h0 : 0 < (p ++ o.take j).length := by omega
  have hn' : (p ++ o.take j).length ≤ ppref.T := by omega
  have e : (p ++ o.take j).length - 1 = x.r + j := by
    rw [hl, hr]
    omega
  unfold outputCost costOf
  rw [List.getD_eq_getElem _ _ hj', List.getElem_map, ← List.map_take, ← List.map_append,
    tokenCost_of_window m weights hF x.prompt (p ++ o.take j) h0 hn' (get_context hx hj hn') o[j],
    e, w_requestOf hx hj]

/-- The step for lists of tokens of the vocabulary, at weights whose arrays hold the numbers of a
committed model m: if the program at m runs on the built request's window, and the policy's clauses
hold of the program's logits on the window, the output meets the policy under the weights' scores.
(A built request has its form: `IntegerModel.requestWellFormed_requestOf`.) -/
theorem meetsPolicy_of_feeds (policy : AcceptancePolicy) {x : IntegerModel.Request}
    {p o pad : List IntegerModel.Token} (hx : IntegerModel.requestOf p o pad = some x)
    (runs : RunsK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt)
    (pol : PolOK (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt)
      policy x) :
    MeetsPolicy settings policy weights (p.map Fin.val) (o.map Fin.val) := by
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
  have context : ∀ j, j < o.length →
      0 < (p ++ o.take j).length ∧ (p ++ o.take j).length ≤ ppref.T := by
    intro j hj
    rw [length_append_take p hj]
    omega
  exact
    { promptNonempty := List.length_pos_iff.1 (by rw [List.length_map]; exact hp0)
      outputNonempty := List.length_pos_iff.1 (by rw [List.length_map]; exact ho0)
      length_le := by
        rw [List.length_map, List.length_map, hpos]
        exact hlen
      inVocabulary := by
        intro token member
        rw [← List.map_append] at member
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 member
        rw [hF.same.sizes.vocabulary]
        exact t.isLt
      defined := by
        intro j hj
        rw [List.length_map] at hj
        rw [← List.map_take, ← List.map_append, modelNextToken_of_feeds m weights hF,
          Option.isSome_map]
        exact IntegerModel.model_isSome_of_window m x.prompt (p ++ o.take j) (context j hj).1
          (context j hj).2 (get_context hx hj (context j hj).2) runs
      meanCost := by
        have ha := pol.a
        unfold Instance.cnt at ha
        rw [Finset.sum_Ico_eq_sum_range] at ha
        rw [hcount]
        refine le_of_eq_of_le (Finset.sum_congr rfl fun j hj => ?_) ha
        rw [cost j (Finset.mem_range.1 hj)]
      aboveClip := by
        have hb := pol.b
        unfold Instance.cnt at hb
        rw [Finset.card_filter, Finset.sum_Ico_eq_sum_range] at hb
        rw [hcount, Finset.card_filter]
        refine le_of_eq_of_le (Finset.sum_congr rfl fun j hj => ?_) hb
        have e := cost j (Finset.mem_range.1 hj)
        by_cases above : (policy.C : ℤ) <
            costOf (lgK ppref m.settings.kap m.settings.nf (fun _ => tbRef) m.weights.val x.prompt)
              x (x.r + j)
        · rw [if_pos above, if_pos (by rw [e]; exact above)]
        · rw [if_neg above, if_neg (by rw [e]; exact above)]
      afterFullWindow := by
        intro j hj full
        have hj' : j < o.length := by
          rw [List.length_map] at hj
          exact hj
        have full' : ppref.T ≤ p.length + j := by
          rw [hpos, List.length_map] at full
          exact full
        have hfull : p.length + j = ppref.T := by omega
        have hlast : (p ++ o.take j).length - 1 = ppref.T - 1 := by
          rw [length_append_take p hj', hfull]
        have gap := pol.c (by rw [hr, he]; omega) (by rw [he]; omega)
        rw [y_requestOf hx hj' hfull] at gap
        have best := (gapOf_eq_zero_iff ppref.V _ (o[j]).isLt).1 gap
        have token := IntegerModel.model_of_window m x.prompt (p ++ o.take j) (context j hj').1
          (context j hj').2 (get_context hx hj' (context j hj').2) runs o[j]
          (by rw [hlast]; exact best.1) (by rw [hlast]; exact best.2)
        rw [← List.map_take, ← List.map_append, modelNextToken_of_feeds m weights hF, token,
          List.getElem_map]
        rfl }

end Feeds

section
variable {scales : Cm.Scales} (lawful : scales.Lawful) {settings : IntegerTransformer.Settings}
  (valid : settingsAreValid settings = true) (tie : settingsOf scales = settings)
include lawful tie

/-- The arrays of an index hold the numbers of the library's committed model at the table and that
index. At `tie := settingsOf_scalesOf valid` it is `feeds_weightsOfIndex`
(IntegerModel/Arrays/OfIndex.lean). -/
theorem feeds_of_tie (index : Cm.Idx) :
    IntegerModel.Readable.Feeds (IntegerModel.committedOf scales lawful index) settings lookupTables
      (weightsOfIndex valid index).val := by
  subst tie
  exact feeds_arrays (IntegerModel.committedOf scales lawful index)

/-- The step for lists of tokens of the vocabulary, at the weights that an index holds. -/
theorem meetsPolicy_of_requestOf (policy : AcceptancePolicy) (index : Cm.Idx) {x : IntegerModel.Request}
    {p o pad : List IntegerModel.Token} (hx : IntegerModel.requestOf p o pad = some x)
    (holds : IsTrueUnder scales policy index x) :
    MeetsPolicy settings policy (weightsOfIndex valid index) (p.map Fin.val) (o.map Fin.val) :=
  meetsPolicy_of_feeds (IntegerModel.committedOf scales lawful index) (weightsOfIndex valid index)
    (feeds_of_tie lawful valid tie index) policy hx
    ((isTrueUnder_iff_polOK scales policy index x).1 holds).1
    ((isTrueUnder_iff_polOK scales policy index x).1 holds).2.2

/-- **From a true request to the claim.** At a lawful table of scales, if the request built from a
prompt, output tokens and a padding is true under a policy at an index, the output meets the policy
under the scores of the weights that the index holds. The padding is the prover's: the statement
holds for every padding, and the claim does not speak of it.
It holds for every policy.

Its sister for exact match is
`IntegerModel.isModelOutput_of_isTrueRequest` (IntegerModel/ModelOutput.lean). `tie` can be met in
two ways: a table with its settings (`tie := rfl`), and settings with their table
(`tie := settingsOf_scalesOf valid`). -/
theorem meetsPolicy_of_isTrueUnder (policy : AcceptancePolicy) (index : Cm.Idx) {x : IntegerModel.Request}
    {prompt output padding : List ℕ} (built : requestOfTokens (prompt, output) padding = some x)
    (holds : IsTrueUnder scales policy index x) :
    MeetsPolicy settings policy (weightsOfIndex valid index) prompt output := by
  obtain ⟨p, o, pad, hp, ho, -, hx⟩ := requestOfTokens_some built
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  exact meetsPolicy_of_requestOf lawful valid tie policy index hx holds

end

/-! ## 4. The all-zero weights -/

/-- The all-zero weights, as arrays: the weights that the matrix of the all-zero index holds. That
every entry of the arrays is 0 is by the definitions of `iZero` and `weightsOfIndex`; no theorem
states it. What the theorems below use is that the index's logits are 0. -/
def zeroWeights {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) : ModelWeights settings :=
  weightsOfIndex valid (Cm.Idx.ofIndex ScalesSanity.iZero)

/-- At valid settings and the all-zero weights, every output meets every policy with 257 ≤ theta and
257 ≤ C, whatever cap is, under the side conditions written out: prompt and output are not empty,
have at most 1,025 tokens together, all in the vocabulary, and a token that follows a full window is
token 0. So at such a policy the claim, said of weights of which one knows only that they exist,
says little. What follows for a statement with an extractor: the head of Ladder.lean.
The half on the relation is
`TrueGuards.zero_all` (Policy/Rel/TrueGuards.lean). -/
theorem meetsPolicy_zeroWeights {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {policy : AcceptancePolicy} (mean : 257 ≤ policy.theta)
    (clip : 257 ≤ policy.C) {prompt output : List Token} (promptNonempty : prompt ≠ [])
    (outputNonempty : output ≠ [])
    (length_le : prompt.length + output.length ≤ settings.positions + 1)
    (inVocabulary : ∀ token ∈ prompt ++ output, token < settings.vocabulary)
    (last : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position → output[position] = 0) :
    MeetsPolicy settings policy (zeroWeights valid) prompt output := by
  have hT : ppref.T = 1024 := by decide
  have hpos : settings.positions = 1024 := (Back.valid_numbers valid).1
  obtain ⟨p, hp⟩ := IntegerModel.vocabularyTokens_of_small prompt fun token member => by
    rw [← vocabulary_eq valid]
    exact inVocabulary token (List.mem_append_left _ member)
  obtain ⟨o, ho⟩ := IntegerModel.vocabularyTokens_of_small output fun token member => by
    rw [← vocabulary_eq valid]
    exact inVocabulary token (List.mem_append_right _ member)
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  have hp0 : 0 < p.length := by
    have := List.length_pos_iff.2 promptNonempty
    rwa [List.length_map] at this
  have ho0 : 0 < o.length := by
    have := List.length_pos_iff.2 outputNonempty
    rwa [List.length_map] at this
  have hlen : p.length + o.length ≤ ppref.T + 1 := by
    rw [List.length_map, List.length_map, hpos] at length_le
    rw [hT]
    exact length_le
  obtain ⟨x, hx⟩ : ∃ x, IntegerModel.requestOf p o [] = some x := by
    unfold IntegerModel.requestOf
    rw [dif_pos ⟨hp0, ho0, hlen⟩]
    exact ⟨_, rfl⟩
  obtain ⟨-, -, he, -⟩ := IntegerModel.requestOf_some hx
  have hy : x.e = ppref.T → x.y.val = 0 := by
    intro heT
    have hj : o.length - 1 < o.length := by omega
    have hfull : p.length + (o.length - 1) = ppref.T := by
      rw [he] at heT
      omega
    have h0 := last (o.length - 1) (by rw [List.length_map]; exact hj)
      (by rw [List.length_map, hpos]; omega)
    rw [List.getElem_map] at h0
    rw [y_requestOf hx hj hfull]
    exact h0
  exact meetsPolicy_of_requestOf (lawful_scalesOf valid) valid (settingsOf_scalesOf valid) policy
    (Cm.Idx.ofIndex ScalesSanity.iZero) hx
    (TrueGuards.zero_all (lawful_scalesOf valid) policy mean clip x
      (IntegerModel.form_of_requestWellFormed (IntegerModel.requestWellFormed_requestOf hx)) hy)

/-- Token 1. -/
def tokenOne : IntegerModel.Token := ⟨1, by decide⟩

/-- At valid settings and the all-zero weights, token 1 costs 257 after the prompt of the one token
0: all logits are 0, the model's first choice is token 0, and token 1 has gap 1 by the rule for
ties. -/
theorem outputCost_zeroWeights_one {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) :
    outputCost settings (zeroWeights valid) [0] [1] 0 = 257 := by
  obtain ⟨x, hx⟩ : ∃ x, IntegerModel.requestOf [IntegerModel.tokenZero] [tokenOne] [] = some x := by
    unfold IntegerModel.requestOf
    rw [dif_pos ⟨by decide, by decide, by decide⟩]
    exact ⟨_, rfl⟩
  have h := outputCost_eq_costOf
    (IntegerModel.committedOf (scalesOf settings) (lawful_scalesOf valid)
      (Cm.Idx.ofIndex ScalesSanity.iZero)) (zeroWeights valid)
    (feeds_of_tie (lawful_scalesOf valid) valid (settingsOf_scalesOf valid) _) hx (j := 0)
    (by decide) (by decide)
  rw [IntegerModel.committedOf_ofIndex, ProgramRGuards.cost_zero, w_requestOf hx (by decide),
    if_neg (by decide)] at h
  exact h

/-- Which policies the output of the one token 1 meets after the prompt of the one token 0, at valid
settings and the all-zero weights: those with min 257 C ≤ theta, and with 1 ≤ cap if C < 257. The
one output token is counted and costs 257: clause (a) reads C and theta, clause (b) reads C and
cap. -/
theorem meetsPolicy_zeroWeights_one_iff {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (policy : AcceptancePolicy) :
    MeetsPolicy settings policy (zeroWeights valid) [0] [1] ↔
      min 257 policy.C ≤ policy.theta ∧ (policy.C < 257 → 1 ≤ policy.cap) := by
  have hpos : settings.positions = 1024 := (Back.valid_numbers valid).1
  have hV : settings.vocabulary = 202048 := (Back.valid_numbers valid).2.2.2.2.2.2.2.2.2.1
  have counted : countedTokens settings [0] [1] = 1 := by
    unfold countedTokens
    rw [hpos]
    rfl
  have cost := outputCost_zeroWeights_one valid
  have base : MeetsPolicy settings ⟨257, 257, 0⟩ (zeroWeights valid) [0] [1] := by
    refine meetsPolicy_zeroWeights valid (by decide) (by decide) (by simp) (by simp)
      (by rw [hpos]; decide) ?_ ?_
    · intro token member
      have small : token = 0 ∨ token = 1 := by simpa using member
      rw [hV]
      rcases small with rfl | rfl <;> decide
    · intro position h full
      have h1 : position < 1 := h
      have h2 : 1024 ≤ 1 + position := by
        rw [hpos] at full
        exact full
      exact absurd h2 (by omega)
  constructor
  · intro h
    have ha := h.meanCost
    have hb := h.aboveClip
    rw [counted, Finset.sum_range_one, cost, Nat.cast_one, mul_one] at ha
    rw [counted] at hb
    refine ⟨by omega, fun small => ?_⟩
    have member : 0 ∈ (Finset.range 1).filter fun position =>
        (policy.C : ℤ) < outputCost settings (zeroWeights valid) [0] [1] position :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 Nat.one_pos, by rw [cost]; omega⟩
    exact le_trans (Finset.card_pos.2 ⟨0, member⟩) hb
  · rintro ⟨mean, limit⟩
    exact
      { toHasScores := base.toHasScores
        meanCost := by
          rw [counted, Finset.sum_range_one, cost, Nat.cast_one, mul_one]
          omega
        aboveClip := by
          rw [counted]
          by_cases small : policy.C < 257
          · exact le_trans (Finset.card_filter_le _ _)
              (by rw [Finset.card_range]; exact limit small)
          · have hf : ((Finset.range 1).filter fun position =>
                (policy.C : ℤ) < outputCost settings (zeroWeights valid) [0] [1] position) = ∅ :=
              Finset.filter_false_of_mem fun position hp => by
                obtain rfl : position = 0 := by
                  have := Finset.mem_range.1 hp
                  omega
                rw [cost]
                omega
            rw [hf]
            exact Nat.zero_le _
        afterFullWindow := base.afterFullWindow }

/-- The claim reads each of the policy's three numbers, and it is not monotone in C. At valid
settings and the all-zero weights, for the output of the one token 1 after the prompt of the one
token 0, with policies written (C, theta, cap):
(256, 256, 1) is met. (256, 256, 0), exact match, is not: cap is read. (300, 256, 1) is not: C is
read in the sum, and a larger clip refuses.
(512, 257, 0) is met. (256, 257, 0) is not: C is read in the count, and a smaller clip refuses.
(512, 256, 0) is not: theta is read.
The gap 1 comes from the rule for ties alone: the example does not bear on whether the weights or
the tokens before the output token are read. -/
theorem meetsPolicy_reads_policy {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) :
    (MeetsPolicy settings ⟨256, 256, 1⟩ (zeroWeights valid) [0] [1] ∧
      ¬ MeetsPolicy settings AcceptancePolicy.exact (zeroWeights valid) [0] [1] ∧
      ¬ MeetsPolicy settings ⟨300, 256, 1⟩ (zeroWeights valid) [0] [1]) ∧
    (MeetsPolicy settings ⟨512, 257, 0⟩ (zeroWeights valid) [0] [1] ∧
      ¬ MeetsPolicy settings ⟨256, 257, 0⟩ (zeroWeights valid) [0] [1] ∧
      ¬ MeetsPolicy settings ⟨512, 256, 0⟩ (zeroWeights valid) [0] [1]) :=
  ⟨⟨(meetsPolicy_zeroWeights_one_iff valid _).2 (by decide),
      fun h => absurd ((meetsPolicy_zeroWeights_one_iff valid _).1 h) (by decide),
      fun h => absurd ((meetsPolicy_zeroWeights_one_iff valid _).1 h) (by decide)⟩,
    ⟨(meetsPolicy_zeroWeights_one_iff valid _).2 (by decide),
      fun h => absurd ((meetsPolicy_zeroWeights_one_iff valid _).1 h) (by decide),
      fun h => absurd ((meetsPolicy_zeroWeights_one_iff valid _).1 h) (by decide)⟩⟩

end Policy

#print axioms Policy.isTrueUnder_iff_polOK
#print axioms Policy.getD_append_take
#print axioms Policy.length_append_take
#print axioms Policy.get_context
#print axioms Policy.w_requestOf
#print axioms Policy.y_requestOf
#print axioms Policy.outputCost_eq_costOf
#print axioms Policy.meetsPolicy_of_feeds
#print axioms Policy.feeds_of_tie
#print axioms Policy.meetsPolicy_of_requestOf
#print axioms Policy.meetsPolicy_of_isTrueUnder
#print axioms Policy.meetsPolicy_zeroWeights
#print axioms Policy.outputCost_zeroWeights_one
#print axioms Policy.meetsPolicy_zeroWeights_one_iff
#print axioms Policy.meetsPolicy_reads_policy
