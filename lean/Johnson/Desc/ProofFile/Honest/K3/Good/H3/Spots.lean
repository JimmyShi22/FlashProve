-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Spots.lean: the kind "lookup" (K3): at every spot of the
lookup's two marks (`spots`, `spotsOut`, Honest/K3/GoodDraws.lean) the verifier's list of rounds has
a round, and that round draws enough elements by the even rule (`SpotLaid`,
Honest/K3/Good/H3/Defs.lean); and the rounds that sample alpha and the shift. Conditional. Theorems
on public data.

Terms. Honest/K3/GLOSSARY.md: see there spot, stage and face. In this file: f is a lookup's face and
s a stage of its row.

What is shown.
  `spot_laid`: every spot of the first mark is laid.
  `spotOut_laid`: every spot of the second mark is laid.
  `alpha_laid`, `shift_laid`: the entries of the rounds that sample alpha and the shift.
Helpers: `at_zero`, `at_succ` (on lists); `entry_at` (from a stage's own rounds to the verifier's
list); `entries_call`, `entries_none`; `eps_laid`, `var_laid`, `draw_laid`; `spotsAt_laid`;
`key_in`, `leaves_in`, `bits_in`, `alpha_in`, `shift_in` (stages that stand in the row);
`level_vars`, `leaf_vars`, `bits_vars` (how many variables a stage's sumcheck has).

Hypotheses that remain.
  `h2`: the face has two planes at least: with fewer the verifier's list and the row's stages part
    (`entries_stages`, Honest/K3/RowLaw.lean, asks it).
  `h1`: (in `spotOut_laid`) each part of the keys has a bit at least: at a part of no bit the second
    mark names a stage that does not stand in the row.
  `hs`: (in `shift_laid`) the face has a shift.

Users. Honest/K3/Good/H3/Fence.lean [not in this library], FewOfCap.lean, LeafOfCap.lean and
Guards.lean.

Limits. No sampled value is read. The verifier's own test on a face's numbers (`Face.ok`) is not
asked. That h2 and h1 are needed is tried at a small synthetic face in Honest/K3/Good/H3/Teeth.lean
[not in this library].
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Defs
import Johnson.Desc.ProofFile.Honest.K3.RowAt
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc.Part (MaskedSum.entries MaskedSum.entry)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.K3 (entriesV drawEntry leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV (levelVars)

/-! ## 1 On lists -/

theorem at_zero {α : Type} (a : α) (X Y : List α) : ([a] ++ X ++ Y)[0]? = some a := by
  rw [List.append_assoc, List.singleton_append, List.getElem?_cons_zero]

theorem at_succ {α : Type} (a : α) (X Y : List α) (l : Nat) (hl : l < X.length) :
    ([a] ++ X ++ Y)[1 + l]? = X[l]? := by
  rw [List.append_assoc, List.singleton_append, Nat.add_comm 1 l, List.getElem?_cons_succ,
    List.getElem?_append_left hl]

/-! ## 2 From a stage's own rounds to the verifier's list -/

/-- A round of a stage stands in the verifier's list behind the rounds in front of the stage. -/
theorem entry_at (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) (j : Nat)
    (en : Fmt.Entry) (h : (Stage.entries f s)[j]? = some en) :
    (entriesV f)[firstRound f s + j]? = some en := by
  rw [← entries_at f h2 s hs, List.getElem?_take] at h
  split at h
  · rw [List.getElem?_drop] at h
    exact h
  · cases h

theorem entries_call (f : LFace) (s : Stage) (k : Call) (hk : s.call f = some k) :
    Stage.entries f s = MaskedSum.entries k := by
  unfold Stage.entries
  rw [hk]

theorem entries_none (f : LFace) (s : Stage) (hk : s.call f = none) :
    Stage.entries f s = [drawEntry s.name (s.draws f)] := by
  unfold Stage.entries
  rw [hk]

/-- The round that samples a sumcheck's eps. -/
theorem eps_laid (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) (k : Call)
    (hk : s.call f = some k) (one : Bool) : SpotLaid f ⟨s, 0, 0, one⟩ := by
  unfold SpotLaid
  refine ⟨MaskedSum.entry "PSC epsilon" (k.lead + 1) 1 0, entry_at f h2 s hs 0 _ ?_, rfl,
    Nat.zero_lt_one⟩
  rw [entries_call f s k hk]
  unfold MaskedSum.entries
  exact at_zero _ _ _

/-- The round that samples the challenge of a sumcheck's variable. -/
theorem var_laid (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) (k : Call)
    (hk : s.call f = some k) (l : Nat) (hl : l < k.vs.length) (one : Bool) :
    SpotLaid f ⟨s, 1 + l, 0, one⟩ := by
  unfold SpotLaid
  refine ⟨MaskedSum.entry "PSC round" ((k.vs[l]).d - 1) 1 0, entry_at f h2 s hs (1 + l) _ ?_, rfl,
    Nat.zero_lt_one⟩
  rw [entries_call f s k hk]
  unfold MaskedSum.entries
  rw [at_succ _ _ _ l (by rw [List.length_map]; exact hl), List.getElem?_map,
    List.getElem?_eq_getElem hl]
  rfl

/-- The one round of a stage that sends nothing. -/
theorem draw_laid (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f)
    (hk : s.call f = none) (j : Nat) (hj : j < s.draws f) (one : Bool) :
    SpotLaid f ⟨s, 0, j, one⟩ := by
  unfold SpotLaid
  refine ⟨drawEntry s.name (s.draws f), entry_at f h2 s hs 0 _ ?_, rfl, hj⟩
  rw [entries_none f s hk, List.getElem?_cons_zero]

/-! ## 3 The first mark's spots -/

theorem spotsAt_laid (f : LFace) (h2 : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) (p : Spot)
    (hp : p ∈ spotsAt f s) : SpotLaid f p := by
  have hV : ∀ q ∈ (List.range (((s.call f).map (·.vs.length)).getD 0)).map
      (fun l => (⟨s, 1 + l, 0, false⟩ : Spot)), SpotLaid f q := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
    have hl' := List.mem_range.1 hl
    cases hk : s.call f with
    | none =>
      rw [hk] at hl'
      exact absurd hl' (Nat.not_lt_zero l)
    | some k =>
      rw [hk] at hl'
      exact var_laid f h2 s hs k hk l hl' false
  have hEV : ∀ k, s.call f = some k → ∀ q ∈ ([⟨s, 0, 0, false⟩] : List Spot) ++
      (List.range (((s.call f).map (·.vs.length)).getD 0)).map
        (fun l => (⟨s, 1 + l, 0, false⟩ : Spot)), SpotLaid f q := by
    intro k hk q hq
    rcases List.mem_append.1 hq with h | h
    · obtain rfl := List.mem_singleton.1 h
      exact eps_laid f h2 s hs k hk false
    · exact hV q h
  have hE : ∀ k, s.call f = some k → ∀ q ∈ ([⟨s, 0, 0, false⟩] : List Spot), SpotLaid f q := by
    intro k hk q hq
    obtain rfl := List.mem_singleton.1 hq
    exact eps_laid f h2 s hs k hk false
  have hL : s.call f = none → 0 < s.draws f →
      ∀ q ∈ ([⟨s, 0, 0, true⟩] : List Spot), SpotLaid f q := by
    intro hk hd q hq
    obtain rfl := List.mem_singleton.1 hq
    exact draw_laid f h2 s hs hk 0 hd true
  cases s with
  | shift => exact absurd (show p ∈ ([] : List Spot) from hp) List.not_mem_nil
  | alpha => exact absurd (show p ∈ ([] : List Spot) from hp) List.not_mem_nil
  | zero => exact absurd (show p ∈ ([] : List Spot) from hp) List.not_mem_nil
  | tie n =>
    cases n with
    | zero => exact absurd (show p ∈ ([] : List Spot) from hp) List.not_mem_nil
    | succ n => exact hE _ rfl p hp
  | split i => exact hE _ rfl p hp
  | join =>
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1
      (show p ∈ (List.range f.mu).map (fun k => (⟨.join, 0, k, true⟩ : Spot)) from hp)
    exact draw_laid f h2 .join hs rfl k (List.mem_range.1 hk) true
  | key i m => exact hEV _ rfl p hp
  | keyLine i m => exact hL rfl Nat.zero_lt_one p hp
  | tab l => exact hEV _ rfl p hp
  | tabLine l => exact hL rfl Nat.zero_lt_one p hp
  | leaves => exact hEV _ rfl p hp
  | bits => exact hV p hp

/-- CONDITIONAL on two planes at least: every spot of the first mark is laid. -/
theorem spot_laid (f : LFace) (h2 : 2 ≤ f.planes) : ∀ p ∈ spots f, SpotLaid f p := by
  intro p hp
  obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp
  exact spotsAt_laid f h2 s hs p hps

/-! ## 4 Stages that stand in the row -/

theorem key_in (f : LFace) (x : Nat × Nat) (hx : x ∈ f.parts.zipIdx) (m : Nat) (hm : m < x.1) :
    Stage.key x.2 m ∈ stages f ∧ Stage.keyLine x.2 m ∈ stages f := by
  have h : ∀ s ∈ [Stage.key x.2 m, Stage.keyLine x.2 m], s ∈ stages f := by
    intro s hs
    unfold stages
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    exact List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, hs⟩⟩
  exact ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem leaves_in (f : LFace) : Stage.leaves ∈ stages f := by
  unfold stages
  exact List.mem_append_right _ List.mem_cons_self

theorem bits_in (f : LFace) : Stage.bits ∈ stages f := by
  unfold stages
  exact List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem alpha_in (f : LFace) : Stage.alpha ∈ stages f := by
  unfold stages
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))))))

theorem shift_in (f : LFace) (hs : f.shifted = true) : Stage.shift ∈ stages f := by
  unfold stages
  rw [if_pos hs]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ List.mem_cons_self))))))

/-! ## 5 The second mark's spots; alpha; the shift -/

theorem level_vars (m : Nat) : (levelCall m).vs.length = m := by
  simp [levelCall, levelVars]

theorem leaf_vars (f : LFace) : (leafVars f #[]).length = f.mu + f.d := by
  simp [leafVars]

theorem bits_vars (n : Nat) : (bitsCall (List.replicate n OnBytes.zeroE)).vs.length = n := by
  simp [bitsCall]

/-- CONDITIONAL on that, and on each part having a bit at least: every spot of the second mark. -/
theorem spotOut_laid (f : LFace) (h2 : 2 ≤ f.planes) (h1 : ∀ v ∈ f.parts, 1 ≤ v) :
    ∀ p ∈ spotsOut f, SpotLaid f p := by
  intro p hp
  unfold spotsOut at hp
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_singleton] at hp
  rcases hp with ((⟨x, hx, (⟨l, hl, rfl⟩ | rfl)⟩ | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
  · have hl' := List.mem_range.1 hl
    exact var_laid f h2 _ (key_in f x hx (x.1 - 1) (by omega)).1 (levelCall (x.1 - 1)) rfl l
      (by rw [level_vars]; exact hl') true
  · have hx1 : 1 ≤ x.1 := h1 x.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx))
    exact draw_laid f h2 _ (key_in f x hx (x.1 - 1) (by omega)).2 rfl 0 Nat.zero_lt_one true
  · have hl' := List.mem_range.1 hl
    refine var_laid f h2 .leaves (leaves_in f) _ rfl l ?_ true
    show l < (leafVars f #[]).length
    rw [leaf_vars]
    exact hl'
  · have hl' := List.mem_range.1 hl
    refine var_laid f h2 .bits (bits_in f) _ rfl l ?_ true
    show l < (bitsCall (List.replicate (f.mu + f.d) OnBytes.zeroE)).vs.length
    rw [bits_vars]
    exact hl'

/-- Alpha's round. -/
theorem alpha_laid (f : LFace) (h2 : 2 ≤ f.planes) :
    (entriesV f)[firstRound f .alpha]? = some (drawEntry "LKP" 1) := by
  have e : Stage.entries f .alpha = [drawEntry "LKP" 1] := rfl
  exact entry_at f h2 .alpha (alpha_in f) 0 (drawEntry "LKP" 1)
    (by rw [e, List.getElem?_cons_zero])

/-- The shift's round, where the face has a shift. -/
theorem shift_laid (f : LFace) (h2 : 2 ≤ f.planes) (hs : f.shifted = true) :
    (entriesV f)[firstRound f .shift]? = some (drawEntry "LKP shift" 1) := by
  have e : Stage.entries f .shift = [drawEntry "LKP shift" 1] := rfl
  exact entry_at f h2 .shift (shift_in f hs) 0 (drawEntry "LKP shift" 1)
    (by rw [e, List.getElem?_cons_zero])

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.at_zero
#print axioms ProofFile.Honest.K3.Good.at_succ
#print axioms ProofFile.Honest.K3.Good.entry_at
#print axioms ProofFile.Honest.K3.Good.entries_call
#print axioms ProofFile.Honest.K3.Good.entries_none
#print axioms ProofFile.Honest.K3.Good.eps_laid
#print axioms ProofFile.Honest.K3.Good.var_laid
#print axioms ProofFile.Honest.K3.Good.draw_laid
#print axioms ProofFile.Honest.K3.Good.spotsAt_laid
#print axioms ProofFile.Honest.K3.Good.spot_laid
#print axioms ProofFile.Honest.K3.Good.key_in
#print axioms ProofFile.Honest.K3.Good.leaves_in
#print axioms ProofFile.Honest.K3.Good.bits_in
#print axioms ProofFile.Honest.K3.Good.alpha_in
#print axioms ProofFile.Honest.K3.Good.shift_in
#print axioms ProofFile.Honest.K3.Good.level_vars
#print axioms ProofFile.Honest.K3.Good.leaf_vars
#print axioms ProofFile.Honest.K3.Good.bits_vars
#print axioms ProofFile.Honest.K3.Good.spotOut_laid
#print axioms ProofFile.Honest.K3.Good.alpha_laid
#print axioms ProofFile.Honest.K3.Good.shift_laid
