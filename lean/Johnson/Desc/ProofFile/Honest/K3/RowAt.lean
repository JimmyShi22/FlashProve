-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowAt.lean: where a stage stands in the lookup's row
(Honest/K3/Stages.lean, Honest/K3/Row.lean), and that the row with the forms beside it passes the
frame's test on a side. Theorems, and one helper definition; general in the lookup's numbers, but
that `entries_at` and `lookPairs_fits` ask two planes at least.

Terms. Honest/K3/GLOSSARY.md ("row", "stage", "slot").

What is shown.
  `stages_nodup`: no stage stands twice in a lookup's row.
  `indexOf_getElem`: so the stage at number i has `indexOf` i.
  `firstRound_getElem`, `firstSlot_getElem`: and its first round and first slot are the sums over
    the i stages in front.
  `entries_at`: the verifier's list of rounds, from `firstRound f s` on, begins with the stage's
    own.
  `simOf_addr`, `lookPairs_fits`: each form names its part's address; `Side.fits` holds at every
    sub-protocol that stands at the place and has as many rounds as `entriesV`.

Hypotheses that remain.
  `h`: (in `entries_at`, `lookPairs_fits`) the face has two planes at least.
  `hs`: (in `entries_at`) the stage is one of the row's. `hi`: (in `indexOf_getElem`,
    `firstRound_getElem`, `firstSlot_getElem`) i lies below the number of stages.
  `hp`, `hr`, `ho`: (in `lookPairs_fits`) the sub-protocol stands at the place; it has as many
    rounds as `entriesV`; it states a list of oracle messages for each round.
  The helpers on lists have hypotheses of their own: no member twice, injective makers, a member, a
    range, equal lengths.

Limits. Numbers, names and addresses alone: nothing on any value that is sent. `lookPairs_fits`
takes the sub-protocol's place and two lengths as hypotheses; that a description's member has them
is not shown in this file. Shown in part: Honest/K3/Law/MemberAtSite.lean (`memberAtSite`): the
member at a lookup's place has the rounds and the oracle messages of the lot's sub-protocol there,
where the description returns. That theorem does not speak of the two lengths.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K3 (entriesV)

variable {V W Pb V₁ W₁ X₁ S Cl : Type}

/-! ## No stage stands twice -/

theorem nodup_app {l₁ l₂ : List Stage} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a, a ∈ l₁ → a ∈ l₂ → False) : (l₁ ++ l₂).Nodup :=
  List.Nodup.append h₁ h₂ (fun a ha hb => hd a ha hb)

theorem mem_pairs (F G : Nat → Stage) (v : Nat) (a : Stage) :
    a ∈ (List.range v).flatMap (fun m => [F m, G m]) ↔ ∃ m, m < v ∧ (a = F m ∨ a = G m) := by
  simp [List.mem_flatMap]

theorem pairs_nodup (F G : Nat → Stage) (hF : ∀ m n, F m = F n → m = n)
    (hG : ∀ m n, G m = G n → m = n) (hFG : ∀ m n, F m ≠ G n) (v : Nat) :
    ((List.range v).flatMap fun m => [F m, G m]).Nodup := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [List.range_succ, List.flatMap_append]
    refine nodup_app ih ?_ ?_
    · simp [hFG]
    · intro a ha hb
      rw [mem_pairs] at ha
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hb
      obtain ⟨m, hm, h1⟩ := ha
      rcases h1 with rfl | rfl <;> rcases hb with hb | hb
      · have := hF _ _ hb; omega
      · exact hFG _ _ hb
      · exact hFG _ _ hb.symm
      · have := hG _ _ hb; omega

/-- The key side's stages, of the parts numbered from n on. -/
def keyStages (l : List Nat) (n : Nat) : List Stage :=
  (l.zipIdx n).flatMap fun x =>
    (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]

theorem mem_keyStages (l : List Nat) (n : Nat) (a : Stage) (h : a ∈ keyStages l n) :
    ∃ i m, n ≤ i ∧ (a = .key i m ∨ a = .keyLine i m) := by
  induction l generalizing n with
  | nil => simp [keyStages] at h
  | cons v l ih =>
    unfold keyStages at h
    rw [List.zipIdx_cons, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨m, -, hm⟩ := (mem_pairs _ _ _ _).1 h
      exact ⟨n, m, Nat.le_refl n, hm⟩
    · obtain ⟨i, m, hi, hm⟩ := ih (n + 1) h
      exact ⟨i, m, by omega, hm⟩

theorem keyStages_nodup (l : List Nat) (n : Nat) : (keyStages l n).Nodup := by
  induction l generalizing n with
  | nil => simp [keyStages]
  | cons v l ih =>
    unfold keyStages
    rw [List.zipIdx_cons, List.flatMap_cons]
    refine nodup_app
      (pairs_nodup (Stage.key n) (Stage.keyLine n) (fun _ _ h => (Stage.key.inj h).2)
        (fun _ _ h => (Stage.keyLine.inj h).2) (fun _ _ h => Stage.noConfusion h) v)
      (ih (n + 1)) ?_
    intro a ha hb
    obtain ⟨m, -, hm⟩ := (mem_pairs _ _ _ _).1 ha
    obtain ⟨i, m', hi, hm'⟩ := mem_keyStages l (n + 1) a hb
    rcases hm with rfl | rfl <;> rcases hm' with h | h
    · have := (Stage.key.inj h).1; omega
    · exact Stage.noConfusion h
    · exact Stage.noConfusion h
    · have := (Stage.keyLine.inj h).1; omega

/-- **No stage stands twice in a lookup's row.** -/
theorem stages_nodup (f : LFace) : (stages f).Nodup := by
  have hA : (if f.shifted then [Stage.shift] else []).Nodup := by split <;> simp
  have hT : ((List.range (f.planes - 1)).map Stage.tie).Nodup :=
    List.nodup_range.map (fun _ _ h => Stage.tie.inj h)
  have hS : ((List.range (f.parts.length - 1)).map Stage.split).Nodup :=
    List.nodup_range.map (fun _ _ h => Stage.split.inj h)
  have hK : (keyStages f.parts 0).Nodup := keyStages_nodup f.parts 0
  have hB : ((List.range f.d).flatMap fun l => [Stage.tab l, Stage.tabLine l]).Nodup :=
    pairs_nodup Stage.tab Stage.tabLine (fun _ _ h => Stage.tab.inj h)
      (fun _ _ h => Stage.tabLine.inj h) (fun _ _ h => Stage.noConfusion h) f.d
  show ((if f.shifted then [Stage.shift] else []) ++ [Stage.alpha] ++
      (List.range (f.planes - 1)).map Stage.tie ++
      (List.range (f.parts.length - 1)).map Stage.split ++ [Stage.join] ++ keyStages f.parts 0 ++
      (List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l]) ++
      [Stage.leaves, Stage.zero, Stage.bits]).Nodup
  refine nodup_app (nodup_app (nodup_app (nodup_app (nodup_app (nodup_app (nodup_app hA
    (by simp) ?_) hT ?_) hS ?_) (by simp) ?_) hK ?_) hB ?_) (by simp) ?_
  · intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    cases hsh : f.shifted <;> simp [hsh] at ha
  · intro a ha hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    cases hsh : f.shifted <;> simp [hsh] at ha
  · intro a ha hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    cases hsh : f.shifted <;> simp [hsh] at ha
  · intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    cases hsh : f.shifted <;> simp [hsh] at ha
  · intro a ha hb
    obtain ⟨i, m, -, h⟩ := mem_keyStages _ _ _ hb
    rcases h with rfl | rfl <;> cases hsh : f.shifted <;> simp [hsh] at ha
  · intro a ha hb
    obtain ⟨l, -, h⟩ := (mem_pairs _ _ _ _).1 hb
    have hk : ∀ x, x ∈ keyStages f.parts 0 → x ≠ a := by
      intro x hx hxa
      obtain ⟨i, m, -, h'⟩ := mem_keyStages _ _ _ hx
      subst hxa
      rcases h with h | h <;> rcases h' with h' | h' <;> exact Stage.noConfusion (h.symm.trans h')
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · rcases h with rfl | rfl <;> cases hsh : f.shifted <;> simp [hsh] at ha
    · exact hk a ha rfl
  · intro a ha hb
    have hk : ∀ x, x ∈ keyStages f.parts 0 → x ≠ a := by
      intro x hx hxa
      obtain ⟨i, m, -, h'⟩ := mem_keyStages _ _ _ hx
      subst hxa
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with h | h | h <;> rcases h' with h' | h' <;>
        exact Stage.noConfusion (h.symm.trans h')
    rw [List.mem_append, List.mem_append] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases ha with (ha | ha) | ha
    · rcases hb with rfl | rfl | rfl <;> cases hsh : f.shifted <;> simp [hsh] at ha
    · exact hk a ha rfl
    · obtain ⟨l, -, h⟩ := (mem_pairs _ _ _ _).1 ha
      rcases hb with rfl | rfl | rfl <;> rcases h with h | h <;> exact Stage.noConfusion h

/-! ## A stage's number -/

theorem idxOf_getElem_of_nodup {α : Type} [DecidableEq α] (l : List α) (h : l.Nodup) (i : Nat)
    (hi : i < l.length) : l.idxOf l[i] = i := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hl : i < l.length := by simpa using hi
      have hne : a ≠ l[i] := fun e => (List.nodup_cons.1 h).1 (e ▸ List.getElem_mem hl)
      simp only [List.getElem_cons_succ]
      rw [List.idxOf_cons_ne _ hne, ih (List.nodup_cons.1 h).2 i hl]

/-- The stage at number i of the row has that number. -/
theorem indexOf_getElem (f : LFace) (i : Nat) (hi : i < (stages f).length) :
    indexOf f (stages f)[i] = i :=
  idxOf_getElem_of_nodup _ (stages_nodup f) i hi

theorem firstRound_getElem (f : LFace) (i : Nat) (hi : i < (stages f).length) :
    firstRound f (stages f)[i] = (((stages f).take i).map (Stage.rounds f)).sum := by
  unfold firstRound
  rw [indexOf_getElem]

theorem firstSlot_getElem (f : LFace) (i : Nat) (hi : i < (stages f).length) :
    firstSlot f (stages f)[i] = (((stages f).take i).map (Stage.slots f)).sum := by
  unfold firstSlot
  rw [indexOf_getElem]

/-! ## The rounds from a stage's first on -/

theorem drop_length_add {β : Type} (l₁ l₂ : List β) (k : Nat) :
    (l₁ ++ l₂).drop (l₁.length + k) = l₂.drop k := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    rw [List.cons_append, List.length_cons, show l.length + 1 + k = (l.length + k) + 1 by omega,
      List.drop_succ_cons, ih]

theorem flatMap_at {α β : Type} [DecidableEq α] (g : α → List β) (l : List α) (s : α)
    (hs : s ∈ l) :
    ((l.flatMap g).drop (((l.take (l.idxOf s)).map fun x => (g x).length).sum)).take (g s).length =
      g s := by
  induction l with
  | nil => simp at hs
  | cons a l ih =>
    by_cases e : a = s
    · subst e
      simp
    · have hs' : s ∈ l := by
        rcases List.mem_cons.1 hs with h | h
        · exact absurd h.symm e
        · exact h
      rw [List.idxOf_cons_ne _ e, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.flatMap_cons, drop_length_add]
      exact ih hs'

/-- **From a stage's first round on, the verifier's list begins with the stage's own rounds.** At a
face with two planes at least. -/
theorem entries_at (f : LFace) (h : 2 ≤ f.planes) (s : Stage) (hs : s ∈ stages f) :
    ((entriesV f).drop (firstRound f s)).take (Stage.rounds f s) = Stage.entries f s := by
  have := flatMap_at (Stage.entries f) (stages f) s hs
  simp only [entries_length] at this
  rw [entries_stages f h] at this
  exact this

/-! ## The frame's test on a side -/

/-- A form names its part's address. -/
theorem simOf_addr (a : At) (s : Stage) (i : Nat) : (simOf (Pb := Pb) a s i).addr = ⟨a.place, i⟩ :=
    by
  unfold simOf
  cases s.call a.face <;> rfl

theorem addrs_fit {α : Type} (a : At) (ss : List Stage) (P : List α) (n : Nat) :
    ((P.zip ((ss.zipIdx n).map fun x => simOf (Pb := Pb) a x.1 x.2)).zipIdx n).all
      (fun s => s.1.2.addr == ⟨a.place, s.2⟩) = true := by
  induction ss generalizing P n with
  | nil => simp
  | cons s ss ih =>
    cases P with
    | nil => simp
    | cons p P =>
      rw [List.zipIdx_cons, List.map_cons, List.zip_cons_cons, List.zipIdx_cons, List.all_cons, ih]
      simp [simOf_addr]

theorem map_fst_zip_eq {α β : Type} (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length) :
    (l₁.zip l₂).map (·.1) = l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ => simp [ih l₂ (by simpa using h)]

/-- **The row with the forms beside it passes the frame's test**, at a face with two planes at
least, at every sub-protocol that stands at the place, has as many rounds as the verifier's text
hears, and states a list of oracle messages for each. -/
theorem lookPairs_fits (b : Block S Cl) (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At)
    (h : 2 ≤ a.face.planes) (hp : b.place = a.place)
    (hr : b.rounds.length = (entriesV a.face).length) (ho : b.oracles.length = b.rounds.length) :
    ({ block := b, row := lookPairs R J wit a } : Side S Cl V₁ W₁ X₁ Pb).fits = true := by
  have hl : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts.length =
      (lookSims (Pb := Pb) a).length := by
    rw [lookSims_length, ← List.length_map (f := fun p : Part V₁ W₁ X₁ => p.moves.length),
      proverSideOfLookupInChainAtOneOwner_moves, List.length_map]
  have h1 : (lookPairs (V₁ := V₁) (X₁ := X₁) (Pb := Pb) R J wit a).zipIdx.all
      (fun s => s.1.2.addr == ⟨b.place, s.2⟩) = true := by
    rw [hp]
    exact addrs_fit a (stages a.face) _ 0
  have h2 : (Side.half ({ block := b, row := lookPairs R J wit a } : Side S Cl V₁ W₁ X₁ Pb)).rounds
    =
      b.rounds.length := by
    unfold Side.half Placed.rounds
    simp only [lookPairs]
    rw [map_fst_zip_eq _ _ hl, foldl_add_eq_sum (fun p : Part V₁ W₁ X₁ => p.moves.length),
      proverSideOfLookupInChainAtOneOwner_moves, rounds_stages a.face h, hr, Nat.zero_add]
  unfold Side.fits
  simp only [h1, h2, ho, beq_self_eq_true, Bool.and_self]

#print axioms ProofFile.Honest.K3.stages_nodup
#print axioms ProofFile.Honest.K3.indexOf_getElem
#print axioms ProofFile.Honest.K3.firstRound_getElem
#print axioms ProofFile.Honest.K3.firstSlot_getElem
#print axioms ProofFile.Honest.K3.entries_at
#print axioms ProofFile.Honest.K3.simOf_addr
#print axioms ProofFile.Honest.K3.lookPairs_fits
#print axioms ProofFile.Honest.K3.nodup_app
#print axioms ProofFile.Honest.K3.mem_pairs
#print axioms ProofFile.Honest.K3.pairs_nodup
#print axioms ProofFile.Honest.K3.mem_keyStages
#print axioms ProofFile.Honest.K3.keyStages_nodup
#print axioms ProofFile.Honest.K3.idxOf_getElem_of_nodup
#print axioms ProofFile.Honest.K3.drop_length_add
#print axioms ProofFile.Honest.K3.flatMap_at
#print axioms ProofFile.Honest.K3.addrs_fit
#print axioms ProofFile.Honest.K3.map_fst_zip_eq

end ProofFile.Honest.K3
