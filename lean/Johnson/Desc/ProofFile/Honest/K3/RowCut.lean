-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowCut.lean: the lookup's row of parts (Honest/K3/Row.lean) is cut
as the book's maker cuts the verifier's rounds (`cutOfNames`, Honest/BookOf.lean), at every face
with two planes at least. Theorems, and one definition; general in the lookup's numbers.

Terms. Honest/K3/GLOSSARY.md ("cut", "book, coins", "row", "stage").

What is shown.
  `Stage.names`: the names of a stage's rounds.
  `names_call`: the names of a masked sumcheck's rounds.
  `unit_call`, `unit_open`, `unit_of_stage`: a stage's names, whatever stands behind them, are one
    unit of the maker's reading; for the leaves' sumcheck, which has no ends: where "ZERO" stands
    behind them.
  `units_closed`, `units_tail`: a list of stages is read stage by stage.
  `cut_stages`: the cut of the names of `entriesV f` is the stages' numbers of rounds.
  `cut_lookRow`: and so the parts' numbers of moves.
  On the way, among others: `front_closed`, whose statement writes the front of `stages`
    (Honest/K3/Stages.lean) out once more; it is tied to `stages` inside the proof of `cut_stages`
    alone.

Hypotheses that remain.
  `h`: (in `cut_stages`, `cut_lookRow`) the face has two planes at least.
  `he`: (in `unit_call`, `unit_open`) the call has ends, or has none. `hs`, `hp`: (in
    `unit_of_stage`, `units_closed`, `units_tail`) the stage, or every stage of the list, is not the
    leaves'.
  The helpers on lists and names have small hypotheses of their own (a length; a list that is not
    empty; a name that is not "PSC round").

Imported. Honest/BookOf.lean.

Limits. Names and numbers alone. The maker's cut is shown here at the list of the verifier's text
`entriesV`, not at the rounds that a description's member states.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowLaw
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part (MaskedSum.entries)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (entriesV noVar leafVars bitsCall drawEntry)
open VerifiableInference.Desc.First.ProdV (levelEnds)

variable {V W : Type}

/-- The names of a stage's rounds. -/
def Stage.names (f : LFace) (s : Stage) : List String := (Stage.entries f s).map (·.name)

/-! ## Lists -/

theorem map_const_replicate {α β : Type} (l : List α) (c : β) :
    l.map (fun _ => c) = List.replicate l.length c := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, ih, List.length_cons, List.replicate_succ]

theorem takeWhile_replicate_append (n : Nat) (a : String) (l : List String) :
    (List.replicate n a ++ l).takeWhile (· == a) = List.replicate n a ++ l.takeWhile (· == a) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem drop_replicate_add {α : Type} (n j : Nat) (a : α) (l : List α) :
    (List.replicate n a ++ l).drop (n + j) = l.drop j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, show n + 1 + j = (n + j) + 1 by omega,
      List.drop_succ_cons, ih]

theorem drop_append_len {α : Type} (l₁ l₂ : List α) (n : Nat) (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by
  subst h
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp

/-! ## The maker's reading -/

theorem unitsOf_nil (k : Nat) : unitsOf k [] = [] := by cases k <;> rfl

theorem unitsOf_succ_of_ne (k : Nat) (ns : List String) (h : ns ≠ []) :
    unitsOf (k + 1) ns = unitLen ns :: unitsOf k (ns.drop (unitLen ns)) := by
  cases ns with
  | nil => exact absurd rfl h
  | cons a l => rfl

theorem cutOfNames_K3 (ns : List String) : cutOfNames .K3 ns = unitsOf ns.length ns := by
  unfold cutOfNames
  cases unitsOf ns.length ns with
  | nil => rfl
  | cons a rest => rfl

theorem unitLen_eps (l : List String) : unitLen ("PSC epsilon" :: l) = 1 + sumTail l := by
  simp [unitLen]

theorem headRun_rounds (n : Nat) (a : String) (X : List String) (h : (a == "PSC round") = false) :
    headRun "PSC round" (List.replicate n "PSC round" ++ a :: X) = n := by
  unfold headRun
  rw [takeWhile_replicate_append, List.takeWhile_cons, h]
  simp

theorem sumTail_closed (n : Nat) (X : List String) :
    sumTail (List.replicate n "PSC round" ++ "PSC Y" :: "PSC values" :: X) = n + 2 := by
  have ha := headRun_rounds n "PSC Y" ("PSC values" :: X) (by decide)
  have d0 := drop_replicate_add n 0 "PSC round" ("PSC Y" :: "PSC values" :: X)
  have d1 := drop_replicate_add n 1 "PSC round" ("PSC Y" :: "PSC values" :: X)
  rw [Nat.add_zero, List.drop_zero] at d0
  have hb : headOne "PSC Y" ("PSC Y" :: "PSC values" :: X) = 1 := by simp [headOne]
  unfold sumTail
  simp only [ha, d0, hb, d1]
  simp [headOne]

theorem sumTail_open (n : Nat) (X : List String) :
    sumTail (List.replicate n "PSC round" ++ "ZERO" :: X) = n := by
  have ha := headRun_rounds n "ZERO" X (by decide)
  have d0 := drop_replicate_add n 0 "PSC round" ("ZERO" :: X)
  rw [Nat.add_zero, List.drop_zero] at d0
  have hb : headOne "PSC Y" ("ZERO" :: X) = 0 := by simp [headOne]
  unfold sumTail
  simp only [ha, d0, hb, Nat.add_zero]
  simp [headOne]

/-! ## A stage is one unit -/

/-- The names of a masked sumcheck's rounds. -/
theorem names_call (k : Call) :
    (MaskedSum.entries k).map (·.name) =
      "PSC epsilon" :: (List.replicate k.vs.length "PSC round" ++
        (match k.ends with
         | none => []
         | some _ => ["PSC Y", "PSC values"])) := by
  have hv : (k.vs.map fun v => VerifiableInference.Desc.Part.MaskedSum.entry "PSC round" (v.d - 1) 1
    0).map
      (·.name) = List.replicate k.vs.length "PSC round" := by
    rw [List.map_map]
    exact map_const_replicate k.vs "PSC round"
  unfold MaskedSum.entries
  rw [List.map_append, List.map_append, hv]
  cases k.ends <;> rfl

/-- A masked sumcheck with ends is one unit, whatever stands behind it. -/
theorem unit_call (k : Call) (e : Ends) (he : k.ends = some e) (X : List String) :
    unitLen ((MaskedSum.entries k).map (·.name) ++ X) =
      VerifiableInference.Desc.K3.roundsOf k := by
  rw [names_call, he]
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [unitLen_eps, sumTail_closed]
  simp [VerifiableInference.Desc.K3.roundsOf, he]
  omega

/-- One without ends is one unit where "ZERO" stands behind it. -/
theorem unit_open (k : Call) (he : k.ends = none) (X : List String) :
    unitLen ((MaskedSum.entries k).map (·.name) ++ "ZERO" :: X) =
      VerifiableInference.Desc.K3.roundsOf k := by
  rw [names_call, he]
  simp only [List.cons_append, List.append_nil]
  rw [unitLen_eps, sumTail_open]
  simp [VerifiableInference.Desc.K3.roundsOf, he]
  omega

/-- **Every stage but the leaves' is one unit, whatever stands behind it.** -/
theorem unit_of_stage (f : LFace) (s : Stage) (hs : s ≠ .leaves) (X : List String) :
    unitLen (Stage.names f s ++ X) = Stage.rounds f s := by
  cases s with
  | shift => show unitLen ("LKP shift" :: X) = 1; simp [unitLen]
  | alpha => show unitLen ("LKP" :: X) = 1; simp [unitLen]
  | tie n =>
    cases n with
    | zero => exact unit_call (noVar 3 3) ⟨3, 3⟩ rfl X
    | succ n => exact unit_call (noVar 3 2) ⟨3, 2⟩ rfl X
  | split i => exact unit_call (noVar 2 2) ⟨2, 2⟩ rfl X
  | join => show unitLen ("JOIN" :: X) = 1; simp [unitLen]
  | key i m => exact unit_call (levelCall m) levelEnds rfl X
  | keyLine i m => show unitLen ("LINE" :: X) = 1; simp [unitLen]
  | tab l => exact unit_call (levelCall (f.mu + l)) levelEnds rfl X
  | tabLine l => show unitLen ("LINE" :: X) = 1; simp [unitLen]
  | leaves => exact absurd rfl hs
  | zero => show unitLen ("ZERO" :: X) = 1; simp [unitLen]
  | bits => exact unit_call (bitsCall (List.replicate (f.mu + f.d) zeroE)) ⟨2, 1⟩ rfl X

theorem names_length (f : LFace) (s : Stage) : (Stage.names f s).length = Stage.rounds f s := by
  unfold Stage.names
  rw [List.length_map, entries_length]

theorem rounds_pos (f : LFace) (s : Stage) : 1 ≤ Stage.rounds f s := by
  unfold Stage.rounds
  cases s.call f with
  | none => exact Nat.le_refl 1
  | some k =>
    show 1 ≤ k.vs.length + (if k.ends.isSome then 3 else 1)
    split <;> omega

theorem names_ne_nil (f : LFace) (s : Stage) (X : List String) : Stage.names f s ++ X ≠ [] := by
  intro h
  have h1 := congrArg List.length h
  rw [List.length_append, names_length] at h1
  have := rounds_pos f s
  simp at h1
  omega

/-! ## A list of stages -/

/-- Stages of which none is the leaves' are read one by one. Here k is the fuel that is left. -/
theorem units_closed (f : LFace) (ss : List Stage) (hs : ∀ s ∈ ss, s ≠ .leaves) (X : List String)
    (k : Nat) :
    unitsOf (ss.length + k) (ss.flatMap (Stage.names f) ++ X) =
      ss.map (Stage.rounds f) ++ unitsOf k X := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rw [List.flatMap_cons, List.append_assoc, List.length_cons,
      show ss.length + 1 + k = (ss.length + k) + 1 by omega,
      unitsOf_succ_of_ne _ _ (names_ne_nil f s _),
      unit_of_stage f s (hs s (List.mem_cons_self ..)),
      drop_append_len _ _ _ (names_length f s),
      ih (fun t ht => hs t (List.mem_cons_of_mem _ ht))]
    rfl

/-- The same with the lookup's last three stages behind them. -/
theorem units_tail (f : LFace) (pre : List Stage) (hp : ∀ s ∈ pre, s ≠ .leaves) (k : Nat) :
    unitsOf ((pre ++ [Stage.leaves, Stage.zero, Stage.bits]).length + k)
        ((pre ++ [Stage.leaves, Stage.zero, Stage.bits]).flatMap (Stage.names f)) =
      (pre ++ [Stage.leaves, Stage.zero, Stage.bits]).map (Stage.rounds f) := by
  have e1 : ([Stage.leaves, Stage.zero, Stage.bits] : List Stage).flatMap (Stage.names f) =
      Stage.names f .leaves ++ (([Stage.zero, Stage.bits] : List Stage).flatMap (Stage.names f) ++
        [])
      := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hz : (([Stage.zero, Stage.bits] : List Stage).flatMap (Stage.names f) ++ []) =
      "ZERO" :: Stage.names f .bits := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  have hu : unitLen (Stage.names f .leaves ++
      (([Stage.zero, Stage.bits] : List Stage).flatMap (Stage.names f) ++ [])) =
      Stage.rounds f .leaves := by
    rw [hz]
    exact unit_open { lead := 0, vs := leafVars f #[], ends := none } rfl _
  have h2 : ∀ s ∈ ([Stage.zero, Stage.bits] : List Stage), s ≠ .leaves := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact fun h => Stage.noConfusion h
  rw [List.flatMap_append, List.length_append, List.map_append, Nat.add_assoc,
    units_closed f pre hp, e1,
    show ([Stage.leaves, Stage.zero, Stage.bits] : List Stage).length + k =
      (([Stage.zero, Stage.bits] : List Stage).length + k) + 1 from by simp; omega,
    unitsOf_succ_of_ne _ _ (names_ne_nil f _ _), hu,
    drop_append_len _ _ _ (names_length f .leaves), units_closed f _ h2, unitsOf_nil]
  rfl

theorem length_le_names (f : LFace) (ss : List Stage) :
    ss.length ≤ (ss.flatMap (Stage.names f)).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, names_length]
    have := rounds_pos f s
    omega

/-- In front of the last three stages none is the leaves'. -/
theorem front_closed (f : LFace) : ∀ s ∈
    (if f.shifted then [Stage.shift] else []) ++ [Stage.alpha] ++
      (List.range (f.planes - 1)).map Stage.tie ++
      (List.range (f.parts.length - 1)).map Stage.split ++
      [Stage.join] ++
      f.parts.zipIdx.flatMap (fun x =>
        (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]) ++
      (List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l]), s ≠ .leaves := by
  intro s hs he
  subst he
  cases hsh : f.shifted <;> simp [hsh] at hs

/-- **The row is cut as the book's maker cuts the verifier's rounds.** -/
theorem cut_stages (f : LFace) (h : 2 ≤ f.planes) :
    cutOfNames .K3 ((entriesV f).map (·.name)) = (stages f).map (Stage.rounds f) := by
  rw [cutOfNames_K3, ← entries_stages f h, List.map_flatMap]
  show unitsOf ((stages f).flatMap (Stage.names f)).length ((stages f).flatMap (Stage.names f)) = _
  obtain ⟨k, hk⟩ : ∃ k, ((stages f).flatMap (Stage.names f)).length = (stages f).length + k :=
    ⟨_, (Nat.add_sub_cancel' (length_le_names f _)).symm⟩
  rw [hk]
  exact units_tail f _ (front_closed f) k

/-- The parts' numbers of moves are that cut. -/
theorem cut_lookRow (R : Reads) (J : LookJobs W) (a : At) (h : 2 ≤ a.face.planes) :
    (lookRow (V := V) R J a).map (·.moves.length) =
      cutOfNames .K3 ((entriesV a.face).map (·.name)) := by
  rw [lookRow_moves, cut_stages a.face h]

#print axioms ProofFile.Honest.K3.names_call
#print axioms ProofFile.Honest.K3.unit_call
#print axioms ProofFile.Honest.K3.unit_open
#print axioms ProofFile.Honest.K3.unit_of_stage
#print axioms ProofFile.Honest.K3.units_closed
#print axioms ProofFile.Honest.K3.units_tail
#print axioms ProofFile.Honest.K3.front_closed
#print axioms ProofFile.Honest.K3.cut_stages
#print axioms ProofFile.Honest.K3.cut_lookRow
#print axioms ProofFile.Honest.K3.map_const_replicate
#print axioms ProofFile.Honest.K3.takeWhile_replicate_append
#print axioms ProofFile.Honest.K3.drop_replicate_add
#print axioms ProofFile.Honest.K3.drop_append_len
#print axioms ProofFile.Honest.K3.unitsOf_nil
#print axioms ProofFile.Honest.K3.unitsOf_succ_of_ne
#print axioms ProofFile.Honest.K3.cutOfNames_K3
#print axioms ProofFile.Honest.K3.unitLen_eps
#print axioms ProofFile.Honest.K3.headRun_rounds
#print axioms ProofFile.Honest.K3.sumTail_closed
#print axioms ProofFile.Honest.K3.sumTail_open
#print axioms ProofFile.Honest.K3.names_length
#print axioms ProofFile.Honest.K3.rounds_pos
#print axioms ProofFile.Honest.K3.names_ne_nil
#print axioms ProofFile.Honest.K3.length_le_names

end ProofFile.Honest.K3
