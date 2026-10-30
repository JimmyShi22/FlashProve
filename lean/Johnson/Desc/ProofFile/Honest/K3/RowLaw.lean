-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowLaw.lean: the lookup's row of parts (Honest/K3/Row.lean) has the
verifier's rounds and the verifier's count of slots, at every face with two planes at least.
Theorems; general in the lookup's numbers.

Terms. Honest/K3/GLOSSARY.md ("row", "stage", "slot", "half").

What is shown.
  `two_le_planes_of_ok`: a face that passes the verifier's tests has two planes at least.
  `levelCall_eq`: a level's call has the shape at which the verifier makes a level's entries.
  `entries_stages`: the stages' rounds, as entries of the plan, are `entriesV f`.
  `entries_length`: a stage has as many entries as `Stage.rounds` says.
  `rounds_stages`: the stages' numbers of rounds add up to the length of `entriesV f`.
  `sumPart_moves`: the masked sumcheck's part has as many moves as its call has rounds.
  `partOf_moves`, `lookRow_length`, `lookRow_moves`, `proverSideOfLookupInChainAtOneOwner_moves`, `lookSims_length`: the row:
    one part for each stage; one move for each round; seated or not; one form for each part.
  `proverSideOfLookupAtOneOwner_rounds`: the half has as many rounds as `entriesV f` has entries.
  `slots_stages`: the stages' slots add up to `Face.slots`. On the way `ownSlots_eq`, which states
    what the library's `MaskedSum.ownSlots_eq` (Johnson/Desc/Part/MaskedSumSound.lean) states.

Hypotheses that remain.
  `h`: (in `entries_stages`, `rounds_stages`, `proverSideOfLookupAtOneOwner_rounds`, `slots_stages`) the face has two
    planes at least; (in `two_le_planes_of_ok`) the face passes the verifier's tests; (in the
    helpers `getD_map_length`, `sum_leaf_low`) every list has the length n; n ≤ d.

Limits. Numbers and shapes alone: nothing on any value that is sent, on what the verifier makes of
the rounds, or on the book. At one plane or none the four statements that bear the hypothesis on the
planes are false (Honest/K3/RowGuards.lean [not in this library] has a line for the first); there
the verifier's tests reject the face.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part (MaskedSum.entries)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.K3 (entriesV noVar leafVars bitsCall drawEntry)
open VerifiableInference.Desc.First.ProdV (runEntries levelEntries levelEnds)

variable {V W Pb V₁ W₁ X₁ X : Type}

/-! ## Lists -/

theorem flatMap_zipIdx_fst {α β : Type} (g : α → List β) (l : List α) (n : Nat) :
    (l.zipIdx n).flatMap (fun x => g x.1) = l.flatMap g := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx_cons, List.flatMap_cons, ih]

theorem getD_map_length {α β : Type} (o : Option α) (g : α → List β) (n : Nat)
    (h : ∀ e, (g e).length = n) : ((o.map g).getD []).length = if o.isSome then n else 0 := by
  cases o <;> simp [h]

theorem map_range_const {α : Type} (n : Nat) (c : α) :
    (List.range n).map (fun _ => c) = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, ih, List.replicate_succ']; rfl

/-! ## The face -/

theorem two_le_planes_of_ok (f : LFace) (h : f.ok = true) : 2 ≤ f.planes := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.2

/-! ## The rounds -/

/-- A level's call has the shape at which the verifier's text makes a level's entries. -/
theorem levelCall_eq (m : Nat) :
    levelCall m =
      { lead := 0, vs := List.replicate m (Var.point zeroE 3), ends := some levelEnds } := by
  have hv : VerifiableInference.Desc.First.ProdV.levelVars m #[] (List.range m) =
      List.replicate m (Var.point zeroE 3) := by
    unfold VerifiableInference.Desc.First.ProdV.levelVars
    have : (fun b : Nat => Var.point ((#[] : Array E).getD (m - 1 - b) zeroE) 3) =
        fun _ => Var.point zeroE 3 := by
      funext b
      simp
    rw [this]
    exact map_range_const m _
  unfold levelCall
  rw [hv]

theorem entries_level (m : Nat) :
    MaskedSum.entries (levelCall m) ++ [drawEntry "LINE" 1] = levelEntries m := by
  rw [levelCall_eq]
  rfl

theorem entries_ties (f : LFace) (n : Nat) :
    ((List.range (n + 1)).map Stage.tie).flatMap (Stage.entries f) =
      MaskedSum.entries (noVar 3 3) ++
        (List.range n).flatMap fun _ => MaskedSum.entries (noVar 3 2) := by
  rw [List.range_succ_eq_map, List.map_cons, List.flatMap_cons, List.map_map, List.flatMap_map]
  rfl

theorem entries_splits (f : LFace) (n : Nat) :
    ((List.range n).map Stage.split).flatMap (Stage.entries f) =
      (List.range n).flatMap fun _ => MaskedSum.entries (noVar 2 2) := by
  rw [List.flatMap_map]
  rfl

theorem entries_keys (f : LFace) (i v : Nat) :
    ((List.range v).flatMap fun m => [Stage.key i m, Stage.keyLine i m]).flatMap (Stage.entries f) =
      runEntries 0 v := by
  rw [List.flatMap_assoc]
  unfold runEntries
  congr 1
  funext m
  rw [Nat.zero_add]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact entries_level m

theorem entries_tabs (f : LFace) :
    ((List.range f.d).flatMap fun l => [Stage.tab l, Stage.tabLine l]).flatMap (Stage.entries f) =
      runEntries f.mu f.d := by
  rw [List.flatMap_assoc]
  unfold runEntries
  congr 1
  funext l
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact entries_level (f.mu + l)

/-- **The stages' rounds are the verifier's.** -/
theorem entries_stages (f : LFace) (h : 2 ≤ f.planes) :
    (stages f).flatMap (Stage.entries f) = entriesV f := by
  have hp : f.planes - 1 = (f.planes - 2) + 1 := by omega
  unfold stages entriesV
  simp only [List.flatMap_append]
  rw [hp, entries_ties, entries_splits, entries_tabs, List.flatMap_assoc]
  have hk : (f.parts.zipIdx.flatMap fun x =>
      ((List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]).flatMap
        (Stage.entries f)) = f.parts.flatMap fun v => runEntries 0 v := by
    simp only [entries_keys]
    exact flatMap_zipIdx_fst (fun v => runEntries 0 v) f.parts 0
  rw [hk]
  have ha : (if f.shifted = true then [Stage.shift] else []).flatMap (Stage.entries f) =
      if f.shifted = true then [drawEntry "LKP shift" 1] else [] := by
    split <;> rfl
  rw [ha]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

/-- A stage has as many entries as it has rounds. -/
theorem entries_length (f : LFace) (s : Stage) : (Stage.entries f s).length = Stage.rounds f s := by
  unfold Stage.entries Stage.rounds
  cases s.call f with
  | none => rfl
  | some k =>
    simp only [MaskedSum.entries, VerifiableInference.Desc.K3.roundsOf]
    cases k.ends <;> simp

/-- The stages' rounds add up to the verifier's. -/
theorem rounds_stages (f : LFace) (h : 2 ≤ f.planes) :
    ((stages f).map (Stage.rounds f)).sum = (entriesV f).length := by
  rw [← entries_stages f h, List.length_flatMap]
  simp only [entries_length]

/-! ## The row -/

/-- The masked sumcheck's part has as many moves as its call has rounds. -/
theorem sumPart_moves (name endName : String) (J : SumJob W X) :
    (sumPart (V := V) name endName J).moves.length =
      VerifiableInference.Desc.K3.roundsOf J.shape := by
  unfold sumPart VerifiableInference.Desc.K3.roundsOf
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  rw [getD_map_length _ _ 2 (fun _ => rfl)]
  split <;> omega

/-- A part has as many moves as its stage has rounds. -/
theorem partOf_moves (R : Reads) (J : LookJobs W) (a : At) (s : Stage) (i : Nat) :
    (partOf (V := V) R J a s i).moves.length = Stage.rounds a.face s := by
  unfold partOf Stage.rounds
  cases s.call a.face with
  | none => rfl
  | some k => exact sumPart_moves _ _ _

theorem lookRow_length (R : Reads) (J : LookJobs W) (a : At) :
    (lookRow (V := V) R J a).length = (stages a.face).length := by
  simp [lookRow]

theorem map_zipIdx_fst {α β : Type} (g : α → β) (l : List α) (n : Nat) :
    (l.zipIdx n).map (fun x => g x.1) = l.map g := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx_cons, ih]

theorem lookRow_moves (R : Reads) (J : LookJobs W) (a : At) :
    (lookRow (V := V) R J a).map (·.moves.length) = (stages a.face).map (Stage.rounds a.face) := by
  unfold lookRow
  rw [List.map_map]
  have : ((fun p : Part V W Unit => p.moves.length) ∘ fun x : Stage × Nat => partOf R J a x.1 x.2) =
      fun x => Stage.rounds a.face x.1 := by
    funext x
    exact partOf_moves R J a x.1 x.2
  rw [this]
  exact map_zipIdx_fst _ _ 0

theorem proverSideOfLookupInChainAtOneOwner_moves (R : Reads) (J : LookJobs W) (wit : W₁ → W) (a : At) :
    (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) R J wit a).parts.map (·.moves.length) =
      (stages a.face).map (Stage.rounds a.face) := by
  rw [← lookRow_moves (V := Unit) R J a]
  simp [proverSideOfLookupInChainAtOneOwner, Part.lift, Function.comp_def]

theorem lookSims_length (a : At) : (lookSims (Pb := Pb) a).length = (stages a.face).length := by
  simp [lookSims]

theorem foldl_add_eq_sum {α : Type} (g : α → Nat) (l : List α) (n : Nat) :
    l.foldl (fun k p => k + g p) n = n + (l.map g).sum := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => simp [ih]; omega

/-- **The half has the verifier's number of rounds.** -/
theorem proverSideOfLookupAtOneOwner_rounds (R : Reads) (J : LookJobs W) (a : At) (h : 2 ≤ a.face.planes) :
    (proverSideOfLookupAtOneOwner (V := V) R J a).rounds = (entriesV a.face).length := by
  unfold Placed.rounds proverSideOfLookupAtOneOwner
  rw [foldl_add_eq_sum (fun p : Part V W Unit => p.moves.length), lookRow_moves,
    rounds_stages a.face h, Nat.zero_add]

/-! ## The slots -/

theorem ownSlots_eq (vs : List Var) : ownSlots vs = 1 + (vs.map fun v => v.d - 1).sum :=
  foldl_add_eq_sum (fun v : Var => v.d - 1) vs 1

theorem sum_range_const (n c : Nat) : ((List.range n).map fun _ => c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [Nat.succ_mul]

theorem sum_replicate_const (n c : Nat) : (List.replicate n c).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

theorem sum_map_flatMap {α β : Type} (g : α → List β) (h : β → Nat) (l : List α) :
    ((l.flatMap g).map h).sum = (l.map fun x => ((g x).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- A product level with m variables takes 2 m + 3 slots in front of its two end values. -/
theorem ownRun_level (m : Nat) : ownRun (levelCall m) = 2 * m + 3 := by
  rw [levelCall_eq]
  simp only [ownRun, Call.all, levelEnds, ownSlots_eq, List.map_append,
    List.map_replicate, List.sum_append, sum_replicate_const, Var.d, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  omega

theorem sum_leaf_low (d n : Nat) (h : n ≤ d) :
    ((List.range n).map fun j => (if j < d then 3 else 2) - 1).sum = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
    have : n < d := by omega
    simp [this]
    omega

theorem sum_leaf (d mu : Nat) :
    ((List.range (mu + d)).map fun j => (if j < d then 3 else 2) - 1).sum = mu + 2 * d := by
  induction mu with
  | zero => rw [Nat.zero_add, sum_leaf_low d d (Nat.le_refl d)]; omega
  | succ mu ih =>
    have e : mu + 1 + d = (mu + d) + 1 := by omega
    rw [e, List.range_succ, List.map_append, List.sum_append, ih]
    have : ¬ (mu + d < d) := by omega
    simp [this]
    omega

theorem slots_key (f : LFace) (i m : Nat) : Stage.slots f (.key i m) = 2 * m + 5 := by
  show ownRun (levelCall m) + 2 = 2 * m + 5
  rw [ownRun_level]

theorem slots_tab (f : LFace) (l : Nat) : Stage.slots f (.tab l) = 2 * (f.mu + l) + 5 := by
  show ownRun (levelCall (f.mu + l)) + 2 = 2 * (f.mu + l) + 5
  rw [ownRun_level]

theorem slots_leaves (f : LFace) : Stage.slots f .leaves = 1 + f.mu + 2 * f.d := by
  show ownRun { lead := 0, vs := leafVars f #[], ends := none } + 0 = 1 + f.mu + 2 * f.d
  simp only [ownRun, Call.all, ownSlots_eq, leafVars, List.map_map, Function.comp_def, Var.d,
    sum_leaf]
  omega

theorem slots_bits (f : LFace) : Stage.slots f .bits = 1 + 2 * (f.mu + f.d) + 2 + 1 := by
  show ownRun (bitsCall (List.replicate (f.mu + f.d) zeroE)) + 1 = 1 + 2 * (f.mu + f.d) + 2 + 1
  simp only [ownRun, bitsCall, Call.all, ownSlots_eq, List.map_append, List.map_replicate,
    List.sum_append, sum_replicate_const, Var.d, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem slots_ties (f : LFace) (n : Nat) :
    (((List.range (n + 1)).map Stage.tie).map (Stage.slots f)).sum = 7 + 6 * n := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.sum_cons, List.map_map,
    List.map_map]
  have : ((Stage.slots f ∘ Stage.tie) ∘ Nat.succ) = fun _ => 6 := by funext s; rfl
  rw [this, sum_range_const]
  show 7 + n * 6 = 7 + 6 * n
  omega

theorem slots_splits (f : LFace) (n : Nat) :
    (((List.range n).map Stage.split).map (Stage.slots f)).sum = 5 * n := by
  rw [List.map_map]
  have : (Stage.slots f ∘ Stage.split) = fun _ => 5 := by funext s; rfl
  rw [this, sum_range_const]
  omega

/-- **The stages' slots add up to the verifier's count.** -/
theorem slots_stages (f : LFace) (h : 2 ≤ f.planes) :
    ((stages f).map (Stage.slots f)).sum = f.slots := by
  have hp : f.planes - 1 = (f.planes - 2) + 1 := by omega
  unfold stages VerifiableInference.Desc.K3.Face.slots
  simp only [List.map_append, List.sum_append]
  rw [hp, slots_ties, slots_splits, sum_map_flatMap, sum_map_flatMap]
  have ha : ((if f.shifted = true then [Stage.shift] else []).map (Stage.slots f)).sum = 0 := by
    split <;> rfl
  have hk : (f.parts.zipIdx.map fun x =>
      (((List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]).map
        (Stage.slots f)).sum) = f.parts.map fun v => ((List.range v).map fun k => 2 * k + 5).sum :=
          by
    rw [← map_zipIdx_fst (fun v => ((List.range v).map fun k => 2 * k + 5).sum) f.parts 0]
    congr 1
    funext x
    rw [sum_map_flatMap]
    congr 2
    funext m
    show Stage.slots f (.key x.2 m) + (0 + 0) = 2 * m + 5
    rw [slots_key]
  have ht : ((List.range f.d).map fun l =>
      (([Stage.tab l, Stage.tabLine l] : List Stage).map (Stage.slots f)).sum) =
      (List.range f.d).map fun l => 2 * (f.mu + l) + 5 := by
    congr 1
    funext l
    show Stage.slots f (.tab l) + (0 + 0) = 2 * (f.mu + l) + 5
    rw [slots_tab]
  have hl : (([Stage.leaves, Stage.zero, Stage.bits] : List Stage).map (Stage.slots f)).sum =
      (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1) := by
    show Stage.slots f .leaves + (0 + (Stage.slots f .bits + 0)) = _
    rw [slots_leaves, slots_bits]
    omega
  have hb : (([Stage.alpha] : List Stage).map (Stage.slots f)).sum = 0 := rfl
  have hj : (([Stage.join] : List Stage).map (Stage.slots f)).sum = 0 := rfl
  rw [ha, hk, ht, hl, hb, hj]
  omega

#print axioms ProofFile.Honest.K3.levelCall_eq
#print axioms ProofFile.Honest.K3.slots_stages
#print axioms ProofFile.Honest.K3.two_le_planes_of_ok
#print axioms ProofFile.Honest.K3.entries_stages
#print axioms ProofFile.Honest.K3.entries_length
#print axioms ProofFile.Honest.K3.rounds_stages
#print axioms ProofFile.Honest.K3.sumPart_moves
#print axioms ProofFile.Honest.K3.partOf_moves
#print axioms ProofFile.Honest.K3.lookRow_length
#print axioms ProofFile.Honest.K3.lookRow_moves
#print axioms ProofFile.Honest.K3.proverSideOfLookupInChainAtOneOwner_moves
#print axioms ProofFile.Honest.K3.lookSims_length
#print axioms ProofFile.Honest.K3.proverSideOfLookupAtOneOwner_rounds
#print axioms ProofFile.Honest.K3.flatMap_zipIdx_fst
#print axioms ProofFile.Honest.K3.getD_map_length
#print axioms ProofFile.Honest.K3.map_range_const
#print axioms ProofFile.Honest.K3.entries_level
#print axioms ProofFile.Honest.K3.entries_ties
#print axioms ProofFile.Honest.K3.entries_splits
#print axioms ProofFile.Honest.K3.entries_keys
#print axioms ProofFile.Honest.K3.entries_tabs
#print axioms ProofFile.Honest.K3.map_zipIdx_fst
#print axioms ProofFile.Honest.K3.foldl_add_eq_sum
#print axioms ProofFile.Honest.K3.ownSlots_eq
#print axioms ProofFile.Honest.K3.sum_range_const
#print axioms ProofFile.Honest.K3.sum_replicate_const
#print axioms ProofFile.Honest.K3.sum_map_flatMap
#print axioms ProofFile.Honest.K3.ownRun_level
#print axioms ProofFile.Honest.K3.sum_leaf_low
#print axioms ProofFile.Honest.K3.sum_leaf
#print axioms ProofFile.Honest.K3.slots_key
#print axioms ProofFile.Honest.K3.slots_tab
#print axioms ProofFile.Honest.K3.slots_leaves
#print axioms ProofFile.Honest.K3.slots_bits
#print axioms ProofFile.Honest.K3.slots_ties
#print axioms ProofFile.Honest.K3.slots_splits

end ProofFile.Honest.K3
