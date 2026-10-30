-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowOwnedLaw.lean: the key file's letter for the owners of the row's
stretches (`keyOwners`, Honest/K3/RowOwned.lean), unrolled slot by slot, is the verifier's own list
`K3.fromKeys` (Johnson/Desc/First/Look/K3Key.lean): general in the face. Theorems, and one helper
definition.

Terms. Honest/K3/GLOSSARY.md ("part, stretch", "slot", "stage", "letter, letters").

What is shown.
  `bitsOf`, `secondOf_eq`: a stage's share of the unrolled letter.
  `plain_of_not_key`, `bitsOf_plain`, `plain_flat`: at every stage but a key level both stretches
    are the lookups' own message's: "no", as often as the stage has slots.
  `zipIdx_getD`: a part's number finds the part's size. `mult_ne`: the two owners' names differ.
    `no_add`: "no" a times, then b times.
  `bitsOf_level`, `keys_flat`: a key level and the line behind it; all key trees.
  `fromKeys_eq`: the theorem, at every face with two planes or more.

Hypotheses that remain.
  `h`: (in `fromKeys_eq`) the face has two planes or more, which the face's own test asks; (in
    `plain_of_not_key`, `bitsOf_plain`) the stage is no key level.
  `hv`: (in `bitsOf_level`) part i has the size v.
  Without a name, in front of arrows: in `plain_flat`: no stage of the list is a key level; in
    `zipIdx_getD`: x is a member of the numbered list.

Limits. Names and numbers alone. The hypothesis is needed: with fewer than two planes the row has no
tie step, and the verifier's list counts seven slots for one.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.First.Look.K3Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc.K3 (fromKeys)

local notation "no" => VerifiableInference.Desc.K3.own

/-- A stage's share of the key file's letter, unrolled. -/
def bitsOf (f : LFace) (s : Stage) : List Bool :=
  List.replicate (s.own f) ((keyOwners f s).1 == indexMaskRun) ++
    List.replicate (s.tail f) ((keyOwners f s).2 == indexMaskRun)

/-- The unrolled letter is the stages' shares, one behind the other. -/
theorem secondOf_eq (f : LFace) : secondOf (keyOwners f) f indexMaskRun =
    (stages f).flatMap (bitsOf f) :=
  rfl

/-- The two owners' names differ. -/
theorem mult_ne : (multRun == indexMaskRun) = false := by decide

/-- "No" a times, then b times. -/
theorem no_add (a b : Nat) : no a ++ no b = no (a + b) := by
  unfold VerifiableInference.Desc.K3.own
  rw [List.replicate_append_replicate]

/-- At every stage but a key level both stretches are the lookups' own message's. Conditional on the
stage being no key level. -/
theorem plain_of_not_key (f : LFace) (s : Stage) (h : ∀ i m, s ≠ .key i m) :
    keyOwners f s = (multRun, multRun) := by
  cases s <;> first | rfl | exact absurd rfl (h _ _)

/-- Such a stage's share: "no", as often as it has slots. Conditional on the stage being no key
level. -/
theorem bitsOf_plain (f : LFace) (s : Stage) (h : ∀ i m, s ≠ .key i m) :
    bitsOf f s = no (Stage.slots f s) := by
  unfold bitsOf
  rw [plain_of_not_key f s h]
  show List.replicate _ (multRun == indexMaskRun) ++ List.replicate _ (multRun == indexMaskRun) = _
  rw [mult_ne]
  exact no_add _ _

/-- A list of stages without a key level: "no", as often as they have slots. Conditional on that. -/
theorem plain_flat (f : LFace) : ∀ (l : List Stage), (∀ s ∈ l, ∀ i m, s ≠ .key i m) →
    l.flatMap (bitsOf f) = no ((l.map (Stage.slots f)).sum)
  | [], _ => rfl
  | s :: l, h => by
    rw [List.flatMap_cons, bitsOf_plain f s (h s (List.mem_cons_self ..)),
      plain_flat f l (fun t ht => h t (List.mem_cons_of_mem _ ht)), no_add, List.map_cons,
      List.sum_cons]

/-- A part's number finds the part's size. Conditional on the pair standing in the numbered list. -/
theorem zipIdx_getD (pre : List Nat) : ∀ (l : List Nat) (x : Nat × Nat), x ∈ l.zipIdx pre.length →
    (pre ++ l).getD x.2 0 = x.1
  | [], x, h => by simp at h
  | a :: l, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have e := zipIdx_getD (pre ++ [a]) l x (by rw [List.length_append]; exact h)
      rw [List.append_assoc] at e
      exact e

/-- A key level and the line behind it. Here v is the size of the level's part. Conditional on v
being that size. -/
theorem bitsOf_level (f : LFace) (i m v : Nat) (hv : f.parts.getD i 0 = v) :
    bitsOf f (.key i m) ++ bitsOf f (.keyLine i m) =
      if m + 1 == v then no (2 * m + 3) ++ [true, true] else no (2 * m + 5) := by
  have hl : bitsOf f (.keyLine i m) = [] := rfl
  have ho : Stage.own f (.key i m) = 2 * m + 3 := ownRun_level m
  have ht : Stage.tail f (.key i m) = 2 := rfl
  rw [hl, List.append_nil]
  unfold bitsOf
  rw [ho, ht]
  show List.replicate (2 * m + 3) (multRun == indexMaskRun) ++ List.replicate 2
    ((if m + 1 == f.parts.getD i 0 then indexMaskRun else multRun) == indexMaskRun) = _
  rw [mult_ne, hv]
  split
  · rfl
  · rw [mult_ne]
    exact no_add _ _

/-- All key trees. -/
theorem keys_flat (f : LFace) :
    (f.parts.zipIdx.flatMap fun x =>
      (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]).flatMap (bitsOf f) =
    f.parts.flatMap fun v => (List.range v).flatMap fun k =>
      if k + 1 == v then no (2 * k + 3) ++ [true, true] else no (2 * k + 5) := by
  rw [List.flatMap_assoc]
  have e : ∀ x ∈ f.parts.zipIdx,
      ((List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]).flatMap (bitsOf f)
        =
        (fun v => (List.range v).flatMap fun k =>
          if k + 1 == v then no (2 * k + 3) ++ [true, true] else no (2 * k + 5)) x.1 := by
    intro x hx
    have hv : f.parts.getD x.2 0 = x.1 := zipIdx_getD [] f.parts x hx
    rw [List.flatMap_assoc]
    refine List.flatMap_congr fun m _ => ?_
    show bitsOf f (.key x.2 m) ++ (bitsOf f (.keyLine x.2 m) ++ []) = _
    rw [List.append_nil]
    exact bitsOf_level f x.2 m x.1 hv
  rw [List.flatMap_congr e]
  exact flatMap_zipIdx_fst (fun v => (List.range v).flatMap fun k =>
    if k + 1 == v then no (2 * k + 3) ++ [true, true] else no (2 * k + 5)) f.parts 0

/-- **The key file's letter, unrolled, is the verifier's own list.** Conditional on two planes or
more, which the face's own test asks. Instances, and a face with one plane at which the two lists
part: Honest/K3/RowOwnedGuards.lean [not in this library]. -/
theorem fromKeys_eq (f : LFace) (h : 2 ≤ f.planes) :
    secondOf (keyOwners f) f indexMaskRun = fromKeys f := by
  have hp : f.planes - 1 = (f.planes - 2) + 1 := by omega
  rw [secondOf_eq]
  unfold stages fromKeys
  rw [List.flatMap_append, List.flatMap_append, List.flatMap_append, keys_flat, List.append_assoc,
    ← List.flatMap_append]
  congr 1
  · congr 1
    rw [plain_flat f _ (by
      intro s hs i m e
      subst e
      cases hsh : f.shifted <;> simp [hsh] at hs)]
    congr 1
    simp only [List.map_append, List.sum_append]
    rw [hp, slots_ties, slots_splits]
    have ha : ((if f.shifted = true then [Stage.shift] else []).map (Stage.slots f)).sum = 0 := by
      split <;> rfl
    rw [ha]
    show 0 + 0 + (7 + 6 * (f.planes - 2)) + 5 * (f.parts.length - 1) + 0 = _
    omega
  · rw [plain_flat f _ (by
      intro s hs i m e
      subst e
      simp at hs)]
    congr 1
    rw [List.map_append, List.sum_append, sum_map_flatMap]
    have et : (fun l => (([Stage.tab l, Stage.tabLine l] : List Stage).map (Stage.slots f)).sum) =
        fun l => 2 * (f.mu + l) + 5 := by
      funext l
      show Stage.slots f (.tab l) + (0 + 0) = _
      rw [slots_tab]
    rw [et]
    show _ + (Stage.slots f .leaves + (0 + (Stage.slots f .bits + 0))) = _
    rw [slots_leaves, slots_bits]
    omega

#print axioms ProofFile.Honest.K3.secondOf_eq
#print axioms ProofFile.Honest.K3.mult_ne
#print axioms ProofFile.Honest.K3.no_add
#print axioms ProofFile.Honest.K3.plain_of_not_key
#print axioms ProofFile.Honest.K3.bitsOf_plain
#print axioms ProofFile.Honest.K3.plain_flat
#print axioms ProofFile.Honest.K3.zipIdx_getD
#print axioms ProofFile.Honest.K3.bitsOf_level
#print axioms ProofFile.Honest.K3.keys_flat
#print axioms ProofFile.Honest.K3.fromKeys_eq

end ProofFile.Honest.K3
