-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverReps.lean: a choice of the counted falls that proves the
field `hin` of `FirstAsks` (Honest/Law/CoverAsks.lean). The structure takes a function `reps` that
gives, for each sub-protocol, the falls for which a bound is stated there. `hin` asks that every
fall of the chain's list that stands near a sub-protocol lies inside one of them. "Near" means: at
the place of the sub-protocol itself or of a sub-protocol without a round right after it (`groupOf`,
Honest/Law/CoverNone.lean). Here `reps` is laid as all falls of the list that stand near the
sub-protocol. Then `hin` holds: each fall lies inside itself. It is general in the chain and in the
list of falls.

  1  `groupPlaces`, `repsAt`   the definitions
  2  `dropWhile_at`, `groupPlaces_at`   in a list with distinct places, the places near the
     sub-protocol after `A`
  3  `mem_repsAt`   a fall of the list that stands near a sub-protocol is counted there
  4  `hin_reps`   the field `hin`

Limits.
  * With this choice the field `hF` asks a bound for each fall of the list that stands near the
    sub-protocol.
  * Where no fall of the list stands near a sub-protocol, `repsAt` is empty there. How many falls
    it has at a sub-protocol of a given chain is not shown here.
  * That the places are distinct (`hnd`) is a hypothesis. `places_nodup` (Honest/Law/Cuts.lean)
    proves it from a description's own test on its places.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl : Type}

/-! ## 1 The counted falls -/

/-- The places of the group of the sub-protocol that stands at `p` in the list: its own place and
the places of the sub-protocols without a round right after it (`groupOf`,
Honest/Law/CoverNone.lean). The empty list if none stands at `p`. -/
def groupPlaces (all : List (Block S Cl)) (p : Place) : List Place :=
  match all.dropWhile (fun d => d.place != p) with
  | [] => []
  | b :: rest => (groupOf b rest).map (·.place)

/-- The counted falls at a sub-protocol: the falls of the list that stand at a place of its
group. -/
def repsAt (all : List (Block S Cl)) (fs : List (Fall S)) (b : Block S Cl) : List (Fall S) :=
  fs.filter fun f => decide (f.place ∈ groupPlaces all b.place)

/-! ## 2 The places near a sub-protocol -/

/-- Dropping the sub-protocols that do not stand at `p` leaves the list from the first one that
does. -/
theorem dropWhile_at {A rest : List (Block S Cl)} {c : Block S Cl} {p : Place}
    (h : ∀ a ∈ A, a.place ≠ p) (hc : c.place = p) :
    (A ++ c :: rest).dropWhile (fun d => d.place != p) = c :: rest := by
  induction A with
  | nil =>
    have hn : ¬ ((c.place != p) = true) := by
      rw [hc]
      simp
    exact List.dropWhile_cons_of_neg hn
  | cons a A ih =>
    have hy : (a.place != p) = true := bne_iff_ne.2 (h a List.mem_cons_self)
    have e1 : (a :: (A ++ c :: rest)).dropWhile (fun d => d.place != p) =
        (A ++ c :: rest).dropWhile (fun d => d.place != p) := List.dropWhile_cons_of_pos hy
    exact e1.trans (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- In a list with distinct places: the places near the sub-protocol after `A`. -/
theorem groupPlaces_at {all A rest : List (Block S Cl)} {b : Block S Cl}
    (hnd : (all.map (·.place)).Nodup) (e : all = A ++ b :: rest) :
    groupPlaces all b.place = (groupOf b rest).map (·.place) := by
  subst e
  rw [List.map_append] at hnd
  have hd := (List.pairwise_append.1 hnd).2.2
  have h := dropWhile_at (rest := rest) (c := b) (p := b.place)
    (fun a ha => hd a.place (List.mem_map.2 ⟨a, ha, rfl⟩) b.place
      (List.mem_map.2 ⟨b, List.mem_cons_self, rfl⟩)) rfl
  unfold groupPlaces
  simp only [h]

/-! ## 3 A fall near a sub-protocol is counted there -/

/-- A fall of the list that stands at the place of a member of the group is counted. -/
theorem mem_repsAt {all A rest : List (Block S Cl)} {b : Block S Cl}
    (hnd : (all.map (·.place)).Nodup) (e : all = A ++ b :: rest) {fs : List (Fall S)}
    {f : Fall S} (hf : f ∈ fs) {d : Block S Cl} (hd : d ∈ groupOf b rest)
    (hp : f.place = d.place) : f ∈ repsAt all fs b := by
  refine List.mem_filter.2 ⟨hf, decide_eq_true ?_⟩
  rw [groupPlaces_at hnd e, hp]
  exact List.mem_map.2 ⟨d, hd, rfl⟩

/-! ## 4 The field -/

/-- The field `hin` of `FirstAsks`, at `reps := repsAt all fs`, at every list of falls, every test
`seatF` and every condition `P`. The counted fall that takes a fall in is that fall itself. -/
theorem hin_reps {all pre₁ : List (Block S Cl)} {e₁ : Block S Cl} (cut : all = pre₁ ++ [e₁])
    (hnd : (all.map (·.place)).Nodup) (fs : List (Fall S)) (seatF : Place → Bool)
    (P : Block S Cl → List Fmt.Drawn → S → Prop) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → seatF b.place = true → b.rounds ≠ [] →
      ∀ f ∈ fs, (∃ d ∈ groupOf b (b' :: B ++ [e₁]), f.place = d.place) →
      ∃ g ∈ repsAt all fs b, ∀ fr s' own, P b fr s' →
        localFall [f] 0 (b :: (b' :: B ++ [e₁])) s' own →
        localFall [g] 0 (b :: (b' :: B ++ [e₁])) s' own := by
  intro A b b' B e _ _ f hf hd
  obtain ⟨d, hd, hp⟩ := hd
  have e' : all = A ++ b :: (b' :: B ++ [e₁]) := by
    rw [cut, e, List.append_assoc, List.cons_append, List.cons_append]
  exact ⟨f, mem_repsAt hnd e' hf hd hp, fun _ _ _ _ h => h⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.dropWhile_at
#print axioms ProofFile.Honest.groupPlaces_at
#print axioms ProofFile.Honest.mem_repsAt
#print axioms ProofFile.Honest.hin_reps
