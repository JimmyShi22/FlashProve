-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotPlaces.lean: no two jobs of the two lots of the kind K1 are at one place.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Z is any public part and G any ground; there is no further premise.
  lotPlaces_nodup    The list of the places of lotPars Z G (LotsTest.lean: the public numbers of the
                     jobs of lotJobs and wJobs, in their order) has no entry twice.
  lotPlacesApart     So the public test lotPlacesApartB Z G (LotsGuard.lean) accepts.
  jobPlaces_nodup    The same for the jobs themselves: the list of J.P.place over lotJobs and wJobs
                     has no entry twice.

How it fits. With jobs_52_in_scope (LotCount.lean) the 52 entries are 52 places. The look-up from a
sender's address to its job (lotAt, LotsGuard.lean) then finds each job. The proof reads the places
off the lists' text: the opening is at piece 1 of segment 0; a segment's reads and digits are at
pieces 4 and 6 or 5 and 7 of that segment (IM.numbers_pieces, Johnson/IMR/K1Seat.lean); the
request's own table is in no segment. A lemma on lists: no distribution is named. Not one of the
release's goal statements.

The other names.
  laterPlacesAt      the places of one segment's reads and digits.
  laterPlaces_eq     the places of laterPars are these, segment by segment.
  later_mem, later_nodup   each is in its segment, at a piece from 4 on; the two differ.

Limits. It says nothing on the description's other members. All limits of AtDescLots.lean.
-/
import Johnson.SendSim.Seat.LotsGuard
import Johnson.SendSim.Seat.LotsTestTie

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {X Xi : Type}

/-- The places of one segment's reads and digits. -/
def laterPlacesAt (G : ProofFile.Ground) (y : OnBytes.Model.Stages.LinkH × Nat) : List Place :=
  match K1.linkNumbers G y.1 with
  | none => []
  | some (pr, pd, _, _) => [⟨1, some y.2, pr, .K1⟩, ⟨1, some y.2, pd, .K1⟩]

theorem laterPlaces_eq (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (laterPars Z G).map (·.place) = G.built.toList.zipIdx.flatMap (laterPlacesAt G) := by
  unfold laterPars
  rw [List.map_flatMap]
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  unfold laterPlacesAt
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn]
    rfl
  · simp only [hn]
    rfl

theorem later_mem {G : ProofFile.Ground} {y : OnBytes.Model.Stages.LinkH × Nat} {a : Place}
    (h : a ∈ laterPlacesAt G y) : a.link = some y.2 ∧ 4 ≤ a.piece := by
  unfold laterPlacesAt at h
  split at h
  · cases h
  · rename_i pr pd reads digits hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases IM.numbers_pieces hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h with rfl | rfl <;>
      exact ⟨rfl, by simp⟩

theorem later_nodup (G : ProofFile.Ground) (y : OnBytes.Model.Stages.LinkH × Nat) :
    (laterPlacesAt G y).Nodup := by
  unfold laterPlacesAt
  split
  · exact List.nodup_nil
  · rename_i pr pd reads digits hn
    rcases IM.numbers_pieces hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- **No two entries of lotPars are at one place.** -/
theorem lotPlaces_nodup (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((lotPars Z G).map (·.1.place)).Nodup := by
  have h1 : (lotPars Z G).map (·.1.place) =
      ((⟨1, some 0, 1, .K1⟩ : Place) :: (laterPars Z G).map (·.place)) ++
        ((linMessageW Z.first.lin).map fun _ => (⟨1, none, 4, .K1⟩ : Place)).toList := by
    unfold lotPars
    rw [List.map_append, List.map_cons, List.map_map]
    refine congrArg₂ (· ++ ·) rfl ?_
    cases linMessageW Z.first.lin <;> rfl
  rw [h1, laterPlaces_eq]
  refine List.Nodup.append (List.nodup_cons.2 ⟨?_, ?_⟩) ?_ ?_
  · intro hm
    obtain ⟨y, _, hy⟩ := List.mem_flatMap.1 hm
    exact absurd (later_mem hy).2 (by decide)
  · refine List.nodup_flatMap.2 ⟨fun y _ => later_nodup G y, ?_⟩
    have h0 : (G.built.toList.zipIdx.map Prod.snd).Pairwise (· < ·) := by
      rw [List.zipIdx_map_snd]
      exact List.pairwise_lt_range'
    refine (List.pairwise_map.1 h0).imp fun {a b} hab => ?_
    show List.Disjoint (laterPlacesAt G a) (laterPlacesAt G b)
    intro x hxa hxb
    have e := (later_mem hxa).1
    rw [(later_mem hxb).1] at e
    exact absurd (Option.some.inj e).symm (Nat.ne_of_lt hab)
  · cases linMessageW Z.first.lin <;> simp
  · intro a ha hb
    have hn : a.link = none := by
      cases hW : linMessageW Z.first.lin with
      | none => rw [hW] at hb; cases hb
      | some msg =>
        rw [hW] at hb
        rw [List.mem_singleton.1 hb]
    rcases List.mem_cons.1 ha with rfl | ha
    · cases hn
    · obtain ⟨y, _, hy⟩ := List.mem_flatMap.1 ha
      rw [(later_mem hy).1] at hn
      cases hn

/-- The public test on the jobs' places accepts. -/
theorem lotPlacesApart (Z : ProofFile.Pub) (G : ProofFile.Ground) : lotPlacesApartB Z G = true :=
  decide_eq_true (lotPlaces_nodup Z G)

/-- No two jobs of the two lists are at one place. -/
theorem jobPlaces_nodup (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    ((lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G).map (·.P.place)).Nodup := by
  have h := lotPlaces_nodup Z G
  rw [lotPars_eq (X := X) no D Z G, List.map_map] at h
  exact h

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.lotPlaces_nodup
#print axioms OnBytes.SendSim.Seat.lotPlacesApart
#print axioms OnBytes.SendSim.Seat.jobPlaces_nodup
