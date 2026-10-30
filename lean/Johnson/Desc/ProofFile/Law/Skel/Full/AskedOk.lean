-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/AskedOk.lean: WHERE A BATCHING IS ASKED, AT THE FULL SIZE: AT
THE SPOTS' PLACES ALONE. The rounds' column's laws (SkelRounds.lean, SkelRoundsParts.lean) ask a
lot's batching only where a letter A holds. Here A is "a spot sits at the place". Definitions,
statements and proofs.
  `IsSpot spots a`    a spot of the list sits at a
  `asks_full`         A CLOSED FACT, DECIDED BY LEAN's KERNEL: at the written sorts each place at
                      which the driver asks for a batching (`askAt`) is a written place's
  `asked_are_spots`   so hA, where the places and the sorts are the written ones
  `nameAt_default`    at a spot's place the name that is looked up does not hang on the default
  `name_at_spot`      and, at the written places, it is that spot's own (`names_full`)
  `hK_of_spots`       **hK at A := `IsSpot B.spots`, from: for each lot, each spot p and what the
                      lot's batching makes at p's place, at every gatherer: Q holds of p's name and
                      its rounds**
Why. A lot's `batch` may answer at places that nobody asks: K9's does not read the place's chain.
Limits. Nothing is paid. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Names
import Johnson.Desc.ProofFile.Law.Skel.SkelRoundsParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-- A spot of the list sits at a. -/
def IsSpot (spots : List Spot) (a : Place) : Prop := ∃ p ∈ spots, p.place = a

theorem asks_full :
    (subsW.zipIdx.all fun x => spotsW.any fun p => p.place == askAt x.2 x.1) = true := by
  decide +kernel

theorem asked_are_spots {Z : Pub} {B : PureBase} (h₁ : B.spots = spotsW)
    (h₄ : subsOf Z = subsW) : ∀ x ∈ (subsOf Z).zipIdx, IsSpot B.spots (askAt x.2 x.1) := by
  intro x hx
  rw [h₄] at hx
  rw [h₁]
  obtain ⟨p, hp, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 asks_full x hx)
  exact ⟨p, hp, eq_of_beq e⟩

theorem nameAt_default {spots : List Spot} {a : Place} (h : IsSpot spots a) (n m : String) :
    nameAtSk spots a n = nameAtSk spots a m := by
  obtain ⟨p, hp, e⟩ := h
  unfold nameAtSk
  cases f : spots.find? fun q => q.place == a with
  | some q => rfl
  | none =>
    have k := List.find?_eq_none.1 f p hp
    rw [e] at k
    exact absurd (beq_self_eq_true a) k

theorem name_at_spot {B : PureBase} (h₁ : B.spots = spotsW) :
    ∀ p ∈ B.spots, ∀ n, nameAtSk B.spots p.place n = p.name := by
  intro p hp n
  rw [nameAt_default ⟨p, hp, rfl⟩ n "", h₁]
  rw [h₁] at hp
  exact eq_of_beq (List.all_eq_true.1 names_full p hp)

theorem hK_of_spots {Q : String → List Fmt.DeclaredRound → Prop} {T : PureSeat} {B : PureBase}
    (h₁ : B.spots = spotsW)
    (wK : ∀ L ∈ T.lots, ∀ p ∈ B.spots, ∀ mk, L.batch B.G₀ p.place = some mk →
      ∀ g, Q p.name (mk g).rounds) :
    ∀ L ∈ T.lots, ∀ a mk, IsSpot B.spots a → L.batch B.G₀ a = some mk →
      ∀ g, Q (nameAtSk B.spots a (mk g).name) (mk g).rounds := by
  intro L hL a mk hA hb g
  obtain ⟨p, hp, e⟩ := hA
  subst e
  rw [name_at_spot h₁ p hp]
  exact wK L hL p hp mk hb g

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.asks_full
#print axioms ProofFile.Sk.Full.asked_are_spots
#print axioms ProofFile.Sk.Full.nameAt_default
#print axioms ProofFile.Sk.Full.name_at_spot
#print axioms ProofFile.Sk.Full.hK_of_spots
