-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyK14Sits.lean: K14_sits, THE KEY FILE's HALF, AT THE PLACES
1 · 2 · 4 · 5 OF THE SHARED CHAIN: THE SEATING SUBSTITUTED INTO THE LAWS' PREMISES:
where
K14's eight blocks can be said at the key file's own parameters (p14At X P = Key.sharedPar X.chains
(Key.beforeSharedPoint P)), THE DESCRIPTION's OWN SHARED CHAIN (Key.descriptionFromSource X N P).shared.blocksInOrder HOLDS AT
SEAT 1 + j THE BLOCK seat bⱼ, AND THAT BLOCK's YES, AS THE MAKER HOLDS IT (held), GIVES THE PREMISE
hl OF THE LAW AT THAT ROW, NAMED BELOW (2.1: linPoint · 2.2 | 2.5: SentBack, and the sending kind's
IsSend · 2.4: loc).
THE SEATING IS CALLED IN THE FORM shared_at_blocks (Johnson/RunOne/KeyCut23.lean): light.
desc_eight (RunOne/Sound/KeyEightAtDesc.lean [not in this library]; its statement stands in
Johnson/RunOne/Sound/KeyEightLight.lean) says the same places at the
same parameters with atClaim b := bareB b.retype, WHICH IS seat b's OWN TEXT, and gives the list
from planOk alone; it is not called here:
sits_of_seating takes the seating as a premise in the form that BOTH give, so that desc_eight
enters by one application where it lies.
OBJECT: (Key.descriptionFromSource X N P).shared.blocksInOrder · held (seat bⱼ) · USER: the list's row K14_sits («the key
file's too where it seats the kind»); loc_back₂_seat | point_back₂_seat | keeps₂_send2_seat |
keeps₂_send5_seat (their b := seat bⱼ, hdⱼ := rfl) · LETTERS: X N P; Pr free.
  eight_of_blocks   where the kind's blocks can be said they are eight [a near twin of
    blocks_length, Johnson/RunOne/Sound/KeyEightLight.lean]
  Sits1245          what is said of a list of seats
  sits_of_seating   from any seating «blocksInOrder[1 + j]? = some (seat b)»
  k14_sits_key      at the key file's description, by shared_at_blocks
NOT HERE: place 7 (row 2.7: KeyRow27Chance.lean's hz_held: the like) · places 3 · 6 · 8
(rows 2.3 · 2.6 · 2.8: left to other files) · that blocks (p14At X P) can be said (planOk:
fk_blocks_of_planOk [not in this library]) · that the MAKER's pieces hold these seats at these
numbers (rowAt₂, Johnson/Top/Fire/Code/RowCut.lean). Nothing on soundness.

-/
import Johnson.RunOne.KeyRowsSeat
import Johnson.RunOne.KeyCut23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (IsSend)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)

/-- Where the kind's blocks can be said they are eight. -/
theorem eight_of_blocks (Q : P14) (l : List (Block St₂ Unit)) (h : blocks Q = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks at h
  cases hu : withU Q.S with
  | none =>
    rw [hu] at h
    cases h
  | some u =>
    rw [hu] at h
    exact ⟨_, _, _, _, _, _, _, _, (Option.some.inj h).symm⟩

/-- **What is said of a list of seats**: at the places 1 · 2 · 4 · 5 lie blocks whose yes, as the
maker holds them, gives the laws' premises. -/
def Sits1245 {Cl : Type} (Q : P14) (flat : List (Block St₂ Cl)) : Prop :=
  ∃ c1 c2 c4 c5 : Block St₂ Cl, flat[1]? = some c1 ∧ flat[2]? = some c2 ∧ flat[4]? = some c4 ∧
      flat[5]? = some c5 ∧
    ∀ Pr : Type,
      (∀ z rs gs z', (held c1 : Block (Pr × St₂) Cl).decide z rs gs = .ok z' → z'.1 = z.1 ∧
          _root_.Desc.K14.linPoint Q.par z.2 rs = some z'.2) ∧
      (∀ z rs gs z', (held c2 : Block (Pr × St₂) Cl).decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack
          z.2 z'.2) ∧
      (∀ z rs gs z', (held c4 : Block (Pr × St₂) Cl).decide z rs gs = .ok z' → z'.1 = z.1 ∧
          _root_.Desc.K14.loc Q.par z.2 rs gs = some z'.2) ∧
      (∀ z rs gs z', (held c5 : Block (Pr × St₂) Cl).decide z rs gs = .ok z' → z'.1 = z.1 ∧ SentBack
          z.2 z'.2) ∧
      (∃ sentU, withU Q.S = some sentU ∧ IsSend (parK1 Q 2 "o_u and the first mask" sentU) (fun z :
          Pr × St₂ => z.2.st) (held c2 : Block (Pr × St₂) Cl)) ∧
      IsSend (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) (fun z : Pr × St₂ => z.2.st) (held c5 :
          Block (Pr × St₂) Cl)

/-- **From any seating.** -/
theorem sits_of_seating {Cl : Type} (Q : P14) (l : List (Block St₂ Unit)) (h : blocks Q = some l)
    (flat : List (Block St₂ Cl))
    (hs : ∀ (j : Nat) (b : Block St₂ Unit), l[j]? = some b → flat[1 + j]? = some (seat b)) :
        Sits1245 Q flat := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_blocks Q l h
  refine ⟨seat b1, seat b2, seat b4, seat b5, hs 0 b1 rfl, hs 1 b2 rfl, hs 3 b4 rfl, hs 4 b5 rfl,
      fun Pr => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact hl_point Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b1) rfl
  · exact hl_send2 Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b2) rfl
  · exact hl_loc Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b4) rfl
  · exact hl_send5 Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b5) rfl
  · exact hS_sends Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b2) rfl
  · exact hS_send5 Q b1 b2 b3 b4 b5 b6 b7 b8 h (seat b5) rfl

/-- A member of the mapped list behind a head. -/
theorem getElem?_seated {α β : Type} (f : α → β) (a : β) (l : List α) (r s : List β) (j : Nat) (b :
    α) (hb : l[j]? = some b) :
    (a :: (l.map f ++ r ++ s))[1 + j]? = some (f b) := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  rw [Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simpa using hj),
    List.getElem?_map, hb]
  rfl

/-- **K14_sits, the key file's half, at the places 1 · 2 · 4 · 5.** -/
theorem k14_sits_key (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (l : List (Block St₂ Unit))
    (h : blocks (p14At X P) = some l) :
    Sits1245 (p14At X P) (descriptionFromSource X N P).shared.blocksInOrder := by
  refine sits_of_seating (p14At X P) l h _ fun j b hb => ?_
  rw [shared_at_blocks X N P l h]
  exact getElem?_seated seat _ l _ _ j b hb

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.sits_of_seating
#print axioms Johnson.RunOne.KeyRows23.k14_sits_key
