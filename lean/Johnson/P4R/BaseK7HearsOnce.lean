-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/BaseK7HearsOnce.lean: AT AN OPENING OF THE PROOF FILE's IOP AS
WRITTEN IN LEAN (IM.Open, IMR/SeatOpen.lean): EVERY MEMBER OF base AT A PLACE OF THE KIND K7
HEARS ONCE, at the reader heardV of the heard reply (Johnson/P5J/ReplyAtDriver.lean). One theorem
and a small lemma on lists. For (R3) of the frame fact on the reply.

  mapM_back         what a mapM's answer holds comes from a member of the list. (A NEAR TWIN of
                    mapM_ok_mem, Loose/H2K12/SitsInPure.lean: typed again so that this
                    file does not stand over that one.)
  base_k7_under     a member of base at such a place is Under x.retype, x a member of
                    ProofFile.h1Own Bs.G₀.
  base_k7_hearsOnce MAIN.

THE ROAD. O.places and mapM_back: the member stands in the seat's list of places ·
places_from_lots: it is the batching's face, or a lot's sub-protocol at the blank letters,
marked, under the spot's name · the face bears the kind K9 (face_kind, makers_K9) · lot_K7: a lot's
sub-protocol of the kind K7 is x.retype, x of ProofFile.h1Own · guardMark_yes: the marked one accepts only
where the lot's own does, with the same state behind · Law/K7HearsOnceUnder.lean: k7_lot_hearsOnce.
AT EVERY LETTER o FOR THE SECOND HASH FUNCTION: no scope is asked.
WHAT IT IS NOT. UNDER hV: the plan's vocabulary is no larger than the reference's. An implication:
the opening O is a premise. Nothing on soundness.

-/
import Johnson.IMR.K7Seat
import Johnson.Desc.Kinds.Law.K7HearsOnceUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law (k7_lot_hearsOnce)
open ProofFile (Cl)

theorem mapM_back {α β : Type} (f : α → Except String β) : ∀ (l : List α) (out : List β),
    l.mapM f = .ok out → ∀ y ∈ out, ∃ x ∈ l, f x = .ok y
  | [], out, h, y, hy => by
    rw [List.mapM_nil] at h
    cases h
    cases hy
  | a :: l, out, h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok z =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok zs =>
        rw [hl] at h
        obtain rfl : z :: zs = out := Except.ok.inj h
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨x, hx, e⟩ := mapM_back f l zs hl y hy'
          exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- A member of base at a place of the kind K7 is Under the lot's own sub-protocol. -/
theorem base_k7_under (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ b0 ∈ base, b0.place.kind = KindName.K7 →
      ∃ x ∈ ProofFile.h1Own Bs.G₀, b0.Under (x.retype : Block S Cl) := by
  intro b0 hb hk
  have hp := O.places
  unfold ProofFile.PureParts.base at hp
  obtain ⟨⟨sp, r⟩, hx, e⟩ := mapM_back _ _ _ hp b0 hb
  obtain rfl : r = .ok b0 := e
  obtain ⟨_, hc⟩ := IM.places_from_lots (IM.base_made O.made).2.2.2 sp b0 hx
  rcases hc with ⟨mk, hmk, rfl⟩ | ⟨_, L, hL, b', hb', _, rfl⟩
  · rw [IM.face_kind (IM.makers_K9 Z Bs.G₀) hmk] at hk
    cases hk
  · obtain ⟨x, hx', rfl⟩ := IM.lot_K7 (Z := Z) hL hb' hk
    exact ⟨x, hx', fun s rs gs s' H => ((IM.guardMark_yes _ s s' rs gs).1 H).1⟩

/-- **EVERY MEMBER OF base AT A PLACE OF THE KIND K7 HEARS ONCE.** -/
theorem base_k7_hearsOnce (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hV : Bs.G₀.W.hS.V ≤ Inst.Model.ppref.V) :
    ∀ b0 ∈ base, b0.place.kind = KindName.K7 →
      b0.HearsOnce (P5J.heardV fun s : S => s) := by
  intro b0 hb hk
  obtain ⟨x, hx, hU⟩ := base_k7_under O b0 hb hk
  exact k7_lot_hearsOnce hV ⟨x, hx, rfl⟩ hU

end P4

#print axioms P4.base_k7_under
#print axioms P4.base_k7_hearsOnce
