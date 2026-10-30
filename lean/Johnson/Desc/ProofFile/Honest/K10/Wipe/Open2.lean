-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Open2.lean: the closing of a segment (K10): the walk of Wipe/Lots2.lean at the
letters of an opening of the proof file's description (Johnson/IMR/SeatOpen.lean: IM.Open), and from there the premise
that Honest/K10/WipeFold.lean's front_zero wants. General in w : S → S, S the first chain's state. Theorems.

  open_front2       SeatKeeps2 w, SeatRest2 w and an opening with the first chain c: every block of Meaning.K2.frontOf c
                    is Decides2 w
  takeWhile_front   a first stretch of two lists in a row ends inside the first list, where that list has a member
                    that ends it
  keeps_front       so, for a place a that a block of frontOf c bears: every block of c.blocksInOrder in front of the first
                    block at a is Keeps w 0

What is proved, by what. open_front2 follows Johnson/IMR/OpenWalk.lean's open_front, over thePure_keeps2, chainBy_front2
and the five laws on partsAt (Wipe/Lots2.lean). keeps_front: the library's flat_eq and chainBy_noFront cut c.blocksInOrder into
frontOf c and the blocks behind the last link; keeps_of_decides2 (Wipe/Link2.lean) goes from Decides2 to Keeps.

Limits. SeatKeeps2 and SeatRest2 are premises: they are shown of no w here. That the closing's place is borne by a block
of frontOf c is a premise too. Nothing is shown of a block behind the last link. No property of the protocol is claimed:
nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Lots2
import Johnson.IMR.OpenWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.First (S)

variable {w : S → S} {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The walk at an opening's own letters.** -/
theorem open_front2 (H : SeatKeeps2 w) (Hr : SeatRest2 w) (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∀ b ∈ Meaning.K2.frontOf c, Decides2 w b := by
  have hall := Meaning.K2.all_of_made (IM.base_made O.made).2.2.2
  have K₀ : LotsKeep2 w (ProofFile.pureSeat o Z).lots Bs.G₀ := thePure_keeps2 H Hr Z Bs.G₀
  exact chainBy_front2 O.chain (partsAt_base2 (failed_of H) K₀ hall O.places)
    (partsAt_frames2 (failed_of H) K₀ hall)
    (fun a mk e f hf => (partsAt_roadW2 (failed_of H) K₀ e f hf).1)
    (fun l => partsAt_each2 K₀ l) (fun l => partsAt_tests2 K₀ l) (sameReply2 H)

/-- A first stretch of two lists in a row is that of the first list, where a member of the first list ends it. -/
theorem takeWhile_front {α : Type} (p : α → Bool) : ∀ (l₁ l₂ : List α), (∃ x ∈ l₁, p x = false) →
    (l₁ ++ l₂).takeWhile p = l₁.takeWhile p := by
  intro l₁ l₂
  induction l₁ with
  | nil =>
    intro h
    obtain ⟨x, hx, _⟩ := h
    cases hx
  | cons a l ih =>
    intro h
    by_cases hp : p a = true
    · obtain ⟨x, hx, hx'⟩ := h
      rcases List.mem_cons.1 hx with e | hx
      · rw [e, hp] at hx'
        cases hx'
      · rw [List.cons_append, List.takeWhile_cons_of_pos hp, List.takeWhile_cons_of_pos hp, ih ⟨x, hx, hx'⟩]
    · rw [List.cons_append, List.takeWhile_cons_of_neg hp, List.takeWhile_cons_of_neg hp]

/-- **What front_zero wants**: every block of the first chain's flat list in front of a place inside the links keeps. -/
theorem keeps_front (H : SeatKeeps2 w) (Hr : SeatRest2 w) (O : IM.Open o pol lay KL F Z Bs base c A B) {a : Place}
    (ha : ∃ b ∈ Meaning.K2.frontOf c, b.place = a) :
    ∀ b ∈ c.blocksInOrder.takeWhile (·.place != a), Keeps w 0 b := by
  intro b hb
  obtain ⟨b₀, hb₀, e₀⟩ := ha
  have hp : (fun x : Block S ProofFile.Cl => x.place != a) b₀ = false := by
    show (b₀.place != a) = false
    rw [e₀]
    simp only [bne_self_eq_false]
  rw [Meaning.K2.flat_eq (Meaning.K2.chainBy_noFront O.chain),
    takeWhile_front (fun x : Block S ProofFile.Cl => x.place != a) _ _ ⟨b₀, hb₀, hp⟩] at hb
  exact keeps_of_decides2 (open_front2 H Hr O b ((List.takeWhile_prefix _).subset hb)) 0

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.open_front2
#print axioms ProofFile.Honest.K10.takeWhile_front
#print axioms ProofFile.Honest.K10.keeps_front
