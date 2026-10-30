-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverGroup.lean: AN IDLE MEMBER's GROUP HOLDS NO SEAT.
`localDebts_sparse` (Honest/Law/CoverSparse.lean) asks, at an idle member b with a round, that no
fall of the chain's list sits in b's group: b and the members without a round right behind it
(`groupOf`, Honest/Law/CoverNone.lean). Falls go by the place. Here, general in the chain: seat: a
test on places that every fall's place passes; Busy: a letter on members. WHERE EVERY MEMBER WITHOUT
A ROUND AT A SEAT HAS RIGHT IN FRONT OF IT A BUSY MEMBER WITH A ROUND, the group of a member that is
not busy and sits at no seat holds no seat (`group_idle`); so no fall sits there (`group_noFall`).

WHAT THIS IS. Lemmas on lists and on a definition of ours. None of the library's goals.

  `quiet_idle`, `group_idle`, `group_noFall`

Limits. The premise H (what stands right in front of a seat without a round) is shown here of no
chain: at the first chain it is a closed fact on the written places with one fact on the members'
rounds. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl : Type}

/-- Along the members without a round behind c: none sits at a seat, where c has no round or is not
busy. -/
theorem quiet_idle (all : List (Block S Cl)) (seat : Place → Bool) (Busy : Block S Cl → Prop)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seat d.place = true → d.rounds = [] → c.rounds ≠ [] ∧ Busy c) :
    ∀ (t P : List (Block S Cl)) (c : Block S Cl), all = P ++ c :: t →
      (c.rounds = [] ∨ ¬ Busy c) →
      ∀ d ∈ t.takeWhile (fun d => d.rounds.isEmpty), seat d.place = false
  | [], _, _, _, _, d, hd => by cases hd
  | e :: t', P, c, hall, hc, d, hd => by
    by_cases he : e.rounds.isEmpty = true
    · rw [List.takeWhile_cons_of_pos (p := fun d : Block S Cl => d.rounds.isEmpty) (a := e)
        (l := t') he] at hd
      have he' : e.rounds = [] := List.isEmpty_iff.1 he
      rcases List.mem_cons.1 hd with rfl | hd'
      · cases hs : seat d.place with
        | false => rfl
        | true =>
          obtain ⟨h1, h2⟩ := H P c d t' hall hs he'
          rcases hc with hc | hc
          · exact absurd hc h1
          · exact absurd h2 hc
      · exact quiet_idle all seat Busy H t' (P ++ [c]) e
          (by rw [hall, List.append_assoc, List.singleton_append]) (Or.inl he') d hd'
    · rw [List.takeWhile_cons_of_neg (p := fun d : Block S Cl => d.rounds.isEmpty) (a := e)
        (l := t') he] at hd
      cases hd

/-- **The group of a member that is not busy and sits at no seat holds no seat.** -/
theorem group_idle (all : List (Block S Cl)) (seat : Place → Bool) (Busy : Block S Cl → Prop)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seat d.place = true → d.rounds = [] → c.rounds ≠ [] ∧ Busy c)
    (A : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl)) (hall : all = A ++ b :: t)
    (hb : seat b.place = false) (hn : ¬ Busy b) : ∀ d ∈ groupOf b t, seat d.place = false := by
  intro d hd
  unfold groupOf at hd
  rcases List.mem_cons.1 hd with rfl | hd'
  · exact hb
  · exact quiet_idle all seat Busy H t A b hall (Or.inr hn) d hd'

/-- **So no fall of a list whose falls all sit at seats sits in that group.** -/
theorem group_noFall (all : List (Block S Cl)) (seat : Place → Bool) (Busy : Block S Cl → Prop)
    (H : ∀ (P : List (Block S Cl)) (c d : Block S Cl) (Q : List (Block S Cl)),
      all = P ++ c :: d :: Q → seat d.place = true → d.rounds = [] → c.rounds ≠ [] ∧ Busy c)
    (fs : List (Fall S)) (hfs : ∀ f ∈ fs, seat f.place = true) (A : List (Block S Cl))
    (b : Block S Cl) (t : List (Block S Cl)) (hall : all = A ++ b :: t)
    (hb : seat b.place = false) (hn : ¬ Busy b) :
    ∀ d ∈ groupOf b t, ∀ f ∈ fs, f.place ≠ d.place := by
  intro d hd f hf e
  have h1 := group_idle all seat Busy H A b t hall hb hn d hd
  rw [← e, hfs f hf] at h1
  cases h1

end ProofFile.Honest

#print axioms ProofFile.Honest.quiet_idle
#print axioms ProofFile.Honest.group_idle
#print axioms ProofFile.Honest.group_noFall
