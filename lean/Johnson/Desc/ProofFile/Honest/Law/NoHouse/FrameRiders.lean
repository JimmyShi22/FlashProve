-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FrameRiders.lean: the list of rider clauses `csHead`
(Thread/CsHead.lean) at the borders after the 77 sub-protocols of the kind `frame` of the first
chain at the full size. At 76 of these borders no clause of the list speaks, so `ridersOf (csHead ν
st R)` (Thread/Riders.lean) holds there of every state. At border 349, after the frame's step after
the batching of the output head's segment, one clause speaks: "the field `wo` is set". No
definition.

  1  `csHead_spans`      the spans of the list's clauses, written out
  2  `csHead_clear_of`   no clause speaks at border 1, 353 or 358, at a border `14 * l + 2` with
     `l < 25`, or at a border `14 * l + 11` or `14 * l + 15` with `l < 24`
  3  `riders_clear`      so `ridersOf (csHead ν st R)` holds there of every input and state
  4  `csHead_only_wo`    a clause that speaks at border 349 is the clause on `wo`
  5  `riders_349`        `ridersOf` passes from border 348 to border 349 over a step that leaves the
     library's `rest9` (Johnson/Desc/First/Link/Law/Rest9.lean)
  6  `riders_front`, `riders_laid`, `riders_behind`, `riders_cleared`, `riders_seal`   the
     hypotheses `hRd` of the five lemmas of FrameOwes.lean, at `Rd := ridersOf (csHead ν st R)`
  7  `csHead_none_begins`   no clause of the list begins at one of the 77 borders. So the column
     `hl` of `owesS_head_form` (Thread/GatherHeadForm.lean) asks nothing at these sub-protocols

Limits.
  * About the list `csHead` alone. A longer list needs these lemmas anew.
  * Nothing shows that a clause holds at any state.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHeadAt
import Johnson.Desc.ProofFile.Honest.Thread.Numbers358
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindLeft
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.ClearIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (rest9)
open ProofFile.Honest.FirstThread (rest9_wo clearIx_is)

variable {W : Type} {ν : Nat} {st : Nat → S → Prop}
  {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {c : RiderCl W S}

/-- The spans of the list's clauses. -/
theorem csHead_spans (h : c ∈ csHead ν st R) :
    (c.lo = 342 ∧ c.hi = 347) ∨ (c.lo = 343 ∧ c.hi = 348) ∨ (c.lo = 347 ∧ c.hi = 352) ∨
      (c.lo = 346 ∧ c.hi = 346) ∨ (c.lo = 344 ∧ c.hi = 345) ∨ (c.lo = 346 ∧ c.hi = 347) ∨
      (∃ l, l < 24 ∧ c.lo = 14 * l + 9 ∧ c.hi = 14 * l + 9) ∨
      (∃ g, g < 12 ∧ c.lo = 14 * (2 * g + 1) + 4 ∧ c.hi = 14 * (2 * g + 1) + 9) ∨
      ∃ g, g < 12 ∧ c.lo = 28 * g + 5 ∧ c.hi = 28 * g + 10 := by
  rcases (csHead_mem ν st R c).1 h with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, rfl, rfl⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g, hg, rfl, rfl⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨g, hg, rfl, rfl⟩))))))))

/-- No clause of the list speaks at these borders. -/
theorem csHead_clear_of {n : Nat}
    (hn : n = 1 ∨ n = 353 ∨ n = 358 ∨ (∃ l, l < 25 ∧ n = 14 * l + 2) ∨
      ∃ l, l < 24 ∧ (n = 14 * l + 11 ∨ n = 14 * l + 15))
    (h : c ∈ csHead ν st R) : ¬ (c.lo ≤ n ∧ n ≤ c.hi) := by
  rcases csHead_spans h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ |
      ⟨l', hl', a, b⟩ | ⟨g, hg, a, b⟩ | ⟨g, hg, a, b⟩ <;>
    rcases hn with rfl | rfl | rfl | ⟨l, hl, rfl⟩ | ⟨l, hl, rfl | rfl⟩ <;> omega

/-- So the list's condition holds there of every input and state. -/
theorem riders_clear {n : Nat}
    (hn : n = 1 ∨ n = 353 ∨ n = 358 ∨ (∃ l, l < 25 ∧ n = 14 * l + 2) ∨
      ∃ l, l < 24 ∧ (n = 14 * l + 11 ∨ n = 14 * l + 15)) (v : W) (s : S) :
    ridersOf (csHead ν st R) n v s :=
  fun _ hc h1 h2 => absurd ⟨h1, h2⟩ (csHead_clear_of hn hc)

/-- A clause of the list that speaks at border 349 is the clause on `wo`. -/
theorem csHead_only_wo (h : c ∈ csHead ν st R) (h1 : c.lo ≤ 349) (h2 : 349 ≤ c.hi) :
    c = riderHead 347 352 fun a => a.wo.isSome = true := by
  rcases (csHead_mem ν st R c).1 h with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · have a2 : 349 ≤ 347 := h2
    omega
  · have a2 : 349 ≤ 348 := h2
    omega
  · rfl
  · have a2 : 349 ≤ 346 := h2
    omega
  · have a2 : 349 ≤ 345 := h2
    omega
  · have a2 : 349 ≤ 347 := h2
    omega
  · have a2 : 349 ≤ 347 := h2
    omega
  · have a2 : 349 ≤ 14 * l + 9 := h2
    omega
  · have a2 : 349 ≤ 14 * (2 * g + 1) + 9 := h2
    omega
  · have a2 : 349 ≤ 28 * g + 10 := h2
    omega

/-- From border 348 to border 349, over a step that leaves `rest9`. -/
theorem riders_349 (v : W) (s s' : S) (H : ridersOf (csHead ν st R) 348 v s)
    (e : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    ridersOf (csHead ν st R) 349 v s' := by
  intro c hc h1 h2
  have ec := csHead_only_wo hc h1 h2
  subst ec
  obtain ⟨a, ha, hP⟩ := csHead_wo_at H (by omega) (by omega)
  obtain ⟨a', ha', ew⟩ := rest9_wo e a ha
  refine ⟨a', ha', ?_⟩
  show a'.wo.isSome = true
  rw [ew]
  exact hP

/-! ## The hypotheses `hRd` of FrameOwes.lean -/

theorem riders_front (v : W) (s : S) (_ : ridersOf (csHead ν st R) 0 v s) :
    ridersOf (csHead ν st R) (0 + 1) v s :=
  riders_clear (Or.inl rfl) v s

theorem riders_laid {l : Nat} (hl : l < 25) (v : W) (s : S)
    (_ : ridersOf (csHead ν st R) (14 * l + 1) v s) :
    ridersOf (csHead ν st R) (14 * l + 1 + 1) v s :=
  riders_clear (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, hl, rfl⟩)))) v s

theorem riders_behind {l : Nat} (hl : l < 25) (v : W) (s s' : S)
    (H : ridersOf (csHead ν st R) (14 * l + IM.nAt l + 3) v s)
    (e : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    ridersOf (csHead ν st R) (14 * l + IM.nAt l + 3 + 1) v s' := by
  by_cases h24 : l = 24
  · subst h24
    have n9 := nAt_head
    have e8 : 14 * 24 + IM.nAt 24 + 3 = 348 := by omega
    have e9 : 14 * 24 + IM.nAt 24 + 3 + 1 = 349 := by omega
    rw [e8] at H
    rw [e9]
    exact riders_349 v s s' H e
  · have n7 := nAt_lt (l := l) (by omega)
    exact riders_clear (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, by omega, Or.inl (by omega)⟩)))) v s'

theorem riders_cleared {l : Nat} (hl : l < 25) (v : W) (s t : S)
    (_ : ridersOf (csHead ν st R) (P1L20.clearIx l) v s) :
    ridersOf (csHead ν st R) (P1L20.clearIx l + 1) v t := by
  have ei := clearIx_is l
  by_cases h24 : l = 24
  · subst h24
    have n9 := nAt_head
    exact riders_clear (Or.inr (Or.inl (by omega))) v t
  · have n7 := nAt_lt (l := l) (by omega)
    exact riders_clear (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, by omega, Or.inr (by omega)⟩)))) v t

theorem riders_seal (v : W) (s : S) (_ : ridersOf (csHead ν st R) 357 v s) :
    ridersOf (csHead ν st R) 358 v s :=
  riders_clear (Or.inr (Or.inr (Or.inl rfl))) v s

/-- No clause of the list begins at the border after a sub-protocol of the kind `frame`. -/
theorem csHead_none_begins {b : Nat}
    (hb : b = 0 ∨ b = 357 ∨ ∃ l, l < 25 ∧
      (b = 14 * l + 1 ∨ b = 14 * l + IM.nAt l + 3 ∨ b = 14 * l + IM.nAt l + 7))
    (h : c ∈ csHead ν st R) : c.lo ≠ b + 1 := by
  have n9 := nAt_head
  have n7 : ∀ l, l < 24 → IM.nAt l = 7 := fun l hl => nAt_lt hl
  intro e
  rcases hb with rfl | rfl | ⟨l, hl, hb⟩
  · rcases csHead_spans h with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ |
      ⟨l', -, a, -⟩ | ⟨g, -, a, -⟩ | ⟨g, -, a, -⟩ <;> omega
  · rcases csHead_spans h with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ |
      ⟨l', hl', a, -⟩ | ⟨g, hg, a, -⟩ | ⟨g, hg, a, -⟩ <;> omega
  · by_cases h24 : l = 24
    · subst h24
      rcases csHead_spans h with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ |
        ⟨l', hl', a, -⟩ | ⟨g, hg, a, -⟩ | ⟨g, hg, a, -⟩ <;> omega
    · have e7 := n7 l (by omega)
      rcases csHead_spans h with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩ |
        ⟨l', hl', a, -⟩ | ⟨g, hg, a, -⟩ | ⟨g, hg, a, -⟩ <;> omega

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_spans
#print axioms ProofFile.Honest.csHead_clear_of
#print axioms ProofFile.Honest.riders_clear
#print axioms ProofFile.Honest.csHead_only_wo
#print axioms ProofFile.Honest.riders_349
#print axioms ProofFile.Honest.riders_front
#print axioms ProofFile.Honest.riders_laid
#print axioms ProofFile.Honest.riders_behind
#print axioms ProofFile.Honest.riders_cleared
#print axioms ProofFile.Honest.riders_seal
#print axioms ProofFile.Honest.csHead_none_begins
