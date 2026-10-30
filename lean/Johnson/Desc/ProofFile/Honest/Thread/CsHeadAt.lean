-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/CsHeadAt.lean: lemmas that read one clause out of the list
`csHead` (CsHead.lean). The part `rides` of the first chain's invariant is
`ridersOf (csHead ν st R)`: at border `b` it says that every clause of the list whose span holds `b`
is true. Each lemma here takes that statement at a border inside one clause's span and returns that
clause's fact. They are for the sub-protocol that uses the fact. No definition.

  1  `csHead_x_at`, `csHead_t_at`, `csHead_wo_at`   the fields `x`, `t`, `wo` of the head's own part
     are set
  2  `csHead_next_at`   the ledger's next free slot is `ν`
  3  `csHead_fold0_at`, `csHead_fold1_at`   the number `tl.foldDrawn` is 0, is 1
  4  `csHead_st_head_at`, `csHead_st_at`   the fact `st l` after a segment's lookup argument on the
     digits
  5  `csHead_att_at`, `csHead_own_at`   the facts of an attention segment and of a layers' segment
  6  `csHead_in_head`   between the borders 342 and 352 the chain is in the head's segment

Limits.
  * Each lemma has `ridersOf (csHead ν st R) b w s` as a hypothesis. It is not proved here at any
    state.
  * No property of the protocol is proved.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

/-- From border 342 to border 347 the field `x` of the head's own part is set. -/
theorem csHead_x_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 342 ≤ b) (h₂ : b ≤ 347) :
    ∃ a, s.here = .head a ∧ a.x.isSome = true :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inl rfl))))) h₁ h₂

/-- From border 343 to border 348 the field `t` of the head's own part is set. -/
theorem csHead_t_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 343 ≤ b) (h₂ : b ≤ 348) :
    ∃ a, s.here = .head a ∧ a.t.isSome = true :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inl rfl)))))) h₁ h₂

/-- From border 347 to border 352 the field `wo` of the head's own part is set. -/
theorem csHead_wo_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 347 ≤ b) (h₂ : b ≤ 352) :
    ∃ a, s.here = .head a ∧ a.wo.isSome = true :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inr (Or.inl rfl))))))) h₁ h₂

/-- At border 346 the ledger's next free slot is `ν`. -/
theorem csHead_next_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 346 ≤ b) (h₂ : b ≤ 346) :
    ∃ a, s.here = .head a ∧ a.F.next = ν :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) h₁ h₂

/-- At the borders 344 and 345 the number `tl.foldDrawn` is 0. -/
theorem csHead_fold0_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 344 ≤ b) (h₂ : b ≤ 345) :
    ∃ a, s.here = .head a ∧ a.tl.foldDrawn = 0 :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) h₁ h₂

/-- At the borders 346 and 347 the number `tl.foldDrawn` is 1. -/
theorem csHead_fold1_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 346 ≤ b) (h₂ : b ≤ 347) :
    ∃ a, s.here = .head a ∧ a.tl.foldDrawn = 1 :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) h₁ h₂

/-- At the borders 346 and 347 the fact `st 24` holds. -/
theorem csHead_st_head_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 346 ≤ b) (h₂ : b ≤ 347) : st 24 s :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))) h₁ h₂

/-- At border `14 * l + 9`, for `l` below 24, the fact `st l` holds. -/
theorem csHead_st_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {l : Nat} (hl : l < 24) {w : W} {s : S}
    (h : ridersOf (csHead ν st R) (14 * l + 9) w s) : st l s :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inr ⟨l, hl, rfl⟩)))) (Nat.le_refl _)
    (Nat.le_refl _)

/-- From border `14 * (2 * g + 1) + 4` to border `14 * (2 * g + 1) + 9`, for `g` below 12, the chain
is in an attention segment and `R g` holds of the field `g` of its own part. -/
theorem csHead_att_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {g : Nat} (hg : g < 12) {b : Nat} {w : W}
    {s : S} (h : ridersOf (csHead ν st R) b w s) (h₁ : 14 * (2 * g + 1) + 4 ≤ b)
    (h₂ : b ≤ 14 * (2 * g + 1) + 9) : ∃ a, s.here = .att a ∧ R g a.g :=
  h _ ((csHead_mem ν st R _).2 (Or.inl (Or.inr ⟨g, hg, rfl⟩))) h₁ h₂

/-- From border `28 * g + 5` to border `28 * g + 10`, for `g` below 12, the layers' segment's own
rounds have returned something. -/
theorem csHead_own_at {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {g : Nat} (hg : g < 12) {b : Nat} {w : W}
    {s : S} (h : ridersOf (csHead ν st R) b w s) (h₁ : 28 * g + 5 ≤ b) (h₂ : b ≤ 28 * g + 10) :
    ∃ o, s.own? = some o :=
  h _ ((csHead_mem ν st R _).2 (Or.inr ⟨g, hg, rfl⟩)) h₁ h₂

/-- Between the borders 342 and 352 the chain is in the head's segment. -/
theorem csHead_in_head {W : Type} {ν : Nat} {st : Nat → S → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {b : Nat} {w : W} {s : S}
    (h : ridersOf (csHead ν st R) b w s) (h₁ : 342 ≤ b) (h₂ : b ≤ 352) :
    ∃ a, s.here = .head a := by
  by_cases h₃ : b ≤ 347
  · obtain ⟨a, ha, -⟩ := csHead_x_at h h₁ h₃
    exact ⟨a, ha⟩
  · obtain ⟨a, ha, -⟩ := csHead_wo_at h (by omega) h₂
    exact ⟨a, ha⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_x_at
#print axioms ProofFile.Honest.csHead_t_at
#print axioms ProofFile.Honest.csHead_wo_at
#print axioms ProofFile.Honest.csHead_next_at
#print axioms ProofFile.Honest.csHead_fold0_at
#print axioms ProofFile.Honest.csHead_fold1_at
#print axioms ProofFile.Honest.csHead_st_head_at
#print axioms ProofFile.Honest.csHead_st_at
#print axioms ProofFile.Honest.csHead_att_at
#print axioms ProofFile.Honest.csHead_own_at
#print axioms ProofFile.Honest.csHead_in_head
