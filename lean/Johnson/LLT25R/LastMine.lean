-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastMine.lean (two lists of members, as in
LastRowTwo.lean): THE LEDGER's FIELD `sits` (`MineSits`) AT A CLOSED mine AND A CLOSED
smp: what no run could evaluate is paid by make; FIVE TESTS ON THE PLAN ARE LEFT.
  `smpLast`: the sample as the last chain's law reads it off the whole record: of a member at
    Omega's seat: what the shared chain's table reads off the shared chain's last record; of every
    other: what the first chain's table reads off what was handed.
  `mineOf`: the members of the first table's list ms₁ that sit at W's or the index masks' seat, and
    those of the shared table's list ms₂ that sit at Omega's.
  `sits_closed`: **`MineSits` at these two, FROM: somebody of ms₁ sits at W's seat, somebody at the
    index masks'; somebody of ms₂ at Omega's; Omega's seat is neither W's nor the index masks'.**
Limits. The five are tests on the plan's lists and numbers: evaluated nowhere here. That smp₁ and
smp₂ are the tables' own readers is the caller's. Nothing on soundness.
-/
import Johnson.LLT25R.LastRowTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)

variable (cs : OnBytes.Codes) {P S₁ S₂ S₃ P₀ : Type}
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ ms₂ : List Mem) (get : P × S₁ → P₀ × First.S) (N₁ : Numbers) (Ns : NumbersS)

/-- **The sample off the whole record.** -/
def smpLast (a : (P × S₁ × S₂) × S₃) (s : Sending) (i : Fin s.l.length) :
    Option ((sigOf cs s.l).om i).Smp :=
  if s.seat i = Ns.tenant .oOmega then smp₂ a.1.2.2 s i else smp₁ (get (a.1.1, a.1.2.1)) s i

/-- **Mine: who of each table's list sits at one of its seats.** -/
def mineOf : List Mem :=
  (ms₁.filter fun x => decide (x.1.seat x.2 = N₁.w) || decide (x.1.seat x.2 = N₁.index)) ++
    ms₂.filter fun x => decide (x.1.seat x.2 = Ns.tenant .oOmega)

variable {ms₁ ms₂ N₁ Ns}

theorem mem_mineOf {x : Mem} : x ∈ mineOf ms₁ ms₂ N₁ Ns ↔
    (x ∈ ms₁ ∧ (x.1.seat x.2 = N₁.w ∨ x.1.seat x.2 = N₁.index)) ∨
      (x ∈ ms₂ ∧ x.1.seat x.2 = Ns.tenant .oOmega) := by
  unfold mineOf
  simp only [List.mem_append, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]

/-- **The ledger's field `sits`, from five tests on the plan.** -/
theorem sits_closed (someW : ∃ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2)
    (someI : ∃ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2)
    (someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2)
    (apartWO : N₁.w ≠ Ns.tenant .oOmega) (apartIO : N₁.index ≠ Ns.tenant .oOmega) :
    MineSits (S₃ := S₃) cs (smpLast cs smp₁ smp₂ get Ns) smp₁ smp₂ ms₁ ms₂
      (mineOf ms₁ ms₂ N₁ Ns) get N₁ Ns where
  each := by
    intro x hx
    rcases mem_mineOf.1 hx with ⟨hm, h | h⟩ | ⟨hm, h⟩
    · exact Or.inl ⟨hm, h, fun a => if_neg (h ▸ apartWO)⟩
    · exact Or.inr (Or.inl ⟨hm, h, fun a => if_neg (h ▸ apartIO)⟩)
    · exact Or.inr (Or.inr ⟨hm, h, fun a => if_pos h⟩)
  allW := fun x hm hs => mem_mineOf.2 (Or.inl ⟨hm, Or.inl hs⟩)
  allI := fun x hm hs => mem_mineOf.2 (Or.inl ⟨hm, Or.inr hs⟩)
  allO := fun x hm hs => mem_mineOf.2 (Or.inr ⟨hm, hs⟩)
  someW := someW
  someI := someI
  someO := someO
  apartWO := apartWO
  apartIO := apartIO

end LLT25

#print axioms LLT25.mem_mineOf
#print axioms LLT25.sits_closed
