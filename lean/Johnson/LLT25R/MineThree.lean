-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/MineThree.lean: THREE OF THE TESTS ON THE PLAN THAT THE LAST TABLE's LAW ASKS OF ITS
MEMBERS `mineOf ms₁ ms₂ N₁ Ns` (Johnson/LLT25R/LastMine.lean) COME DOWN TO FACTS ON THREE SEATS: a
member of that list sits at W's seat, at the index masks' or at Omega's, by its make.

  `fenced_mineOf`: the three seats' trees lie below base ⊢ `Fenced base (mineOf …)`.
  `fence_pure`: THE FIELD fence IN ITS OWN TEXT (base := `baseTwoAt (FL …) D (c0 Z) (c1 N)`), from:
    W's and the index masks' trees lie below D.t₁ · Omega's seat is (D.t₁ + nΩ, 0) · nΩ < D.t₂. No
    test on a list is left.
  `nodup_mineOf`: THE FIELD nodup, from: the list of mine's seats has no double · arr parts the
    three seats (three inequations of numbers).
  `oneTable_of_one`: THE FIELD oneTable at any list, from: no two of the list have one seat · one of
    the list sits at t and has the shape sh · `OneTable cs sh`.
  `oneTable_real`: `OneTable` at the written full size's codes and its shape for Omega: a closed
    fact, by the kernel.
  `oneTable_written`: `OneTable (p14At Z).codes (p14At Z).S.omega` wherever the public part is the
    written one (`Written Z x`, Johnson/Goal/Numbers/WrittenAtZ.lean).
Limits. Rules, and one closed fact at the full size. That any plan meets the premises is not shown
here. Nothing on soundness. On hiding nothing.

-/
import Johnson.LLT25R.LastNum
import Johnson.LLT25R.LastMine
import Johnson.ToldDescR.OneTableB
import Johnson.Goal.Numbers.WrittenAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker OnBytes.Params
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (S Numbers)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14.Law (Written k14_real sized_one)

variable {ms₁ ms₂ : List Mem} {N₁ : Numbers} {Ns : NumbersS}

/-- A member of mine sits at one of the three seats. -/
theorem seat_mineOf {x : Mem} (hx : x ∈ mineOf ms₁ ms₂ N₁ Ns) :
    seatOf x = N₁.w ∨ seatOf x = N₁.index ∨ seatOf x = Ns.tenant .oOmega := by
  rcases mem_mineOf.1 hx with ⟨-, h | h⟩ | ⟨-, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

/-- **Mine lie below a base below which the three seats' trees lie.** -/
theorem fenced_mineOf {base : ℕ} (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (ho : (Ns.tenant .oOmega).1 < base) : Fenced base (mineOf ms₁ ms₂ N₁ Ns) := by
  intro x hx
  rcases seat_mineOf hx with h | h | h
  · exact (show x.1.seat x.2 = N₁.w from h) ▸ hw
  · exact (show x.1.seat x.2 = N₁.index from h) ▸ hi
  · exact (show x.1.seat x.2 = Ns.tenant .oOmega from h) ▸ ho

/-- **THE FIELD fence, IN ITS OWN TEXT.** -/
theorem fence_pure (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
    (c : Chain S Cl) (D : WholeD) {nΩ : ℕ} (hw : N₁.w.1 < D.t₁) (hi : N₁.index.1 < D.t₁)
    (eO : Ns.tenant .oOmega = (D.t₁ + nΩ, 0)) (hn : nΩ < D.t₂) :
    Fenced (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) (mineOf ms₁ ms₂ N₁ Ns) := by
  rw [baseTwo_pure]
  exact fenced_mineOf (Nat.lt_of_lt_of_le hw (Nat.le_add_right _ _))
    (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)) (by rw [eO]; exact Nat.add_lt_add_left hn _)

/-- **THE FIELD nodup.** -/
theorem nodup_mineOf (arr : ℕ → ℕ → ℕ) (hs : ((mineOf ms₁ ms₂ N₁ Ns).map seatOf).Nodup)
    (h₁ : arr N₁.w.1 N₁.w.2 ≠ arr N₁.index.1 N₁.index.2)
    (h₂ : arr N₁.w.1 N₁.w.2 ≠ arr (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2)
    (h₃ : arr N₁.index.1 N₁.index.2 ≠ arr (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2) :
    ((mineOf ms₁ ms₂ N₁ Ns).map (numOf arr)).Nodup := by
  have e : (mineOf ms₁ ms₂ N₁ Ns).map (numOf arr) =
      ((mineOf ms₁ ms₂ N₁ Ns).map seatOf).map fun s => arr s.1 s.2 := by
    rw [List.map_map]
    rfl
  rw [e]
  refine List.Nodup.map_on ?_ hs
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  rcases seat_mineOf hx with p | p | p <;> rcases seat_mineOf hy with q | q | q <;>
    rw [p, q] at hab ⊢ <;> first
      | rfl
      | exact absurd hab h₁
      | exact absurd hab h₂
      | exact absurd hab h₃
      | exact absurd hab.symm h₁
      | exact absurd hab.symm h₂
      | exact absurd hab.symm h₃

/-- **THE FIELD oneTable, at any list.** -/
theorem oneTable_of_one {cs : Codes} {mine : List Mem} {t : ℕ × ℕ} {sh : OracleShape}
    (oneSeat : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y)
    (at_t : ∃ x ∈ mine, seatOf x = t ∧ sh = (x.1.l.get x.2).1) (hT : ToldDesc.OneTable cs sh) :
    ∀ x ∈ mine, seatOf x = t → ToldDesc.OneTable cs (x.1.l.get x.2).1 := by
  obtain ⟨x₀, h₀, s₀, e₀⟩ := at_t
  intro x hx sx
  obtain rfl := oneSeat x hx x₀ h₀ (sx.trans s₀.symm)
  exact e₀ ▸ hT

/-- At the written full size. -/
theorem oneTable_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ToldDesc.OneTable codesFull2 x.shape.omega := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => ToldDesc.oneTableB p.2 p.1.shape.omega) = true := by
    decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, (ToldDesc.oneTable_iff _ _).1 h⟩

/-- **Wherever the public part is the written one.** -/
theorem oneTable_written {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) : ToldDesc.OneTable (p14At Z).codes (p14At Z).S.omega := by
  obtain ⟨y, hy, T⟩ := oneTable_real
  obtain rfl := sized_one hx hy
  show ToldDesc.OneTable Z.p.chains.made.sized.proof.codes
    Z.p.chains.made.sized.proof.batch.shape.omega
  rw [h.codes, h.shape]
  exact T

end LLT25

#print axioms LLT25.seat_mineOf
#print axioms LLT25.fenced_mineOf
#print axioms LLT25.fence_pure
#print axioms LLT25.nodup_mineOf
#print axioms LLT25.oneTable_of_one
#print axioms LLT25.oneTable_real
#print axioms LLT25.oneTable_written
