-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/OnePart.lean: A SIDE OF ONE PART, OF TWO ROUNDS, THAT SPENDS AND
CARRIES NOTHING, PAYS (SidePays, Honest/Law/ReadyOfSides.lean) where the book has at its place the
cut [2], no row behind part 0, no entry that names the place as its spender, and the part's count.
General in the book, the description and the chain: no kind is named.

Limits. An implication. "It pays" says only that chainSteps returns. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.BookLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc (Block FileDescription Place)

variable {S Cl V W Y Xi : Type}

/-- What a side of the sending's form is: one part of two moves that spends and carries nothing. -/
structure OnePart (g : Placed V W Y) (p : Part V W Y) : Prop where
  parts : g.parts = [p]
  moves : p.moves.length = 2
  spends : p.spends = []
  carries : p.carries = []

/-- **The book's side of a member of the sending's form.** -/
structure BookAt (F : FileDescription Xi) (B : ProverCoinCounts) (ch : Nat) (b : Block S Cl) (d : Due) : Prop where
  chain : b.place ∈ placesAt F ch
  rounds : b.rounds.length = 2
  oracles : b.oracles.length = 2
  cut : B.cuts.lookup b.place = some [2]
  rows : (B.rowsOf ch).any (fun r => r.1.place == b.place && decide (1 ≤ r.1.part)) = false
  ahead : ∀ e ∈ B.ahead, e.spender.place ≠ b.place
  due : d = dueAt (B.rowsOf ch) ⟨b.place, 0⟩

theorem spentE_nil {B : ProverCoinCounts} {a : Addr} (h : ∀ e ∈ B.ahead, e.spender.place ≠ a.place) :
    spentE B a = [] := by
  unfold spentE
  refine List.filter_eq_nil_iff.2 fun e he => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 he
  exact absurd (by rw [beq_iff_eq.1 h2]) (h e h1)

theorem carryE_nil {B : ProverCoinCounts} {a : Addr} (h : ∀ e ∈ B.ahead, e.spender.place ≠ a.place) :
    carryE B a = [] := by
  unfold carryE
  refine List.filter_eq_nil_iff.2 fun e he => ?_
  obtain ⟨h1, h2⟩ := List.mem_filter.1 he
  exact absurd (by rw [beq_iff_eq.1 h2]) (h e h1)

/-- **A side of the form pays**, at each member of its place whose book is as stated. -/
theorem sidePays_one {F : FileDescription Xi} {B : ProverCoinCounts} (hw : B.word F = none) (hp : F.placesOk = true)
    {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) (bs : List (Block S Cl)) (g : Placed V W Y)
    (p : Part V W Y) (hg : OnePart g p)
    (H : ∀ b ∈ bs, b.place = g.place → BookAt F B ch b p.takes) : SidePays B ch bs g := by
  obtain ⟨pl, parts⟩ := g
  obtain ⟨h1, hm, hs, hc⟩ := hg
  dsimp only at h1
  subst h1
  refine sidePays_of_tests B ch bs _ fun b hb hpl => ?_
  obtain ⟨c1, r2, o2, cut, rows, ahead, due⟩ := H b hb hpl
  refine ⟨by rw [o2, r2], ?_, ?_, ?_, ?_, ?_⟩
  · show Placed.rounds _ = _
    simp [Placed.rounds, hm, r2]
  · rw [cut]
    simp [hm]
  · simpa using rows
  · refine List.any_eq_false.2 fun e he => ?_
    have := ahead e he
    simp [this]
  · obtain ⟨c, hc'⟩ := lendPart_of_fit (a := ⟨b.place, 0⟩) hw hp hch c1 due
      (by rw [spentE_nil (a := ⟨b.place, 0⟩) ahead, hs]; rfl)
      (by rw [carryE_nil (a := ⟨b.place, 0⟩) ahead, hc]; rfl) default
    refine ⟨default, (c, ()), ?_⟩
    unfold lendRow
    rw [hc']
    rfl

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.sidePays_one
