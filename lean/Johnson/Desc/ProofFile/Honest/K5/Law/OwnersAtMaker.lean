-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OwnersAtMaker.lean: at the book that the maker returns, row by
row, the entries and the attention segments' own rounds (kind K5: the label of that sub-protocol in the
description): a spender of the kind stands at a row's place, no entry is owned there, and each owner of
what the rows spend is a code switch at one of the twelve links (which owner belongs to which spender
is k5_owner_address, Honest/K5/Law/OwnerKindAtMaker.lean); and, if a side with a part stands at each of
these twelve places, each such owner is a part of a side of the prover.

  spender_in_order    a book that passes its tests has every entry's spender at a place of the
                      description
  k5_spender_of_kind  conditional: h; hA: a spender of the kind stands at one of the twelve groups
  k5_spender_kind_iff_rows   conditional: h; hA: at keyOfK3 a spender is of the kind just where it
                      stands at a row's place: the two ways of sorting the entries are one
  k5_owns_nothing_at_rows   conditional: h; hA: no entry has its owner at a row's place
  k5_owners_at_rows   conditional: h; hA: each owner of what the rows spend is the switch's part 0 at
                      one of the twelve links
  k5_owners_are_switches    conditional: h; hA: so each such owner is of the kind K2
  k5_owners_of_sides  conditional: h; hA; hS: each such owner is a part of a side of the prover

The premise hS. A side with a part stands in the prover's first list at piece 1 of each of the twelve
odd links. It is a fact on the filling, not shown here: at a filling without the code switch's lot it
can be false.

Limits. h, the library's head, is a hypothesis: that it can be met is not shown here. hA: the maker
returns at the filling P, a free variable. Where the lot has no row the statements on rows say
nothing: that it has twelve is k5_lot_not_empty_at_return (Honest/K5/Law/LotNotEmptyAtMaker.lean).
What the owner's side does is not said: nothing here says that the owner's coins are uniform or that
they are used once. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.LotNotEmptyAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.KindFivePlaces
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnerKindAtMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X W₀' Rc' Tr' X' Xi Pb : Type}

/-- **A book that passes its tests has every entry's spender at a place of the description.** -/
theorem spender_in_order {Yi : Type} {F : VerifiableInference.Desc.FileDescription Yi} {B : ProverCoinCounts}
    (hw : B.word F = none) : ∀ e ∈ B.ahead, e.spender.place ∈ orderOf F := by
  have t := ProverCoinCounts.tests hw
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, t5, -⟩ := t
  intro e he
  have := List.all_eq_true.1 t5 e he
  simp only [Bool.and_eq_true] at this
  exact List.contains_iff_mem.1 this.1.2

/-- **A SPENDER OF THE KIND STANDS AT ONE OF THE TWELVE GROUPS.** CONDITIONAL: h; hA. -/
theorem k5_spender_of_kind (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender.place.kind = .K5 →
      ∃ g, g < 12 ∧ e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := m.book
  rw [eF] at hB
  intro e he hk
  have hm := spender_in_order (bookWhole_word hB) e he
  unfold orderOf at hm
  rcases List.mem_append.1 hm with hm | hm
  · rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨blk, hb, ep⟩ := List.mem_map.1 hm
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hb
      have hj' : cF.blocksInOrder[j]? = some blk := hj
      obtain ⟨g, hg, rfl⟩ := kindFive_only_at_borders h hj' (by rw [ep]; exact hk)
      obtain ⟨blk', a', hm', -, Dc⟩ := k5_member h hg
      obtain rfl : blk' = blk := Option.some.inj (hm'.symm.trans hj')
      refine ⟨g, hg, ?_⟩
      rw [← ep]
      exact Dc.place
    · obtain ⟨blk, hb, ep⟩ := List.mem_map.1 hm
      exact absurd (ep ▸ hk) (kindFive_not_in_shared h blk hb)
  · obtain ⟨blk, hb, ep⟩ := List.mem_map.1 hm
    exact absurd (ep ▸ hk) (kindFive_not_in_second h blk hb)

/-- **AT keyOfK3 A SPENDER IS OF THE KIND JUST WHERE IT STANDS AT A ROW's PLACE.** CONDITIONAL: h; hA. -/
theorem k5_spender_kind_iff_rows (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells) :
    ∀ e ∈ A.B.ahead, e.spender.place.kind = .K5 ↔
      ∃ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells
        keyOfK3).rows A.Z A.G, e.spender.place = r.place := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ]
  intro e he
  constructor
  · intro hk
    obtain ⟨g, hg, ep⟩ := k5_spender_of_kind h hA e he hk
    have hp := k5_rows_places (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) h hG cells
      (keysFitAll_K3 h hG)
    have hmem : e.spender.place ∈ (List.range 12).map
        fun g => (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) :=
      List.mem_map.2 ⟨g, List.mem_range.2 hg, ep.symm⟩
    rw [← hp] at hmem
    obtain ⟨r, hr, er⟩ := List.mem_map.1 hmem
    exact ⟨r, hr, er.symm⟩
  · rintro ⟨r, hr, ep⟩
    obtain ⟨_, _, Y, _, rfl⟩ := row_of_lot hr
    rw [ep]
    rfl

/-- **NO ENTRY OF THE BOOK THAT THE MAKER RETURNS HAS ITS OWNER AT A ROW's PLACE.** WHERE THE LOT HAS NO
ROW NOTHING IS SAID. CONDITIONAL: h; hA. -/
theorem k5_owns_nothing_at_rows (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    ∀ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z A.G,
      ∀ e ∈ A.B.ahead, e.owner.place ≠ r.place := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ]
  intro r hr e he
  obtain ⟨g, hg, ep⟩ := k5_row_place h hG hr
  rw [ep]
  exact k5_owner_elsewhere h hg hA e he

/-- **EACH OWNER OF WHAT THE ROWS SPEND IS THE SWITCH's PART 0 AT ONE OF THE TWELVE LINKS.** CONDITIONAL:
h; hA. -/
theorem k5_owners_at_rows (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    ∀ a ∈ (A.B.ahead.filter fun e =>
        ((k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z
          A.G).any fun r => r.place == e.spender.place).map (·.owner),
      ∃ g, g < 12 ∧ a = ⟨⟨1, some (2 * g + 1), 1, .K2⟩, 0⟩ := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ]
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
  obtain ⟨he1, he2⟩ := List.mem_filter.1 he
  obtain ⟨r, hr, er⟩ := List.any_eq_true.1 he2
  obtain ⟨g, hg, ep⟩ := k5_row_place h hG hr
  have es : e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := (beq_iff_eq.1 er).symm.trans ep
  exact ⟨g, hg, k5_owner_address h hg hA e he1 es⟩

/-- **SO EACH SUCH OWNER IS OF THE KIND K2.** CONDITIONAL: h; hA. -/
theorem k5_owners_are_switches (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    ∀ a ∈ (A.B.ahead.filter fun e =>
        ((k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z
          A.G).any fun r => r.place == e.spender.place).map (·.owner),
      a.place.kind = .K2 := by
  intro a ha
  obtain ⟨g, -, rfl⟩ := k5_owners_at_rows h hA cells keyOf a ha
  rfl

/-- **EACH SUCH OWNER IS A PART OF A SIDE OF THE PROVER.** CONDITIONAL: h; hA; hS: a side with a part
stands in the prover's first list at piece 1 of each of the twelve odd links. -/
theorem k5_owners_of_sides (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E))
    (hS : ∀ g, g < 12 → ∃ s ∈ A.H.first, s.place = ⟨1, some (2 * g + 1), 1, .K2⟩ ∧ s.parts ≠ []) :
    ∀ a ∈ (A.B.ahead.filter fun e =>
        ((k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z
          A.G).any fun r => r.place == e.spender.place).map (·.owner),
      ∃ s ∈ A.H.first, s.place = a.place ∧ a.part < s.parts.length := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := k5_owners_at_rows h hA cells keyOf a ha
  obtain ⟨s, hs, ep, hn⟩ := hS g hg
  exact ⟨s, hs, ep, List.length_pos_iff.2 hn⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.spender_in_order
#print axioms ProofFile.Honest.K5.k5_spender_of_kind
#print axioms ProofFile.Honest.K5.k5_spender_kind_iff_rows
#print axioms ProofFile.Honest.K5.k5_owns_nothing_at_rows
#print axioms ProofFile.Honest.K5.k5_owners_at_rows
#print axioms ProofFile.Honest.K5.k5_owners_are_switches
#print axioms ProofFile.Honest.K5.k5_owners_of_sides
