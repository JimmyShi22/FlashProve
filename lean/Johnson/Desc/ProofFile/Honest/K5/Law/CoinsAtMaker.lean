-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/CoinsAtMaker.lean: of the coins of the attention segments' own
rounds (kind K5: the label of that sub-protocol in the description) at the book that the maker
returns: every entry handed to a part of the kind is a spent one; and, where the lending to a row
returns, each member of its side gets its carried blocks.

  carried_of_lendRow  general: where the lending to a list of parts returns, the lending to each
                      member returns, so its carried blocks are there
  carried_at_seated   general: the same at the side that Side.seated makes of a row
  k5_row_place        conditional: h; hG: a row of the lot stands at one of the twelve places
  k5_spent_at_group   conditional: h; hA: at each of the twelve groups
  k5_spent_at_rows    conditional: h; hA: at every row of the lot, at the public part and the ground
                      that the maker returns

Limits. h, the library's head, is a hypothesis: that it can be met is not shown here. hA: the maker
returns at the filling P. P is a free variable, and that the maker returns at any filling is not
shown here. Where the lot has no row the last theorem says nothing: that it has twelve is
k5_lot_not_empty_at_return (Honest/K5/Law/LotNotEmptyAtMaker.lean). carried_at_seated has the
lending's return as a premise. On public data alone: names of rounds, places, counts. What is lent is
not said. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnsNothingAtMaker
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Oracle Place)
open P5J (AtMgA TS)

/-! ## 1 Carried blocks, from the lending to a row -/

section
variable {S Cl V W Y Pb : Type}

/-- **Where the lending to a list of parts returns, each member has its carried blocks.** -/
theorem carried_of_lendRow {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} : ∀ (l : List (Part V W Y × Sim Pb)) (j : Nat)
      (rs : List (Fmt.DeclaredRound × List Oracle)),
      (∃ c, lendRow B rows look a (l.map (·.1)) j = .ok c) →
      ∀ u ∈ membersOf l j rs, ∃ ca, (lendPart B rows look ⟨a, u.number⟩ u.part).map (·.2.2) = .ok ca
  | [], _, _, _, u, hu => by cases hu
  | x :: l, j, rs, ⟨c, hc⟩, u, hu => by
    obtain ⟨h1, h2⟩ := lendRow_cons_ok (p := x.1) (ps := l.map (·.1)) hc
    rcases List.mem_cons.1 hu with rfl | hu
    · refine ⟨c.1.2.2, ?_⟩
      show (lendPart B rows look ⟨a, j⟩ x.1).map (·.2.2) = _
      rw [h1]
      rfl
    · exact carried_of_lendRow l (j + 1) _ ⟨c.2, h2⟩ u hu

/-- **The same at the side that Side.seated makes of a row.** Conditional: hσ; hl: the lending to the
row returns at the coins k. -/
theorem carried_at_seated {bs : List (VerifiableInference.Desc.Block S Cl)}
    {r : Unlettered V W Y Pb} {fs : List (Fall S)} {σ : Side S Cl V W Y Pb}
    (hσ : Side.seated bs r.place r.row fs = some σ) {B : ProverCoinCounts} {k : Coins B}
    (hl : ∃ c, lendRow B (B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c) :
    ∀ u ∈ σ.members, ∃ ca, carriedAt B k 0 ⟨r.place, u.number⟩ u.part = .ok ca := by
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ
  intro u hu
  exact carried_of_lendRow r.row 0 _ hl u hu

end

/-! ## 2 Every entry handed to a part of the kind is a spent one -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT EACH OF THE TWELVE GROUPS EVERY ENTRY OF THE BOOK THAT THE MAKER RETURNS WHOSE SPENDER STANDS
AT THE GROUP's PLACE OF THE KIND IS A SPENT ONE.** CONDITIONAL: h; hA: the maker returns A at a filling
P, P a free variable. -/
theorem k5_spent_at_group (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ e ∈ A.B.ahead, e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ → e.once = true := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := m.book
  rw [eF] at hB
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, -, Dc⟩ := k5_member h hg
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  have hpl : blk.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := Dc.place
  intro e he hs
  exact plain_all_spent hB hp hb (k5_no_seed blk (parAt Zp g a') Dc.rounds)
    (k5_no_fold blk (parAt Zp g a') Dc.rounds) e he (hs.trans hpl.symm)

variable {W₀ Rc Tr X₀ X W₀' Rc' Tr' X' Xi Pb : Type}

/-- **A row of the lot stands at the place of the kind of one of the twelve groups.** CONDITIONAL: h;
hG. -/
theorem k5_row_place (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr' → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀' Rc' Xi Tr' X' Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) :
    ∃ g, g < 12 ∧ r.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hl, -⟩ := seat_facts hY
  refine ⟨g, List.mem_range.1 hg, ?_⟩
  show (⟨1, some Y.link, 3, .K5⟩ : Place) = _
  rw [hl]

/-- **AT EVERY ROW OF THE LOT EVERY ENTRY OF THE BOOK THAT THE MAKER RETURNS WHOSE SPENDER STANDS AT
THE ROW's PLACE IS A SPENT ONE.** WHERE THE LOT HAS NO ROW NOTHING IS SAID. CONDITIONAL: h; hA. -/
theorem k5_spent_at_rows (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    ∀ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOf).rows A.Z A.G,
      ∀ e ∈ A.B.ahead, e.spender.place = r.place → e.once = true := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ]
  intro r hr e he hs
  obtain ⟨g, hg, ep⟩ := k5_row_place h hG hr
  exact k5_spent_at_group h hg hA e he (hs.trans ep)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.carried_of_lendRow
#print axioms ProofFile.Honest.K5.carried_at_seated
#print axioms ProofFile.Honest.K5.k5_row_place
#print axioms ProofFile.Honest.K5.k5_spent_at_group
#print axioms ProofFile.Honest.K5.k5_spent_at_rows
