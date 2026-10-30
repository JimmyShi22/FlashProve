-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionBookAtAFilling.lean: what the book of coins says of the
attention segments' own rounds (kind K5: the label of that sub-protocol in the description) at a return
of the maker at any filling that lays the code switch's lot. The index and the pads' types are free
variables, so this serves at every filling of that form, with no reading through in its text.

  ownersOfReturn      whose coins the rows spend: the owners' addresses, read off the book
  AttentionBookAt     what is stated of the book at a return of the maker: seven fields
  LaysTheSwitch       of a filling: at each public part and ground, at each place of the code switch's
                      list, one of its lots has a side there with a part
  written_switch_places, written_switch_places_bite   a closed fact: the switch's written list has a
                      member at piece 1 of each of the twelve odd links; at piece 2 of none of them
  switchHalves_has    the switch's half at a place of its list stands there, with a part
  owner_sides_at      conditional: h; hA; hP: a side with a part stands in the prover's first list at
                      piece 1 of each of the twelve odd links
  attention_book_at   conditional: h; hA; hP: the structure
  attention_switches_at   conditional: h; hA: each owner is of the kind K2, at any filling
  owners_not_empty_at conditional: h; hA: the list of owners has a member

Limits. h, the library's head, is a hypothesis, and so is that the maker returns. LaysTheSwitch is a
premise here: it pins places and parts, not what the switch sends; it is shown at the filling that
the online filling reads through (E2E/AttentionBookAtBase.lean). The book is read for names, places
and counts: nothing here says what the owners' coins are. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionAtAFilling
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnersAtMaker
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open P5J (AtMgA TS)

variable {W₀ Rc X₀ X : Type}

/-- **Whose coins the rows spend**: the owners' addresses, read off the book. -/
def ownersOfReturn (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) : List Addr :=
  (A.B.ahead.filter fun e => (rowsOfReturn A).any fun r => r.place == e.spender.place).map (·.owner)

/-- **The book at a return of the maker.** -/
structure AttentionBookAt (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) : Prop where
  /-- the book is the maker's, and it passes its own tests at the description -/
  book : A.B.word A.F = none
  /-- no entry of the book has its owner at a row's place -/
  ownsNothing : ∀ r ∈ rowsOfReturn A, ∀ e ∈ A.B.ahead, e.owner.place ≠ r.place
  /-- every entry that hands coins to a part of a row marks them as spent -/
  spentOnly : ∀ r ∈ rowsOfReturn A, ∀ e ∈ A.B.ahead, e.spender.place = r.place → e.once = true
  /-- every entry whose spender stands at a place of this kind has it at a row's place -/
  spendersAreRows : ∀ e ∈ A.B.ahead, e.spender.place.kind = .K5 →
    ∃ r ∈ rowsOfReturn A, e.spender.place = r.place
  /-- each owner of coins that this kind spends is a part of a side of the prover -/
  owners : ∀ a ∈ ownersOfReturn A, ∃ h ∈ A.H.first, h.place = a.place ∧ a.part < h.parts.length
  /-- at every run's coins the book lends each row what it spends -/
  lent : ∀ (k : Coins A.B), ∀ r ∈ rowsOfReturn A,
    ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c
  /-- at every run's coins the book gives each member its carried blocks, which are none -/
  carried : ∀ (k : Coins A.B), ∀ r ∈ rowsOfReturn A, ∀ σ,
    Side.seated A.F.first.blocksInOrder r.place r.row [] = some σ → ∀ u ∈ σ.members,
      ∃ ca, carriedAt A.B k 0 ⟨r.place, u.number⟩ u.part = .ok ca

/-- **At each place of the switch's list one of the filling's lots has a side with a part.** What a
side sends is not read. -/
def LaysTheSwitch (P : OnlineProverParts W₀ Rc Cells X₀ X) : Prop :=
  ∀ Z G, ∀ p ∈ K2.switchPlaces Z G, ∃ L ∈ P.lots, ∃ y ∈ L.halves Z G, y.place = p.place ∧ y.parts ≠ []

set_option maxRecDepth 1000000 in
/-- **The switch's written list has a member at piece 1 of each of the twelve odd links.** A closed
fact. Kin: placesW_one (Honest/K2/Law/PlacesCount.lean) says at each link just one, at switchPlaceAt. -/
theorem written_switch_places : ((List.range 12).all fun g =>
    K2.Law.placesW.any fun p => p.place == ⟨1, some (2 * g + 1), 1, .K2⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At piece 2 of none of them. A closed fact: the test is not idle. -/
theorem written_switch_places_bite : ((List.range 12).any fun g =>
    K2.Law.placesW.any fun p => p.place == ⟨1, some (2 * g + 1), 2, .K2⟩) = false := by
  decide +kernel

/-- The switch's half at a place of its list stands there, with a part. -/
theorem switchHalves_has {Xi Tr : Type} (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (p : K2.SwitchPlace) (hp : p ∈ K2.switchPlaces Z G) :
    ∃ x ∈ K2.switchHalves (X := X) Sd D readers closing Z G, x.place = p.place ∧ x.parts ≠ [] :=
  ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, rfl, List.cons_ne_nil _ _⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A SIDE WITH A PART STANDS IN THE PROVER's FIRST LIST AT PIECE 1 OF EACH OF THE TWELVE ODD LINKS.**
CONDITIONAL: h; hA; hP. -/
theorem owner_sides_at (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {P : OnlineProverParts W₀ Rc Cells X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Cells X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hP : LaysTheSwitch P) :
    ∀ g, g < 12 → ∃ s ∈ A.H.first, s.place = ⟨1, some (2 * g + 1), 1, .K2⟩ ∧ s.parts ≠ [] := by
  intro g hg
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  have eG : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans O.blank)
  obtain ⟨p, hp, ep⟩ := List.any_eq_true.1
    (List.all_eq_true.1 written_switch_places g (List.mem_range.2 hg))
  have hp' : p ∈ K2.switchPlaces A.Z A.G := by
    rw [eZ, eG, K2.Law.places_at_head h.toAtMg O]
    exact hp
  obtain ⟨L, hL, y, hy, e1, e2⟩ := hP A.Z A.G p hp'
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  refine ⟨y, ?_, e1.trans (beq_iff_eq.1 ep), e2⟩
  rw [eH1]
  exact List.mem_flatMap.2 ⟨L, hL, hy⟩

/-- **THE BOOK AT A RETURN OF THE MAKER.** CONDITIONAL: h; hA; hP. -/
theorem attention_book_at (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {P : OnlineProverParts W₀ Rc Cells X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Cells X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hP : LaysTheSwitch P) : AttentionBookAt A := by
  have eZ : A.Z = Zp := Except.ok.inj ((parts_of_atPure hA).1.pub.symm.trans h.laid.pub)
  have hl : ∀ (k : Coins A.B), ∀ r ∈ rowsOfReturn A,
      ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c := by
    intro k r hr
    have hr' : r ∈ (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) (Pb := ProofFile.Inst) id
        keyOfK3).rows Zp A.G := eZ ▸ hr
    exact k5_lent_at_rows h hA id k r hr'
  exact
    { book := (atPure_tests hA).1
      ownsNothing := k5_owns_nothing_at_rows h hA id keyOfK3
      spentOnly := k5_spent_at_rows h hA id keyOfK3
      spendersAreRows := fun e he hk => (k5_spender_kind_iff_rows h hA id e he).1 hk
      owners := k5_owners_of_sides h hA id keyOfK3 (owner_sides_at h hA hP)
      lent := hl
      carried := fun k r hr _ hσ => carried_at_seated hσ (hl k r hr) }

/-- **Each owner of what the rows spend is of the kind K2.** CONDITIONAL: h; hA. -/
theorem attention_switches_at (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ a ∈ ownersOfReturn A, a.place.kind = .K2 :=
  k5_owners_are_switches h hA id keyOfK3

/-- **The list of owners has a member.** CONDITIONAL: h; hA. -/
theorem owners_not_empty_at (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) : ownersOfReturn A ≠ [] := by
  obtain ⟨e, he, es⟩ := k5_spender_at_maker h (g := 0) (by omega) hA
  obtain ⟨r, hr, er⟩ := (k5_spender_kind_iff_rows h hA id e he).1 (by rw [es])
  intro h0
  have hm : e.owner ∈ ownersOfReturn A :=
    List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, List.any_eq_true.2 ⟨r, hr, beq_iff_eq.2 er.symm⟩⟩, rfl⟩
  rw [h0] at hm
  cases hm

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.written_switch_places
#print axioms ProofFile.Honest.K5.written_switch_places_bite
#print axioms ProofFile.Honest.K5.switchHalves_has
#print axioms ProofFile.Honest.K5.owner_sides_at
#print axioms ProofFile.Honest.K5.attention_book_at
#print axioms ProofFile.Honest.K5.attention_switches_at
#print axioms ProofFile.Honest.K5.owners_not_empty_at
