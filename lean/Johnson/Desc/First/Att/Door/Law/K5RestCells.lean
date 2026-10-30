-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestCells.lean: kind K5: THE FIELD cells OF K5Rest (K5AtMgPaid.lean), AT THE COMPOSED MEANING's CLOSED CONSTANT AND THE PICK Zof := zofAll h g (K5RestIdn.lean), UNDER THREE CONDITIONS ON PUBLIC DATA.


Main names:
  `PadsAll h`: ONCE PER HEAD: PlacesOffPad (Johnson/P5J/HidBears.lean) at the constant's letters: every place that a segment's seats name is off the pad of the segment's own copy. (Its test with code:
    Johnson/P5J/PlacesOffPadC.lean. It reads no kind. OwnNamed (Johnson/Desc/First/Look/K3CopiesRead.lean) at a segment is SeatsNamed's and this sentence's clauses at that segment: K5CellsAny.lean's ownNamed_of_places; cells_any takes OwnNamed at segments 2 g + 1 and 2 g alone.)
  `K5CellsCond h a x₁ idx`: PER GROUP: tie · one: THE LOOKUP ARGUMENT's OWN LEDGER's FIELDS (AttOwedR, Johnson/Desc/Sound/MgAt/K3Owed.lean), TEXT FOR TEXT at Dm := h.𝔇 · num := At.num Zp · tls := Meaning.tlAt (At.X Zp) · tl := a.seam.tl.
  `cells_all`: **the field**, from PadsAll h and ∃ idx, K5CellsCond h a x₁ idx.
  `syms_of_tie`: SymsOK (the unpaid half of K5Rest's field tiePub) FROM tie ALONE: its field keptSame is the law kept_same (Johnson/Desc/First/Att/K05KeptSame.lean); its field seated is what seat_of_tie (Johnson/Goal/Meaning/ReadingsOne.lean) concludes. `tiePubCells_all`: so tiePub is whole
    under ∃ idx, K5CellsCond h a x₁ idx.
WHERE idx STANDS: UNDER ∃, BEHIND g (a · x₁ are the group's): A LETTER OF EACH SEGMENT. With one idx for all segments tie cannot hold at two segments (printed at the public files of another build). The closed term
idxAt D num (2 g + 1) (Look/K3IdxAt.lean) is the meant witness.
Is it empty here? THE THREE CONDITIONS ARE SHOWN AT NOTHING. An idx can exist only where At.num Zp gives two numbers to two messages of the segment's list: numOfPlan gives EVERY KEY THAT IS ABSENT from the plan's seats ONE number: two
messages of the segment without a seat would collide and no idx would serve. None of the three is named by the head; none has run at the constant's letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5CellsAny
import Johnson.Desc.First.Att.Door.Law.K5RestIdn
import Johnson.Desc.First.Att.Door.Law.K5RestPublic
import Johnson.Desc.First.Att.K05KeptSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls CellsAre)
open VerifiableInference.OnPublicFiles (OneNumber)
open VerifiableInference.Desc.First.Att.P (SymsOK TiePub kept_same)
open P5J (AtMgA mgAtAll TS)

/-- **SymsOK from the link's tie alone.** -/
theorem syms_of_tie {X : Verify.Public} {D : Look.Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {x : Look.Place} {tl : HTailF2}
    (T : _root_.Meaning.linkTieB X D rad num idx x.link tl = true) : SymsOK x tl D rad :=
  ⟨fun k hk => kept_same D x.link k hk,
    fun μ i' c => ⟨_, (_root_.Meaning.seat_of_tie T μ.isLt i'.isLt c.isLt).1, (_root_.Meaning.seat_of_tie T μ.isLt i'.isLt c.isLt).2⟩⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- **Once per head: every place that a segment's seats name is off the pad of the segment's own copy.** -/
def PadsAll : Prop :=
  P5J.PlacesOffPad h.𝔇.sent.codes h.𝔇.arr h.𝔇.ms h.𝔇.N (_root_.Meaning.sizesOf (P5J.At.X Zp))
    (_root_.Meaning.seatBy (_root_.Meaning.fLay h.𝔇.sent.layout (P5J.At.num Zp)) (P5J.At.X Zp) (_root_.Meaning.sizesOf (P5J.At.X Zp)))

/-- **Per group: two fields of the lookup argument's own ledger.** -/
structure K5CellsCond (a : Attention.Plan) (x₁ : Look.Place) (idx : ℕ → ℕ) : Prop where
  /-- test on the public parameters and the layout -/
  tie : _root_.Meaning.linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true
  /-- test on the list of rounds: a member's number is its label's; no pad's place -/
  one : OneNumber (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx (_root_.Meaning.tlAt (P5J.At.X Zp)) x₁.link
    (fun j : Fin (sigListCalls h.𝔇.sent h.𝔇.rad3 x₁.link).length => h.𝔇.seat3 x₁.link false j.1) h.𝔇.arr id

/-- **The field cells.** -/
theorem cells_all (hO : PadsAll h) {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (C : ∃ idx, K5CellsCond h a x₁ idx) :
    ∀ w, h.𝔇.H.base (2 * g + 1) w →
      CellsAre x₁ a.S a.seam.tl h.𝔇.sent h.𝔇.l3.rad
        (msgsOf h.𝔇.sent.codes (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link) (seatAll h x₁) h.𝔇.arr w) (zofAll h g w) := by
  obtain ⟨idx, C⟩ := C
  exact cells_any h.scope h.reads h.pubOne h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) P5J.tokVOf _ _ h.plan.hN h.plan.hG hg ha hx
    h.𝔇.l3.rad idx (seatAll h x₁) C.tie C.one (ownNamed_of_places h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) h.plan.hN hO x₁.link)
    (ownNamed_of_places h.𝔇.sent h.𝔇.arr h.𝔇.ms h.𝔇.N (P5J.At.num Zp) h.plan.hN hO (2 * g))

/-- **tiePub, whole, under the conditions of the field cells.** -/
theorem tiePubCells_all {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {x₁ : Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (C : ∃ idx, K5CellsCond h a x₁ idx) :
    TiePub h.𝔇.sent x₁ a.seam.tl a.ns h.𝔇.l3.rad := by
  obtain ⟨idx, C⟩ := C
  exact tiePub_all h hg ha hx (syms_of_tie C.tie)

end

end H2K5.Door

#print axioms H2K5.Door.syms_of_tie
#print axioms H2K5.Door.tiePubCells_all
#print axioms H2K5.Door.cells_all
