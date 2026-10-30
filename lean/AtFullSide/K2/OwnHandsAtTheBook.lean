-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnHandsAtTheBook.lean: the kind "the code switch" (K2): `own_hands_apart`
(Johnson/Desc/ProofFile/Honest/K2/Law/OwnHandsApart.lean) WITH ITS PREMISES PAID: AT WHATEVER BOOK
bookWhole RETURNS AT F0T, UNDER THE LIBRARY's HEAD AND THE OPENING, ON CHAIN 0, AT EACH SWITCH p OF
THE PLAN: a lens get, put on the run's coins that shows the row at p's own address; at every run's
coins p IS handed, and its own hand is what the lens shows; set at will, p's own hand is what was
set, and what p spends and carries stays; every switch at another place IS handed before and behind,
and its own hand stays; and at EVERY OTHER ADDRESS the cut `K1.lentCut` (Honest/K1/ScriptAt.lean, of
other authors: the shared sending's term for a part's own coins) stays. Then at the written pairs:
the switch in front and the switch behind it stand at two places. It lies in the side library
because it imports files of it. No definition; two closed facts by evaluation in Lean's kernel, each
with a control; lemmas.

  `cut_stays`        at a lens that shows the row at o: the cut at every other address stays
  `place_in_chain`   under the head and the opening a switch's place is one of the first chain's
  `own_hands_at_book`   THE JOIN
  `switchKindW`, `other_kind_stays`   each written place is of the kind K2 (BY LEAN's KERNEL; a
                     control): so at an address of another kind the cut stays: the shared sending's
                     among them
  `pairsApartW`, `own_hands_at_pair`   at each of the written pairs the two places differ (BY LEAN's
                     KERNEL; the control shows that the list has a member and that the test can
                     say no, no more): so the end on another switch speaks at each pair

By: `own_hands_apart` · `handed_at_book` (AtFullSide/K2/HandedAtTheBook.lean) · `bookWhole_word`
(Honest/AtPureLaw.lean), `file_head` (Honest/Law/CoverHeadFile.lean), `RowAt`
(Honest/Law/Rule/LentAt.lean), all three of other authors · `border_block_at_head`
(Honest/K2/Law/SwitchBorders.lean) · `places_at_head` (Honest/K2/Law/PlacesWritten.lean) ·
`copyPairs_mem` (Honest/K2/Law/CopyPairsMem.lean).

Limits. THE OWN HANDS AND THE CUTS AT OTHER ADDRESSES ALONE: of the runs that ANOTHER part spends or
carries nothing is said: of a part that carries a run of p's row these laws do not speak there; THAT
NO OTHER PART IS LENT A RUN OUT OF A KEPT COPY's STRETCH IS NOT SAID. No measure stands in these
laws: they are never quoted as saying that coins are independent or fresh. WHETHER AND WHERE, NOT
WHOSE: all that AtFullSide/K2/HandedAtTheBook.lean says under "WHAT IT IS NOT" stands. Chain 0
alone. That a thread's book is what bookWhole returns at F0T is not said. The full size and the
format's second hash function alone. The head, the opening and the book are premises; that they can be met
is not said. Nothing on any property.
-/
import AtFullSide.K2.HandedAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnHandsApart
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchBorders
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyPairsMem
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.First (S)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace switchPlaces handed switchSent switchFresh sendingDue)
open ProofFile.Honest.K2.Law (placesW places_at_head own_hands_apart border_block_at_head copyPairs
  copyPairs_mem)

/-- At a lens that shows the row at o, the cut at every other address stays. -/
theorem cut_stays {B : ProverCoinCounts} {o : Addr} {t : Nat} {d : Due} {get : Coins B → Cs d}
    {put : Cs d → Coins B → Coins B} (R : RowAt B o t d get put) {a : Addr} (hne : a ≠ o)
    (x : Cs d) (k : Coins B) (ch : Nat) (d' : Due) :
    K1.lentCut (put x k) ch a d' = K1.lentCut k ch a d' := by
  unfold K1.lentCut
  rw [R.other x k ch a hne]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- Under the head and the opening a switch's place is one of the first chain's. -/
theorem place_in_chain (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    p.place ∈ ProofFile.Honest.placesAt (F0T OnBytes.secondHashFunction Zp Np cF) 0 := by
  obtain ⟨blk, hb, e⟩ := border_block_at_head h O hp
  show p.place ∈ cF.blocksInOrder.map (·.place)
  exact List.mem_map.2 ⟨blk, List.mem_of_getElem? hb, e⟩

/-- **THE JOIN: UNDER THE HEAD AND THE OPENING, AT THE BOOK, ON CHAIN 0, AT EACH SWITCH OF THE
PLAN.** THE OWN HANDS AND THE CUTS AT OTHER ADDRESSES ALONE: of the runs that another part spends or
carries nothing is said. No measure stands in this law: it is never quoted as saying that coins are
independent or fresh. -/
theorem own_hands_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∃ (get : Coins B → Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)))
      (put : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) → Coins B → Coins B),
      RowAt B ⟨p.place, 0⟩ 0 _ get put ∧
      (∀ k, ∃ c, handed 0 p k = some c ∧ c.1 = get k) ∧
      (∀ x k, ∃ c, handed 0 p k = some c ∧ handed 0 p (put x k) = some (x, c.2.1, c.2.2)) ∧
      (∀ p' ∈ switchPlaces Zp Bs.G₀, p'.place ≠ p.place → ∀ x k, ∃ c' c'',
        handed 0 p' k = some c' ∧ handed 0 p' (put x k) = some c'' ∧ c''.1 = c'.1) ∧
      ∀ a : Addr, a ≠ ⟨p.place, 0⟩ → ∀ x k ch d',
        K1.lentCut (put x k) ch a d' = K1.lentCut k ch a d' := by
  obtain ⟨c₀, h₀⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp default)
  obtain ⟨get, put, R, h1, h2, h3⟩ := own_hands_apart (bookWhole_word hB)
    (file_head h.toAtMg).2.1 (Or.inl rfl) (place_in_chain h O hp) h₀
  refine ⟨get, put, R, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp k)
    exact ⟨c, hc, h1 k c hc⟩
  · intro x k
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp k)
    exact ⟨c, hc, h2 x k c hc⟩
  · intro p' hp' hne x k
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp' k)
    obtain ⟨c'', e1, e2⟩ := h3 p' hne x k c' hc'
    exact ⟨c', c'', hc', e1, e2⟩
  · intro a hne x k ch d'
    exact cut_stays R hne x k ch d'

set_option maxRecDepth 1000000 in
/-- **Each written place is of the kind K2**; a control: not of the kind K1. -/
theorem switchKindW :
    (placesW.all fun p => p.place.kind == KindName.K2) = true ∧
      (placesW.any fun p => p.place.kind == KindName.K1) = false := by
  decide +kernel

/-- **AN ADDRESS OF ANOTHER KIND IS ANOTHER ADDRESS**: so the last end of `own_hands_at_book` speaks
at each address of the shared sending's. -/
theorem other_kind_stays (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    {a : Addr} (hk : a.place.kind ≠ KindName.K2) : a ≠ ⟨p.place, 0⟩ := by
  rw [places_at_head h.toAtMg O] at hp
  have t := beq_iff_eq.1 (List.all_eq_true.1 switchKindW.1 p hp)
  intro e
  rw [e] at hk
  exact hk t

set_option maxRecDepth 1000000 in
/-- **At each written pair the two places differ**; a control: a place against itself does not. -/
theorem pairsApartW :
    (copyPairs.all fun x => x.1.place != x.2.1.place) = true ∧
      (copyPairs.all fun x => x.1.place != x.1.place) = false := by
  decide +kernel

/-- **AT A WRITTEN PAIR**: x.1: the switch in front; x.2.1: the switch behind it, which keeps
copies. Set x.2.1's own hand at will: x.1 is handed before and behind, and its own hand stays. -/
theorem own_hands_at_pair (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {x : SwitchPlace × SwitchPlace × ProofFile.Honest.K2.SegmentPub} (hx : x ∈ copyPairs) :
    ∃ (get : Coins B → Cs (sendingDue x.2.1.sizes.codes (switchSent x.2.1.sizes x.2.1.others)
        (switchFresh x.2.1.sizes x.2.1.others x.2.1.foldVars)))
      (put : Cs (sendingDue x.2.1.sizes.codes (switchSent x.2.1.sizes x.2.1.others)
        (switchFresh x.2.1.sizes x.2.1.others x.2.1.foldVars)) → Coins B → Coins B),
      (∀ k, ∃ c, handed 0 x.2.1 k = some c ∧ c.1 = get k) ∧
      (∀ y k, ∃ c, handed 0 x.2.1 k = some c ∧
        handed 0 x.2.1 (put y k) = some (y, c.2.1, c.2.2)) ∧
      ∀ y k, ∃ c' c'', handed 0 x.1 k = some c' ∧ handed 0 x.1 (put y k) = some c'' ∧
        c''.1 = c'.1 := by
  obtain ⟨m1, m2, -, -⟩ := copyPairs_mem hx
  rw [← places_at_head h.toAtMg O] at m1 m2
  obtain ⟨get, put, -, h1, h2, h3, -⟩ := own_hands_at_book h O hB m2
  exact ⟨get, put, h1, h2, h3 x.1 m1 (bne_iff_ne.1 (List.all_eq_true.1 pairsApartW.1 x hx))⟩

end AtFullSide.K2

#print axioms AtFullSide.K2.cut_stays
#print axioms AtFullSide.K2.place_in_chain
#print axioms AtFullSide.K2.own_hands_at_book
#print axioms AtFullSide.K2.switchKindW
#print axioms AtFullSide.K2.other_kind_stays
#print axioms AtFullSide.K2.pairsApartW
#print axioms AtFullSide.K2.own_hands_at_pair
