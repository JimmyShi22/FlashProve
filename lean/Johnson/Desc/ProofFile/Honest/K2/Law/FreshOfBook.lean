-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshOfBook.lean: the kind "the code switch" (K2): UNDER THE
LIBRARY's HEAD AND THE OPENING, AT EACH SWITCH OF THE PLAN, AT THE LETTERS AT WHICH THE KIND's LOT
OF ROWS LAYS ITS ROW: FROM THE ONE PREMISE book (the kind's public test on the book, for every
address) TO ALL EIGHT PREMISES `FreshAsks` AND TO THE STATEMENT's END `FreshOf`: the copy, letter
for letter, of the field fresh of the frame's `Good` (Honest/K2/Fresh.lean). Two laws: joins of
calls. No definition; nothing is evaluated here.

  `freshAsks_of_book`   seated · blocks · two · fits · seeds · oneRow by `freshAsks_of_two`
                    (Honest/K2/Law/FreshSixAtHead.lean) · sendFresh by `sendFresh_open`
                    (Honest/K2/Law/BookFromFits.lean)
  `freshOf_of_book`   then the implication `switchFresh` (Honest/K2/Law/FreshAtProof.lean)

Limits. hbook IS A PREMISE: SHOWN OF NO BOOK HERE. THE END IS A LAW OVER COINS: an equation of two
laws of chance over the part's uniform coins; it is as good as `sendFresh_open`, which is as good as
another writer's theorem on the shared sending's rows (Honest/K2/Law/AtCore.lean calls it). The book
and the order are free letters: whoever uses the sentence lays the description's own. D, readers,
ok, fs stay free letters. That the side σ is the one that the frame seats is said by its first limb
alone. Of the files named in this head Honest/K2/Fresh.lean alone is sealed. All limits of the files
named stand. The full size and the format's second hash function alone. THE HEAD AND THE OPENING ARE
HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING MEETS THEM THE LAWS THAT NAME THEM
HOLD EMPTILY. Nothing here says what the statement would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshSixAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.BookFromFits
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshAtProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain Place Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Xi Tr X : Type}

/-- **FROM book TO ALL EIGHT PREMISES.** -/
theorem freshAsks_of_book (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (ok : Xi → Bool) (fs : List (Fall TS)) {Bk : ProverCoinCounts} {ord : List Place}
    (hbook : ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
      (Bk.knownBy ord ⟨p.place, 0⟩ q) = true) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      FreshAsks (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok
        (roundsAt Zp Bs.G₀ p.place) cF.blocksInOrder fs σ Bk ord :=
  freshAsks_of_two h O hp D readers ok fs hbook fun q => sendFresh_open O p hp Bk ord q

/-- **FROM book TO THE STATEMENT's END**, at the side that `Side.seated` lays at the place. A law
over coins. -/
theorem freshOf_of_book (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (ok : Xi → Bool) (fs : List (Fall TS)) {Bk : ProverCoinCounts} {ord : List Place}
    (hbook : ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
      (Bk.knownBy ord ⟨p.place, 0⟩ q) = true) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      Side.seated cF.blocksInOrder p.place (switchRow (coreSender freshTable) D readers
                 (lotClosing Zp Bs.G₀) p ok (roundsAt Zp Bs.G₀ p.place)) fs = some σ ∧
      FreshOf σ Bk ord (switchBud p) := by
  obtain ⟨σ, A⟩ := freshAsks_of_book (X := X) h O hp D readers ok fs hbook
  exact ⟨σ, A.seated, Law.switchFresh _ _ _ _ _ _ _ _ _ _ _ _ A⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.freshAsks_of_book
#print axioms ProofFile.Honest.K2.Law.freshOf_of_book
