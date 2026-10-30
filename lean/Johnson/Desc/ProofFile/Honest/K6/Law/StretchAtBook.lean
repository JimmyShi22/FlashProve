-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/StretchAtBook.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
UNDER THE HYPOTHESIS h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) AND "THE MAKER OF THE WHOLE BOOK OF
COINS RETURNS": WHAT K6's ROW OF PARTS SPENDS IS ONE STRETCH OF THE COINS OF THE SENDER OF LINK 24's
MASK ROW: THE TEXT OF THE FIELD stretch OF `K6HeadBelow` (Honest/K6/Law/ScriptBelowFree.lean), at
o := row.owner, base := row.base.e, cnt := takesOf …, row being what the book's maker finds as that
mask row's owner. No definition; three theorems.

  `k6_stretch_at_book`     under h and hB: `bookWhole` returns Bk at the head's own description, at
                           any three lists of sendings, at the merges that `onlineProverFromPublicFiles` lays
  `k6_book_of_atPure`      GENERAL: where `onlineProverFromPublicFiles` returns A, A.B is what `bookWhole` returns at A.F
  `k6_stretch_at_atPure`   under h and hA: `onlineProverFromPublicFiles` returns A at the head's own files, at any
                           filling: the same at A.B: THE BOOK OF THE PROVER THAT THE FRAME's MAKER
                           RETURNS

By. `bookWhole_row_stretch` (Honest/BookRowStretch.lean), of the book's authors: its eight binders
are met by: hB; `k6_placesOk_at_head`, `k6_elems_at_head` (Honest/K6/Law/WindowNumbers.lean);
`k6_stretch_numbers` (Honest/K6/Law/StretchNumbers.lean); `k6_member_there`, `k6_front_scalars`
(Honest/K6/Law/FrontScalars.lean). `atPure_ok` (Honest/AtPureLaw.lean) and the head's field
laid.value make A.F the head's own description.

What it is not.
  * **WHICH ADDRESS row.owner IS, AND WHICH NUMBER row.base.e IS, IS NOT SAID.** They are what the
    book's maker's `ownerOf` finds at the sending "link 24, moment 0" (`addrOfRound`, `maskStart`:
    Honest/BookEntries.lean). That they are the code switch's own address and the count at which the
    switch's authors lay that message's mask entries among the sending's coins is said by nothing.
  * hB | hA ARE PREMISES: that the maker returns at any files is not shown here.
  * row stands under "there is", tied by `ownerOf`'s equation; in the third theorem the list of
    sendings too.
  * That this stretch lies apart from what another sub-protocol spends of the same row: not here.
  * h: the full size and the format's second hash function alone.
  * Public data alone: a book is a table of entries: nothing on a coin's value or on a run.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K6.Law.FrontScalars
import Johnson.Desc.ProofFile.Honest.K6.Law.StretchNumbers
import Johnson.Desc.ProofFile.Honest.K6.Law.WindowNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Kinds (Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf takesOf)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type}

/-- CONDITIONAL: h; hB. **THE TEXT OF THE FIELD stretch, AT THE BOOK THAT THE MAKER RETURNS.** The
sending's label is "link 24, moment 0", spelt as the book's authors spell it. -/
theorem k6_stretch_at_book (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {p0 p1 p2 : Johnson.G.ChainSends} {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok Bk)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    ∃ row, ownerOf maskRowRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {24}, moment 0" isMaskRowMsg = some row ∧
      oneStretch (rowEntries Bk IM.k6Place (headRow (X := X) wit
        (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length 0) =
        some (row.owner, row.base.e + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs,
          takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) := by
  obtain ⟨b, hb, hp⟩ := k6_member_there h
  obtain ⟨n1, n2, n3, n4, n5⟩ := k6_stretch_numbers (X := X) h wit hb hp
  obtain ⟨row, hrow, hst⟩ := bookWhole_row_stretch (F := P5J.F0T OnBytes.secondHashFunction Zp Np cF) hB
    (k6_placesOk_at_head h) (b := b) hb (l := 24) (congrArg Place.link hp) n3 n4 n5
  refine ⟨row, hrow, ?_⟩
  have e2 : ownScalarsOf (planParts b) =
      takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) := n2
  have e3 : ownScalarsOf (partsInFront cF.blocksInOrder 24 b.place) =
      OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs := by
    rw [hp, k6_elems_at_head h]
    exact k6_front_scalars h
  -- the same sentence, with the description's own types and first chain unfolded
  have hst' : oneStretch (rowEntries Bk b.place (planParts b).length 0) =
      some (row.owner, row.base.e + ownScalarsOf (partsInFront cF.blocksInOrder 24 b.place),
        ownScalarsOf (planParts b)) := hst
  rw [e2, e3, n1, hp] at hst'
  exact hst'

/-- GENERAL. Where the frame's maker returns A, A.B is what the whole book's maker returns at A.F,
at three of the library's lists of sendings and the merges by name. -/
theorem k6_book_of_atPure {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ p0 p1 p2, bookWhole A.F p0 p1 p2 (mergesByName A.F.first.blocksInOrder) = .ok A.B := by
  unfold onlineProverFromPublicFiles at hA
  obtain ⟨Z', _, hA⟩ := bind_ok hA
  obtain ⟨G, _, hA⟩ := bind_ok hA
  obtain ⟨F, _, hA⟩ := bind_ok hA
  obtain ⟨cs, _, hA⟩ := bind_ok hA
  split at hA
  · obtain ⟨B, hB, hA⟩ := bind_ok hA
    dsimp only at hA
    split at hA
    · cases hA
    · split at hA
      · cases hA
      · cases hA
        exact ⟨_, _, _, hB⟩
  · cases hA

/-- CONDITIONAL: h; hA. **THE SAME AT THE BOOK OF THE PROVER THAT THE FRAME's MAKER RETURNS** at the
head's own files, at any filling P. -/
theorem k6_stretch_at_atPure (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) :
    ∃ p0 row, ownerOf maskRowRun cF.blocksInOrder p0
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds))
        s!"link {24}, moment 0" isMaskRowMsg = some row ∧
      oneStretch (rowEntries A.B IM.k6Place (headRow (X := X) wit
        (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) IM.k6Place).length 0) =
        some (row.owner, row.base.e + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs,
          takesOf (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp)))) := by
  obtain ⟨p0, p1, p2, hB⟩ := k6_book_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
    Except.ok.inj ((atPure_ok hA).2.2.1.symm.trans h.laid.value)
  rw [eF] at hB
  obtain ⟨row, h1, h2⟩ := k6_stretch_at_book (X := X) h hB wit
  exact ⟨p0, row, h1, h2⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_stretch_at_book
#print axioms ProofFile.Honest.K6.k6_book_of_atPure
#print axioms ProofFile.Honest.K6.k6_stretch_at_atPure
