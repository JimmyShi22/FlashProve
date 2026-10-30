-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CarryOf.lean: from the closing of a segment to the exact carry, under named premises on the way
in.

What is proved. **`carryExact_of_close`**: `carryExact Zp arr n a y v` (Johnson/Desc/K2/Honest/Carry/Exact.lean), the
sentence on the witness that the code switch into the next group spends, holds if
  (1) the library's way in and the front are known at the state: `doorZ Zp n a.2 = some t`
      (Johnson/Top/H0/K2Caller/CarryClosed.lean), `frontAt … t = some fx` (Johnson/Top/H0/K2Hears/Long.lean);
  (2) the front's carried single rows are those that a closing returned: `foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)`
      for the row that the batching returns at what "BAT" drew;
  (3) the front's statement has the codes and the shapes of `D.S1 s` (`SameShapes`);
  (4) the premises of `close_claimTrue` (Johnson/Desc/K10/Honest/LeftClaim.lean) hold at the words that the witness
      gives at the front's statement and at the book of the state t that the way in returns
      (`wordsFirst arr fx.st t.book v`); `Padded` is not among them: it is proved here.

  `realRows_same`, `padded_same`   the number of real rows, and so `Padded`, read the shapes alone
  `padded_first`    the witness's words at a statement are 0 on the rows beyond the real ones, at every statement with
                   the same shapes

Limits. (1), (2) and (3) are assumptions: that they hold at the state in front of a code switch of a run is not shown
here. So are all premises of `close_claimTrue` but `Padded`: `CloseBase`; the main code's message length is 2 ^ logEll
(hlen); every row that the test takes in holds of the witness's words (hs); the witness's table at the fresh mask's
message pairs with the coefficients W (hP); the premises on the rounds (hl, hsh, hσ, hR). That the premises can be met
together: CarryToy.lean meets those of `carryExact_behind` (CarryAtLink.lean) at one made-up example, the place's sort
aside: .link stays a premise there. This file's premises follow from those as in the proofs of that theorem and of
`carryExact_at_link`; no theorem states it. The words are made at the front's statement and at the book of the state t
that the way in returns. That, at the state behind the lifted closing, they are the words at the statement and the book
in front of the closing: `words_front` (CarryWords.lean). Of n the sentence and these theorems read the place's sort
alone (`(ProofFile.pAtK2 Zp n).stands`). No premise ties n to the link or the group of the record s. Where Zp has no switch
into group n + 1, `pAtK2` gives `deadP2` (Johnson/Desc/ProofFile/CarryAt.lean), whose sort is .link: there the theorems
at a link (CarryAtLink.lean) hold too, of a place that is none. n is Exact.lean's letter m; gs and Cl stand in no
premise. The Limits of LeftClaim.lean and LeftIs.lean hold of `leftAt` here too. Nothing is said on soundness,
completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.LeftClaim
import Johnson.Desc.K2.Honest.Carry.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy)
open VerifiableInference.Desc.First.Close (Par Rec kind)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.First.K2 (SameShapes)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)
open ProofFile.Honest.K10.Values (keptLen)

/-- The number of real rows reads the shapes alone. -/
theorem realRows_same {S S' : Statement} (h : SameShapes S S') (o : Nat) (part : OnBytes.Part) :
    realRows S' o part = realRows S o part := by
  have e := h.shape o
  unfold realRows
  cases h1 : S'.oracles[o]? <;> cases h2 : S.oracles[o]? <;> simp [h1, h2] at e ⊢
  rw [e]

/-- So does `Padded`. -/
theorem padded_same {S S' : Statement} (h : SameShapes S S') {w : Words GE} (hp : Padded S' w) :
    Padded S w := fun o part i hi =>
  hp o part i (by rw [realRows_same h, h.rowBits]; exact hi)

/-- The witness's words at a statement are 0 on the rows beyond the real ones, at every statement with the same
shapes. -/
theorem padded_first {Cells Tok : Type} {S S' : Statement} (h : SameShapes S S') (arr : ℕ → ℕ → ℕ)
    (book : TreeBook) (v : Wit Cells Tok MsgT) : Padded S (wordsFirst arr S' book v) :=
  padded_same h (padded_wordsOn S' _)

/-- **From the closing to the exact carry.** -/
theorem carryExact_of_close {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (a : Q × First.S) (y : Strs) (v : Wit Cells Tok MsgT) {t : First.S} {fx : _root_.Tw.K2.Front}
    (hd : doorZ Zp n a.2 = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx)
    {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (hsame : SameShapes (D.S1 s) fx.st)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList (wordsFirst arr fx.st t.book v))
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    (hrows : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row → fx.f.rows = foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR))
    (W : HIdx (sVars GE 2 ((stageB D s).h + (stageB D s).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D s).h + (stageB D s).g)))
    (hP : Pairs (stageB D s) (stageB D s).Z.l W (freshB D s (wordsFirst arr fx.st t.book v)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g)) W)
    (hR : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      Shows ((stageB D s).h + (stageB D s).g) rR (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st t.book v))) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st t.book v)).kept row.kept) γ) γ) :
    carryExact Zp arr n a y v := by
  obtain ⟨row, hrow, _, hc⟩ := close_claimTrue (Cl := Cl) H hlen (wordsFirst arr fx.st t.book v) hs
    (padded_first hsame arr t.book v) rB rE rR gs hl hsh W γ hP hσ hR fx.T
  rw [carryExact_iff Zp arr n a y v hd hf, hrows row hrow, sizesAt_same hsame, leftAt_same hsame]
  exact hc

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.realRows_same
#print axioms ProofFile.Honest.K10.LeftIs.padded_same
#print axioms ProofFile.Honest.K10.LeftIs.padded_first
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_of_close
