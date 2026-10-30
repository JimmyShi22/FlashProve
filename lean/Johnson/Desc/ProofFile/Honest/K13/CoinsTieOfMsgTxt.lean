-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsTieOfMsgTxt.lean: kind K13, the members' batching:
`coinsTie_of_k1` (CoinsTieOfK1.lean of this folder) AT KIND K1's OWN WHOLE-MESSAGE TEXT `msgTxt`
(Honest/K1/ScriptLots.lean): UNDER THE SAME FACTS ON THE STATE AND THE SAME PUBLIC PREMISES ON THE
SENDING, WHERE THE SCRIPT HAS `OwnMsgs` AT THAT TEXT AND THE SENDER's CUT IS THERE AT EVERY RUN's
COINS (`OwnIs`) (the premises are not shown; no example is known at which all hold and the thread
stands somewhere): THE KIND's TIE `CoinsTie`. The premise on the sender's text has fallen: it is
K1's `msgTxt_mask_slot` (Honest/K1/ScriptMaskSlot.lean). One statement with its proof; no
definition.

Main name: `coinsTie_of_msgTxt`.

WHAT IS LEFT AS PREMISES. hrd, hsh, hq (the caller's) · hSt (the thread's facts at the border) · hV
(the thread's) · hO (THE SCRIPT's: `OwnMsgs` at arr q.1 q.2 at msgTxt … n: that the Script is laid
so, AND THAT THE SENDER's MESSAGE NUMBER n IS LAID AT THE WITNESS's NUMBER arr q.1 q.2) · ho (THE
BOOK's: `OwnIs`: it is `lentCut … = some (own k)` by that definition's text: A SENTENCE AT EVERY
RUN's COINS, NO TEST WITH CODE; without it msgTxt answers nothing. The public test that gives it at
the chain numbers 0 and 1 is K1's `bookCovers` (Honest/K1/ScriptAt.lean), by `lentCut_isSome`
(Honest/K1/ScriptAtLaw.lean): not called here; taken by name in CoinsTieAtHead.lean of this folder)
· hS (THE BOOK's: the test `oneStretch`: the start of the entry for the kind's row is maskStart +
k₀) · hn, hfit, ha (public, on the sending alone) · hshape, hfreeP (public, BETWEEN THE SENDING AND
THE VERIFIER's LIST AND CODES: premises here; under the library's head, O and hP, at n = 4, they are
shown in AtFullSide/K13/CoinsTieFive.lean) · hfree (numbers: k₀ + (2 kCol + 1) ≤ free, at the
letters k₀ and free).

Limits. NOT IN FRONT OF A LAW OVER COINS: the ground: the Limits of CoinsTieOfFacts.lean of this
folder. As CoinsTieOfK1.lean's: conditional on all of these; the ties of counts; nothing on two
places; nothing on what an entry is for. Its imports reach Johnson/Goal/, by ExchangeAtM3.lean.

What is not claimed. That any premise holds. That msgTxt answers at any book. It is none of the
library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.CoinsTieOfK1
import Johnson.Desc.ProofFile.Honest.K1.ScriptMaskSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit rwBook LedgerAt)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Letters OwnMsgs)
open ProofFile.Honest.K1 (dueR sendFits msgTxt lentCut msgTxt_mask_slot fits_noRide free_lt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok : Type}

/-- **`CoinsTie` AT KIND K1's OWN TEXT.** CONDITIONAL: on every premise named; which they are: the
head. -/
theorem coinsTie_of_msgTxt (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok MsgT) (b : Nat)
    (weights : W₀ → Weights) (pile : PileOf Xi) (P₁₃ : Where)
    (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok MsgT →
      Wit GE P₁₃.lin.matrixRows P₁₃.lin.kCol)
    {nR kC : ℕ} (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
    (hrd : ∀ a v, (rd a v).mask = (rwBook arr mat a v).mask)
    (M : List OracleShape) (Ld : VerifiableInference.Desc.K12.Door.Laid) (im k₀ free : ℕ)
    (sh : OracleShape) (q : ℕ × ℕ)
    (hsh : M[im]? = some sh) (hq : Ld.places[im]? = some q)
    (hSt : ∀ k s m En, Thr L.thread b k s m En →
      s.out.indexMasks = im ∧ msgShapesB M s.st = true ∧
        bookInOrderB 0 s.book s.roots = true ∧ seatsCarriedB Ld s.book = true ∧
        s.book.place.size = s.st.oracles.size ∧
        placesBelowB Ld s.book.place.size s.book.trees.size = true ∧ LedgerAt s.st im k₀ ∧
        free = Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
          sh.answers)
    {Vd : Local W₀ Rc Xi Tr → Prop} {N fx : ℕ} {W' X' : Type}
    (wit : Local W₀ Rc Xi Tr → W') (J : K1.SendJob W' X') (own₀ : X') (n : ℕ)
    (hO : OwnMsgs L.Q Vd N (arr q.1 q.2) fx (msgTxt L.thread.chain wit J own₀ n))
    (hV : ∀ k s m En, Thr L.thread b k s m En → Vd m.st.input ∧ N ≤ m.st.heard.length)
    (hn : n < J.P.sent.size) (hfit : sendFits J.P J.ride = true) (hshape : shapeAt J.P n = sh)
    (ha : sh.answers ≠ 0)
    (hfreeP : free ≤ Send.freeMaskEntries sh.maskRows
      (J.P.codes.mask.getD sh.maskCode default).ell sh.answers)
    {own : Coins Bk → Cs (dueR J.P J.ride)}
    (ho : OwnIs Bk L.thread.chain ⟨J.P.place, 0⟩ (dueR J.P J.ride) own)
    (hS : ∀ blk, L.thread.bs[b]? = some blk →
      oneStretch (rowEntries Bk blk.place 2 0) =
        some (⟨J.P.place, 0⟩, K1.maskStart J.P J.ride n + k₀, 2 * P₁₃.lin.kCol + 1))
    (hfree : k₀ + (2 * P₁₃.lin.kCol + 1) ≤ free) :
    CoinsTie L b weights pile P₁₃ rd := by
  refine coinsTie_of_k1 L b weights pile P₁₃ rd arr mat hrd M Ld im k₀ free sh q hsh hq hSt hO hV
    J.P J.ride n hn hfit hshape ha hfreeP ho ?_ hS hfree
  intro k w hd ν _ _ hν
  subst hshape
  have hr : J.ride n = none := fits_noRide J.P J.ride n hfit hn ha
  rw [msgTxt_mask_slot L.thread.chain wit J own₀ n ν k w (hd.take fx) hr
    (free_lt _ _ _ ν (Nat.pos_of_ne_zero ha) (Nat.lt_of_lt_of_le hν hfreeP))]
  have e : lentCut k L.thread.chain ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some (own k) := ho k
  rw [e]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.coinsTie_of_msgTxt
