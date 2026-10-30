-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAt4.lean: THE TWO PARAMETERS THAT `At.𝔇All` (LettersAll.lean) TAKES AS ARGUMENTS,
wt AND cr1, EACH AT ITS OWNER's TERM; AND THE STRUCTURE WITH BOTH LAID. Three definitions;
three equations by the make.

  `At.wt Zp cF lay` := `Kinds.Head.Law.AtTable.wtK6 cs arr ms N X layout num (num 24 0) 0`
    (Johnson/Desc/Kinds/Law/WtK6.lean), each at this folder's own value:
    the sentence "weights" of the output head: fun m a _ w => m = 24 → InRange w.cells →
    WeightAt X a.2 (compCut … w).1.toCells (compCut … w).2; the seats inside it: the owner's
    `seatLay X layout num`. WHY THIS TEXT: the sentence
    is concluded by the merge and taken by the output head's sub-protocol four sub-protocols
    earlier; the merge's own sentence asks a claim that the verifier's state holds only behind the
    last of these four; this one reads what the head has heard, the request and one slot of the
    ledger.
  `At.cr1 Zp lay` := `K2Caller.carryAtZ Zp lay` (Johnson/Top/H0/K2Caller/CarryClosed.lean:
    its way in reads the copy of the frame that is in use): the sentence "carry" of the code
    switching.
  `At.𝔇Whole …` := `At.𝔇All … (wt Zp cF lay) (cr1 Zp lay) nR`: no parameter of the composed meaning
    is an argument.
  `wt_reads_own`, `cr1_is`, `wt_is`: the two fields of `𝔇Whole` are these terms; wt stands at the
    structure's own cs, arr, ms, N and layout.
WHAT ANSWERS IN SILENCE, OR IS A LITERAL, IN THE OWNERS' TEXTS. wt: THREE LITERALS OF THE FULL
SIZE: the segment 24 · `ppref` and `kRef` (in `whOf`, Johnson/Desc/Kinds/Law/WhOf.lean, which also
answers 0 where `indexOf` answers nothing);
`maskQ` has no code: SO NO EXAMPLE AT A SMALL SIZE CAN BE HAD BY NAME. At every m other than 24, and
at cells out of range, the sentence holds idly. cr1: beneath it `ProofFile.pAtK2` (all zeros) · `allAt`
(the empty list) · `keyAt` (the identity) answer in silence (Johnson/Desc/ProofFile/CarryAt.lean):
the named tests: `(ProofFile.wholeAt Zp).isSome` · `(ProofFile.pAtK2? Zp m).isSome` wherever `ProofFile.rowAtK2`
answers; its way in at the head takes a blank plan of the approximate range proof. CAN THEY BE MET?
NOT SHOWN, OF EITHER. By a run at an honest small proof (another size than the sentence's own):
WeightAt's first two conjuncts hold and its one slot is filled, below the ledger's next, with one
value, at the five borders in front of the sub-protocols 5 … 9 of the output head's segment; the
equation itself has not been evaluated. Of cr1 nothing has been evaluated.
Limits. Definitions. Nothing on soundness.

-/
import Johnson.P5J.LettersAll
import Johnson.Desc.Kinds.Law.WtK6
import Johnson.Top.H0.K2Caller.CarryClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.Sound (MgData CellsQ MsgT SeatsNamed GroupsSeated)

/-- The sentence "weights" of the output head. -/
def wt (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (lay : ByteArray) :
    ℕ → ProofFile.InstPub × TS → Strs →
      Wit (CellsQ OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull)) Tok MsgT → Prop :=
  VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6 (cs Zp) (arr Zp) (ms Zp lay) (N Zp cF)
    (X Zp) (layout Zp) (num Zp) (num Zp 24 0) 0

/-- The sentence "carry" of the code switching. -/
def cr1 (Zp : ProofFile.Pub) (lay : ByteArray) :
    ℕ → ProofFile.InstPub × TS → Strs →
      Wit (CellsQ OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull)) Tok MsgT → Prop :=
  VerifiableInference.Desc.First.K2Caller.carryAtZ Zp lay

section
variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
    (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB
    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : GroupsSeated (ms Zp lay) (N Zp cF))
  (x : VerifiableInference.Desc.First.Look.Place)

/-- **The structure of the composed meaning's parameters, whole.** -/
noncomputable def 𝔇Whole (nR : ℕ) :
    MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR
      (X Zp) :=
  𝔇All o Zp Np cF E hs lay hL hN hG x (wt Zp cF lay) (cr1 Zp lay) nR

theorem wt_is (nR : ℕ) : (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).wt = wt Zp cF lay := rfl

theorem cr1_is (nR : ℕ) : (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).cr1 = cr1 Zp lay := rfl

/-- wt stands at the structure's own fields. -/
theorem wt_reads_own (nR : ℕ) :
    (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).wt =
      VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtK6
        (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).cs
        (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).arr
        (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).ms
        (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).N (X Zp)
        (𝔇Whole o Zp Np cF E hs lay hL hN hG x nR).layout (num Zp) (num Zp 24 0) 0 := rfl

end

end P5J.At

#print axioms P5J.At.wt_is
#print axioms P5J.At.cr1_is
#print axioms P5J.At.wt_reads_own
