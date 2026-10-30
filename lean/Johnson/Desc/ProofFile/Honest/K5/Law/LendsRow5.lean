-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LendsRow5.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5): THE JOINED LAW's PREMISE ON THE LENDING (Lends5, Honest/K5/Law/CoinsFewOf.lean: at every
run the book's lending to the kind's row returns) IS ONE Bool OF THE BOOK AND THE ROW: the frame's
own test lendsRow (Honest/Small/LendsRow.lean, of other authors). THE EQUIVALENCE IS lends5_iff
(LendsHalf.lean in this folder); THE NUMBER OF PREMISES STAYS. One statement with its proof: a call.
No definition.

  k5_owes_all_joined_left_lends   CONDITIONAL: k5_owes_all_joined_left (AllJoinedLeft.lean) with
                         hLends, the Bool, where that has hLent

Called: lends5_iff (LendsHalf.lean) · k5_owes_all_joined_left.

The statement was made by a program out of the theorem that it calls: the name; hLent's binder for
hLends'. Nothing else parts.

Limits. Conditional. That the Bool is true at any book is not proved here. It says whether the
lending returns: nothing on what is lent. The test reads of a part its takes, spends and carries
alone. All Limits of AllJoinedLeft.lean hold here too: every other premise stays; the ends may hold
emptily. Through its imports the file stands above the library's folder ThirdParty/. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfBook
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedLeft
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName FileDescription)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **ALL OF THE MEMBER's DEBTS, WITH THE FRAME's Bool IN THE STEAD OF THE PREMISE ON THE LENDING.**
CONDITIONAL: as `k5_owes_all_joined_left`, with hLends where that has hLent. -/
theorem k5_owes_all_joined_left_lends {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow Bk 0 (seatOf keyOfK3 Zp A.G cF g a).place (k5Row (seatOf keyOfK3 Zp A.G cF g a)) =
        true)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_left h Q test carryX item n₁ n₂ Vd RdL f w hg hA hO hfix hf hRdM
    (fun a ha => (lends5_iff Bk _ _).2 (hLends a ha)) HQ hH

end ProofFile.Honest.K5
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_left_lends
