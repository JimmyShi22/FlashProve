-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoinedLeft.lean: CONDITIONAL: ALL OF THE DEBTS OF THE MEMBER
OF AN ATTENTION SEGMENT's OWN ROUNDS (kind K5) AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT THE FILLING OF
RECORD widerFillAt, WITH TWO PREMISES STRUCK AND ONE CUT DOWN BY FILES OF OTHER AUTHORS: so that the
list of what is left stands in a theorem's binders. One statement with its proof: calls.

  k5_owes_all_joined_left   CONDITIONAL: Plays, Behind, Exchange, RidesPast and, at every fall,
                            Accepted, at the border of the group g

WHAT IS LEFT, ALL OF IT: h: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) · hg: g is
below 12 · hA: onlineProverFromPublicFiles returns A at the head's three files and the filling · hO: the filling's reader
of the key points is keyOfK3 · hfix: the Script's number for a tree lies within the rounds in front
of the border behind its sender · hf: the letter f at the kind K5 is the clause by the place · hRdM:
the letter Rd goes on along the kind's clause · hLent: the book's lending to the kind's own row
returns, at all coins (Lends5, Honest/K5/Law/CoinsFewOf.lean) · HQ: K5ScriptQ: the two equations on
the Script · hH: at a valid input the Script's cells hold an index.

WHAT IS STRUCK AGAINST k5_owes_all_joined_wider_lent (Honest/K5/Law/LotLaidWider.lean), AND BY WHAT:
hG: the ground is A's own: atPure_ok (Honest/AtPureLaw.lean) has that the maker makes it of A's
public part, which is the head's · hfit: fits_head (Honest/Thread/FitsHead.lean) cuts it to a closed
test on the written lists and hfix; the closed test is K4.W.onePass_full
(Honest/K4/Law/W/OnePassFull.lean), decided by Lean's kernel · hb₀: THE LETTER b₀ IS LAID: b₀ :=
b0Head (Honest/Thread/ReplyAt.lean: the border behind the one place of the written list whose
decision may write the reply): b0Head_ne_k5 (Honest/Thread/ReplyIs.lean).

WHY THE OTHERS STAY, AS FAR AS THE FILES AT HAND WHEN THIS WAS WRITTEN SAY; no wider search is
claimed. hA: that onlineProverFromPublicFiles returns is shown at no files · hO, hfix and HQ, hRdM, hH with hf: each is a
premise on a free letter of the statement: the filling's O; the Script Q; Rd; Vd; f. Of O no term of
its type was at hand. Of Q a laying by lots and its laws were being typed by their authors. Of Rd
the general law on riders (riders_next, Honest/Thread/Riders.lean) was at hand, the two lemmas that
would bring it to this kind were not. Of Vd no Lean text was at hand. Of f the file that lays it
(Honest/Thread/FHead.lean) was at hand, most of the files that it imports were not · hLent: a
premise on the book: shown nowhere.

Limits. Conditional. h is a hypothesis (it has a member at the library's written copy of the
full-size public files, AtFullSide.Top.headMember_zFull); hg is a bound on a letter; NONE OF THE
OTHER EIGHT IS SHOWN HERE. The statement stands at b₀ := b0Head alone. hLent and HQ are typed at A's
own ground. Beneath what is called lie closed facts that Lean's kernel has decided by evaluation at
the library's written lists: K4.W.onePass_full, and b0Head_closed (Honest/Thread/ReplyAt.lean) under
b0Head_ne_k5. Through its imports the file stands above the library's folder ThirdParty/. At the
library's full size and the format's second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotLaidWider
import Johnson.Desc.ProofFile.Honest.Thread.FitsHead
import Johnson.Desc.ProofFile.Honest.Thread.ReplyIs
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
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

/-- **ALL OF THE MEMBER's DEBTS AT THE PROVER THAT onlineProverFromPublicFiles RETURNS, UNDER WHAT IS LEFT.**
CONDITIONAL: every premise stands, by name, in the file's head. -/
theorem k5_owes_all_joined_left {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a))
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
        fall (borderOf g) := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  exact k5_owes_all_joined_wider_lent h Q test carryX item n₁ n₂ b0Head Vd RdL f w hg hG hA hO
    (FirstThread.fits_head h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w
      K4.W.onePass_full hfix) hf (FirstThread.b0Head_ne_k5 g) hRdM hLent HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_joined_left
