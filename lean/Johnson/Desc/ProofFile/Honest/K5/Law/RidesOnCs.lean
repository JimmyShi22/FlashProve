-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidesOnCs.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5): AT THE WRITTEN LIST OF THE FIRST CHAIN's RIDERS (csHead, Honest/Thread/CsHead.lean)
 THE JOINED LAW's PREMISE ON THE RIDER IS PAID: NINE PREMISES ARE LEFT. One statement
with its proof: a call. No definition.

  k5_owes_all_joined_nine   CONDITIONAL: k5_owes_all_joined_left_lends (LendsRow5.lean) at
                            RdL := ridersOf (csHead ν st R), without its premise hRdM

THE NINE: h · hg · hA · hO · hfix · hf · hLends · HQ · hH. What each asks stands in the heads of
AllJoinedLeft.lean and LendsRow5.lean.

Called: k5_rides_on_csHead (RidesFree.lean in this folder) · k5_owes_all_joined_left_lends.

The statement was made by a program out of the theorem that it calls: the name; hRdM's binder
struck; the letter RdL for ridersOf (csHead ν st R), in the variables and at five places of the end.
Nothing else parts.

Limits. Conditional. PAID AT THIS LIST ALONE: at another list of clauses the premise on its shapes
stays (RidesOn.lean); at a rider that is no list of clauses hRdM stays (AllJoinedLeft.lean). The
three arguments of csHead are letters: what its clauses say is not looked at: their first and last
borders, and in one shape their form. A thread whose rider is a conjunction of this list with a
further sentence is not spoken of: that sentence's passing is another's. All Limits of
AllJoinedLeft.lean and LendsRow5.lean hold here too: the nine are proved together nowhere; the ends
may hold emptily. K5SpansCs.lean bears a name that another file
(Thread/K5ThroughCs.lean) declares too: the two must not be imported into one module. Through its
imports the file stands above the library's folder ThirdParty/. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsRow5
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesOn
import Johnson.Desc.ProofFile.Honest.Thread.K5SpansCs
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head k5_hsp_csHead)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **ALL OF THE MEMBER's DEBTS AT THE WRITTEN LIST OF RIDERS: NINE PREMISES.** CONDITIONAL: as
`k5_owes_all_joined_left_lends`, without hRdM. -/
theorem k5_owes_all_joined_nine {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow Bk 0 (seatOf keyOfK3 Zp A.G cF g a).place (k5Row (seatOf keyOfK3 Zp A.G cF g a)) =
        true)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_left_lends h Q test carryX item n₁ n₂ Vd (ridersOf (csHead ν st R)) f w hg hA
    hO hfix hf (fun a _ => k5_rides_on_csHead ν st R hg a.own) hLends HQ hH

end ProofFile.Honest.K5
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_nine
