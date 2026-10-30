-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidesOn.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5): THE JOINED LAW's PREMISE «the thread's rider goes on along the kind's clause» (hRdM),
EXCHANGED, AT A RIDER THAT IS A LIST OF CLAUSES, FOR ONE PREMISE ON THE CLAUSES' FIRST AND LAST
BORDERS AND THEIR SHAPES. EXCHANGED, NOT PAID: the number of premises stays. Two statements with
their proofs: calls alone. No definition.

  k5_owes_all_joined_left_riders        k5_owes_all_joined_left (AllJoinedLeft.lean) at
                RdL := ridersOf hd, with hsp where that has hRdM
  k5_owes_all_joined_left_book_riders   the like of k5_owes_all_joined_left_book
                (AllJoinedLeftBook.lean)

The premise hsp. Every clause c of the list hd has one of four shapes: it begins behind border 327 ·
it speaks at one border alone, a number 14 l + 9 · it speaks from a number 28 k + 5 to 28 k + 10 ·
it is riderAtt (14 l + 4) (14 l + 9) fun a => R a.g: a sentence on one field of the open attention
segment's part of the verifier's state. It speaks of numbers and of the clauses' form; of no input
and of no state.

Called: k5_rides_on (RidesFree.lean in this folder) · k5_owes_all_joined_left ·
k5_owes_all_joined_left_book.

The two corollaries' statements were made by a program out of the two theorems that they call: the
name; hRdM's binder for hsp's; the letter RdL for ridersOf hd, in the variables and at five places
of the end. Nothing else parts.

Limits. Conditional. THE LIST hd IS A LETTER: that any written list of clauses has the four shapes
is not proved here. A thread whose rider is a conjunction of such a list with a further sentence is
not spoken of: that sentence's passing is another's. All Limits of AllJoinedLeft.lean and
AllJoinedLeftBook.lean hold here too: every other premise stays; the ends may hold emptily.
K5RiderSpans.lean bears two names that Thread/K5ThroughLaidM.lean declares too:
 the two must not be imported into one module. Through its imports the file stands
above the library's folder ThirdParty/. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedLeftBook
import Johnson.Desc.ProofFile.Honest.Thread.K5RiderSpans
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
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head k5_hcs_laid_M k5_hcl_spans)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (hd : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) TS))
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **ALL OF THE MEMBER's DEBTS AT THE RIDER OF A LIST OF CLAUSES.** CONDITIONAL: as
`k5_owes_all_joined_left`, with hsp where that has hRdM. -/
theorem k5_owes_all_joined_left_riders {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hsp : ∀ c ∈ hd, 327 < c.lo ∨ (c.hi = c.lo ∧ c.lo % 14 = 9) ∨
      (c.lo % 28 = 5 ∧ c.hi = c.lo + 5) ∨
      ∃ (l : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
        c = riderAtt (14 * l + 4) (14 * l + 9) fun a => R a.g)
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_left h Q test carryX item n₁ n₂ Vd (ridersOf hd) f w hg hA hO hfix hf
    (fun a _ => k5_rides_on hsp hg a.own) hLent HQ hH

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (hd : List (RiderCl (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) TS))
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE SAME AT THE BOOK THAT onlineProverFromPublicFiles RETURNS.** CONDITIONAL: as `k5_owes_all_joined_left_book`,
with hsp where that has hRdM. -/
theorem k5_owes_all_joined_left_book_riders {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hsp : ∀ c ∈ hd, 327 < c.lo ∨ (c.hi = c.lo ∧ c.lo % 14 = 9) ∨
      (c.lo % 28 = 5 ∧ c.hi = c.lo + 5) ∨
      ∃ (l : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
        c = riderAtt (14 * l + 4) (14 * l + 9) fun a => R a.g)
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd (ridersOf hd) (kpBy f)
          w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_left_book h Q test carryX item n₁ n₂ Vd (ridersOf hd) f w hg hA hO hfix hf
    (fun a _ => k5_rides_on hsp hg a.own) hBook HQ hH

end

end ProofFile.Honest.K5
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_left_riders
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_left_book_riders
