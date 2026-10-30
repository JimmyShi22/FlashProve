-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Eight.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN ROUNDS
(kind K5): THE JOINED LAW's PREMISE ON THE LENDING IS PAID AT THE BOOK THAT onlineProverFromPublicFiles RETURNS: EIGHT
PREMISES ARE LEFT. Three statements with their proofs: calls alone. No definition.

  k5_lends_at_head           CONDITIONAL: under h, hg, hB (bookWhole returns B at the head's
                             description) and ha: **lendsRow B 0 ‹the seat's place› (k5Row ‹the
                             seat›) = true**, at every reader keyOf of the key points and every G
  k5_lends_paid              CONDITIONAL: under h, hg and hA: the same at B := A.B, at keyOfK3 and
                             A.G: hLends of the form of record
  k5_owes_all_joined_eight   CONDITIONAL: k5_owes_all_joined_nine (RidesOnCs.lean) at Bk := A.B,
                             without its premise hLends

THE EIGHT: h · hg · hA · hO · hfix · hf · HQ · hH. What each asks stands in the heads of
AllJoinedLeft.lean and RidesOnCs.lean.

THE ROAD, each step a law with its own file. The frame's test lendsRow (Honest/Small/LendsRow.lean,
of other authors) from our shorter test rowNamed (LendsRow5.lean, LendsOfBook.lean) · rowNamed from
sentences on the book and the maker (RowNamedOfPick.lean, NamedOfWants.lean) · no row and no carried
run at the kind's addresses (Honest/BookPlain.lean) · what the maker states for the member's parts
is what the row's parts state; the names of the member's rounds (StatedK5.lean) · AND, CALLED HERE:
other authors' pick_whole (Honest/BookRowStretch.lean): the entries that a part spends are the
maker's stretches with that spender.

The third statement was made by a program out of k5_owes_all_joined_eight_of (EightOfPick.lean): the
name; hPWA's binder struck. Nothing else parts.

Limits. Conditional. PAID AT Bk := A.B ALONE, AND UNDER hA: that onlineProverFromPublicFiles returns, and with it that
the book's maker returns, stays a premise. It says whether the lending returns: nothing on what is
lent. The rider is the written list csHead, as in RidesOnCs.lean. All Limits of RidesOnCs.lean hold
here too: the eight are proved together nowhere; the ends may hold emptily. h is a hypothesis; on
whether it can be met see Member.lean's head. At the library's full size and the format's second
hash function alone. Through its imports the file stands above the library's folder ThirdParty/. No property
is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.EightOfPick
import Johnson.Desc.ProofFile.Honest.BookRowStretch

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

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **THE FRAME's TEST ON THE LENDING IS TRUE AT K5's PLACE AND ROW, AT EVERY BOOK THAT THE MAKER
RETURNS AT THE HEAD's DESCRIPTION.** -/
theorem k5_lends_at_head {g : Nat} (hg : g < 12) {B : ProverCoinCounts} {p0 p1 p2 : Johnson.G.ChainSends}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (keyOf : ProofFile.Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) (G : Ground)
    {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) :
    lendsRow B 0 (seatOf keyOf Zp G cF g a).place (k5Row (seatOf keyOf Zp G cF g a)) = true :=
  k5_lends_of_pick h hg hB
    (fun _ hb hF =>
      pick_whole hB (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) hb hF)
    keyOf G ha

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

include h in
/-- **hLends, PAID AT THE BOOK THAT onlineProverFromPublicFiles RETURNS.** CONDITIONAL: h; g is below 12; hA. -/
theorem k5_lends_paid {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow A.B 0 (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Row (seatOf keyOfK3 Zp A.G cF g a)) = true :=
  k5_lends_at_pure h hg hA fun _ _ _ hB _ hb hF =>
    pick_whole hB (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) hb hF

/-- **ALL OF THE MEMBER's DEBTS AT THE BOOK THAT onlineProverFromPublicFiles RETURNS: EIGHT PREMISES.** CONDITIONAL: as
`k5_owes_all_joined_nine` at Bk := A.B, without hLends. -/
theorem k5_owes_all_joined_eight {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
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
  k5_owes_all_joined_nine h Q test carryX item n₁ n₂ Vd ν st R f w hg hA hO hfix hf
    (k5_lends_paid h hg hA) HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lends_at_head
#print axioms ProofFile.Honest.K5.k5_lends_paid
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_eight
