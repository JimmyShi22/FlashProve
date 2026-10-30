-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/AtFirstThread355.lean: kind K13, the members' batching: THE FIVE
STATEMENTS AT NUMBER 355 OF THE PROOF FILE's FIRST CHAIN AT THE FIRST THREAD AS IT IS WRITTEN
(`firstThread`, Honest/Thread/TheFirstThread.lean), AND AS ONE VALUE OF `FiveAtBorder`
(Honest/Thread/FiveAtBorder.lean). Statements with their proofs: calls; no definition. THE FULL SIZE
ALONE, AT THE FORMAT's SECOND HASH FUNCTION ALONE.

The variables. A: a value of the structure that the maker `onlineProverFromPublicFiles` returns. hd: the head at A
(`HeadAtReturn`: the maker returned A at some filling, and the library's one hypothesis at the full
size holds at A's public part). parts: what the first thread takes from outside: the Script and the
falls' stated numbers. w: the run's input. Said, fall: any.

EACH STATEMENT WITH ALL ITS PREMISES.
  `k13_behindS_at_firstThread`, `k13_ridesPastS_at_firstThread`, `k13_pins_at_firstThread` (of
    `ExchangeS` the items "pinI" and "pinW"; the second holds by the frame's own parameters and is
    no work of the kind's): **hd alone**: of hd the proofs read the hypothesis at A's public part
    and nothing else; the filling, the index's type and the type of the stored randomness are
    variables.
  `k13_playsS_at_firstThread`: **hd, and hA**: A is the maker's return at the wide filling
    `onlineProverPartsInUse I o S O` (Honest/K1/Law/WSideAtFill.lean), I and o variables.
  `k13_acceptedS_at_firstThread`: **hd, hA, and hO**: O.pile is the written filler `pileAnyK3`.
  `k13_five_at_firstThread`: **`FiveAtBorder (firstThread hd parts w) Said fall 355`: hd, hA, hO,
    and hM, hC**: `MatTie` and `CoinsTie` (ExchangeAtM3.lean of this folder) at the first thread's
    parameters. Of the five's parts the item "pileOne" of `ExchangeS` alone reads these two.

How the clause of what a step keeps is met. At the kind K13 the first thread's clause
(`firstClauses`) is, by its text, `K13KeepsAll` beside the public tests of the claims on linear
forms at the state behind (`formsBehind`, Honest/Thread/FHeadF.lean) and sentences that are "True"
at this kind: `k13_keepsTo_firstClauses`, `k13_keepsOf_firstClauses`. The first half holds behind
the member's accepted step by the kind's own law (`k13_keepsAll_behind`, FiveAt355.lean of this
folder); the second follows from the thread's form behind the member (`formsBehind_of_form` at
`k13_form_behind`, FormBehind.lean): `k13_left_of_clause`, which is general in the clause and in
every other parameter of the thread but the list `csHead` and the number 339. So of the first
thread's file the statements above read these two values and the clause at this kind, and nothing
else.

WHAT IS LEFT AT THIS BORDER: hM and hC. hM: at the one input that the thread admits, the Script's
cells are the matrix that I.weights gives. hC: the mask entries under the slots that the verifier
takes are the coins that the book A.B lends the sumcheck's part. A proof of hC from premises on the
Script: `k13_coinsTie_at_maker` (AtFullSide/K13/CoinsTieAtMaker.lean); it stands at o := the
format's second hash function alone. The join of hM, hC and the five, at the written
Script:
`k13_five_at_firstScript` (AtFullSide/K13/FiveAt355AtFirstScript.lean).
WHAT THE KIND OWES BESIDE THIS BORDER, AND IS NOT TREATED HERE: number 356 of the same chain is the
sending of the message W with a step of this kind joined behind it.

Limits. All five are premises' forms: where the thread stands at no run they speak of nothing, and
neither this file nor any file that it imports shows that it stands at 355 at any run. The wide
filling is defined in
Honest/K1/Law/WSideAtFill.lean. This file does not show that the maker returns at it (more on that:
AtBase355.lean of this
folder, Limits).

What is not claimed. hM, hC at any Script. That a head stands at any A; that the maker returns.
Anything at number 356, in the other two chains or at the key file. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.AtBase355
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (K13KeepsAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF formsBehind formsBehind_of_form HeadAtReturn
  FirstThreadParts firstClauses firstLetters firstThread)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`K13Left` AT ANY CLAUSE BY KINDS THAT, AT THE KIND's PLACE, LIES BETWEEN `K13KeepsAll` AND
`K13KeepsAll` WITH THE PUBLIC TESTS OF THE CLAIMS ON LINEAR FORMS BEHIND**, at the written list of
the thread's other clauses and b₀ := 339: under h. General in all other parameters of the thread. -/
theorem k13_left_of_clause (f : KindName → Place → TS → TS → Prop)
    (hTo : ∀ s s', f .K13 ⟨1, none, 3, .K13⟩ s s' → K13KeepsAll h.𝔇.P13 s s')
    (hOf : ∀ s s', K13KeepsAll h.𝔇.P13 s s' → formsBehind h.𝔇.pubD ⟨1, none, 3, .K13⟩ s' →
      f .K13 ⟨1, none, 3, .K13⟩ s s')
    (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) :
    K13Left h H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) (kpBy f) w :=
  k13_left_at_csHead h test carryX item n₁ n₂ _ ν st R H Q Vd w hTo
    fun blk hb k s m E ds y cols s' hT _ hS =>
      hOf s s'
        (k13_keepsAll_behind h H Q test carryX item n₁ n₂ 339 Vd _ _ w blk hb k s m E ds y cols s'
          hT hS)
        (formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd _ _ w m3_place
          (k13_form_behind h H Q test carryX item n₁ n₂ 339 Vd _ _ w blk hb k s m E ds y cols s' hT
            hS))

end

/-! ## At the first thread, at any value of the maker's structure of returns -/

section
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- At the kind's place the first thread's clause gives what the kind's step leaves of the state. -/
theorem k13_keepsTo_firstClauses : ∀ s s',
    firstClauses hd .K13 ⟨1, none, 3, .K13⟩ s s' → K13KeepsAll hd.head.𝔇.P13 s s' :=
  fun _ _ hk => hk.1.1.1.1.1

/-- At the kind's place the first thread's clause asks no more than that and the public tests of the
claims on linear forms at the state behind. -/
theorem k13_keepsOf_firstClauses : ∀ s s', K13KeepsAll hd.head.𝔇.P13 s s' →
    formsBehind hd.head.𝔇.pubD ⟨1, none, 3, .K13⟩ s' →
      firstClauses hd .K13 ⟨1, none, 3, .K13⟩ s s' :=
  fun _ _ a b => ⟨⟨⟨⟨⟨a, b⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩

/-- **`BehindS` AT 355, AT THE FIRST THREAD**: from the head at A's public part alone. -/
theorem k13_behindS_at_firstThread : BehindS (firstThread hd parts w) Said 355 :=
  k13_behindS_at_355 _ _ _ _ _ _ _ _ _ _ _ _ _
    (k13_left_of_clause hd.head A.H parts.script _ _ _ _ _ _ w _ (k13_keepsTo_firstClauses hd)
      (k13_keepsOf_firstClauses hd) _ _ _) Said

/-- **`RidesPastS` AT 355, AT THE FIRST THREAD**: from the head at A's public part alone. -/
theorem k13_ridesPastS_at_firstThread : RidesPastS (firstThread hd parts w) Said 355 :=
  k13_ridesPastS_at_355 _ _ _ _ _ _ _ _ _ _ _ _ _
    (k13_left_of_clause hd.head A.H parts.script _ _ _ _ _ _ w _ (k13_keepsTo_firstClauses hd)
      (k13_keepsOf_firstClauses hd) _ _ _) Said

/-- **Of `ExchangeS` at 355 the items "pinI" and "pinW", at the first thread**: from the head at A's
public part alone. The second is no work of the kind's: it holds by the frame's own parameters. -/
theorem k13_pins_at_firstThread :
    ExchangeAtS (firstThread hd parts w) Said 355 VerifiableInference.Desc.First.Item.pinI ∧
      ExchangeAtS (firstThread hd parts w) Said 355 VerifiableInference.Desc.First.Item.pinW :=
  ⟨k13_pinI_at_355 _ _ _ _ _ _ _ _ _ _ _ _ _
      (k13_left_of_clause hd.head A.H parts.script _ _ _ _ _ _ w _ (k13_keepsTo_firstClauses hd)
      (k13_keepsOf_firstClauses hd) _ _ _) Said,
    k13_pinW_at_355 _ _ _ _ _ _ _ _ _ _ _ _ _ Said⟩

end

/-! ## Over the prover that the maker returns at the wide filling -/

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
  (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (hd : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include hA in
/-- **`PlaysS` AT 355, AT THE FIRST THREAD**: from the maker's return and the head at it alone. -/
theorem k13_playsS_at_firstThread : PlaysS (firstThread hd parts w) Said 355 :=
  k13_playsS_at_base hd.head I o S O hA parts.script _ _ _ _ _ _ _ _ _ w Said

include hA in
/-- **`AcceptedS` AT 355, AT THE FIRST THREAD**, at every fall: from the maker's return, the head at
it, and that the filling's filler of the pile is the written one. -/
theorem k13_acceptedS_at_firstThread (hO : O.pile = pileAnyK3)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (firstThread hd parts w) Said fall 355 :=
  k13_acceptedS_at_base hd.head I o S O hA parts.script _ _ _ _ _ 339 _ _ _ w Said hO (by omega)
    fall

include hA in
/-- **THE FIVE STATEMENTS AT 355, AT THE FIRST THREAD AS IT IS WRITTEN**, at every Said and every
fall: from the maker's return, the head at it, the written filler of the pile, and the two ties,
which the item "pileOne" alone reads. -/
theorem k13_five_at_firstThread (hO : O.pile = pileAnyK3)
    (hM : MatTie (firstLetters hd parts w) (I.weights A.Z) (pileAnyK3 A.Z A.G) hd.head.𝔇.P13
      (k13ReaderAt hd.head))
    (hC : CoinsTie (firstLetters hd parts w) 355 (I.weights A.Z) (pileAnyK3 A.Z A.G)
      hd.head.𝔇.P13 (k13ReaderAt hd.head))
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (firstThread hd parts w) Said fall 355 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := k13_five_at_base hd.head I o S O hA parts.script _ _ _ _ _ _ _ w
    Said _ _ _ hO (k13_left_of_clause hd.head A.H parts.script _ _ _ _ _ _ w _
      (k13_keepsTo_firstClauses hd) (k13_keepsOf_firstClauses hd) _ _ _) hM hC
    fall
  exact ⟨h1, h2, h3, h4, h5⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_left_of_clause
#print axioms ProofFile.Honest.K13.k13_keepsTo_firstClauses
#print axioms ProofFile.Honest.K13.k13_keepsOf_firstClauses
#print axioms ProofFile.Honest.K13.k13_behindS_at_firstThread
#print axioms ProofFile.Honest.K13.k13_ridesPastS_at_firstThread
#print axioms ProofFile.Honest.K13.k13_pins_at_firstThread
#print axioms ProofFile.Honest.K13.k13_playsS_at_firstThread
#print axioms ProofFile.Honest.K13.k13_acceptedS_at_firstThread
#print axioms ProofFile.Honest.K13.k13_five_at_firstThread
