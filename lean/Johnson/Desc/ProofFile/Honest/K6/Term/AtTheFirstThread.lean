-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/AtTheFirstThread.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind
K6 of the online proof): AT THE FIRST CHAIN's THREAD AS IT IS LAID AT A RETURN OF THE MAKER
(FirstThread.firstThread, Honest/Thread/TheFirstThread.lean), UNDER THE HEAD AT THE RETURN AND "THE
MAKER RETURNS" ALONE, THE FOUR LIGHT ONES OF THIS KIND's FIVE DEBTS AT BORDER 341 HOLD: it plays,
the form holds behind it, what stays open rides past it, and its step accepts. No premise is left on
the thread's letters for "keeps" and for the riders.

WHAT IT IS NOT.
  * THE FIFTH DEBT IS NOT HERE: ExchangeS, that what the member owes is delivered, bears the weight
    of this kind's completeness, and it stands under the twelve fields of K6HeadBelow
    (Honest/K6/Term/Statements.lean: DeliversAtTheBorder), of which no value is shown.
  * ALL FOUR ARE LIGHT AT THIS SUB-PROTOCOL: none says that a sent value is right. PlaysS: the
    row's parts return at all challenges that fit; nothing of the invariant is spent, no column is
    read, and its half on new trees speaks of an empty list. AcceptedS: the member's decision
    compares no sent value. RidesPastS and BehindS read no sent value.
  * None of the four says that a verifier accepts a proof. Each speaks only where the thread's
    invariant holds in front of member 341; whether it holds at any run up to that border is other
    kinds' debt and the frame's.
  * THE THREAD's PROVER IS NOT YET THE PROVER THAT RUNS. The thread is laid at the maker's prover
    and reads that prover's stored tables. The online honest prover runs the maker's prover with the
    committer's columns and key laid in (framedProver, E2E/OutputHeadAtTheHonestProver.lean). The
    two are one only under TableIsTheCommitters (E2E/TheHonestProverStatements.lean), which nothing
    here shows. Where its clause on the columns fails, the invariant holds at no stand of the honest
    prover's run, and the four say nothing of that run.
  * No theorem of this file sets the six values of the honest prover's own filling: fourAtTheFilling
    stands at that filling's form. E2E/OutputHeadAtTheFirstThread.lean sets them.
  * The head at the return (HeadAtReturn, which holds the library's hypothesis on the first chain,
    P5J.AtMgA: the full size and the format's second hash function alone) and "the maker returns" are
    premises. They are shown together at no files at these two fillings. HeadAtReturn fixes two
    letters of the hypothesis, the data (dpZ files) and the run (theProofRun (asDescriptionFiles files)), which
    the statements of E2E/OutputHeadAtTheHonestProver.lean leave general: these are the more
    general.
  * The thread's parts (FirstThreadParts: the Script and the falls' stated numbers), the run's input
    and the letter Said are letters: nothing is said on which values are the honest run's.
  * Nothing on soundness or on what a proof hides.

WORDS. As in the head of Honest/K6/Term/Statements.lean (border, thread, letter, seat, rider). The
maker is onlineProverFromPublicFiles (Honest/AtPure.lean). The row is this kind's sender, headRow (Honest/K6/Part.lean).
Member 341 is counted from 0.

WHAT IT IS. No definition; eight theorems.

  clauseAtThisKind         at this kind's place the clause that the letter fHeadJ lays is K6Keeps
                           together with formsBehind, the public tests of the claims on linear forms
                           at the state behind the member. No premise
  clauseCanFail            a control: that clause fails at every state behind that bears a mark
  clauseGivesKeeps         what fHeadJ lays for this kind gives the kind's own clause K6Keeps. No
                           premise
  clauseIsGivenBehind      under the library's hypothesis: where K6Keeps holds and the thread's form
                           holds behind the member, fHeadJ's clause for this kind holds
  noRiderSpeaksAt341       no clause of the frame's list of riders csHead spans border 341: its
                           three arguments cannot make the riders' sentence fail there. Beside that
                           sentence the thread's clause on riders holds one on the reply, of which
                           this says nothing
  fourAtTheFirstThread     the four, at every value of the maker's type that has the head and the
                           seat
  fourAtTheBaseProver      the four at the maker's return at the base filling
  fourAtTheFilling         the four at the maker's return at that filling read through two readers

CALLED. fourAtTheHeadsRiders (Honest/K6/Term/AtTheBorder.lean); seatAtTheBase, seatAtTheFilling
(Honest/K6/Term/SideAtFilling.lean); fHead_K6 (Honest/Thread/FHead.lean); formsBehind_of_form
(Honest/Thread/FHeadF.lean); csHead_span (Honest/Thread/CsHead.lean); k6_at341
(Johnson/Desc/K6/Honest/Law/KeepsAtHead.lean).
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.K6.Term.AtTheBorder
import Johnson.Desc.ProofFile.Honest.K6.Term.SideAtFilling
import Johnson.Desc.K6.Honest.Law.KeepsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6 k6_at341)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF fHead_K6 fHeadJ formsBehind formsBehind_of_form
  HeadAtReturn FirstThreadParts firstClauses)

/-! ## 1 The two premises on "keeps", at the letter fHeadJ -/

section Clauses
variable (Zp : Pub) (cF : Chain TS Cl) (G : Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- **At this kind's place the letter's clause is K6Keeps together with the public tests of the
claims on linear forms at the state behind the member.** The four further clauses of fHeadJ are
"True" at this kind. No premise. -/
theorem clauseAtThisKind (Dp : VerifiableInference.Desc.First.PubData) (s s' : TS) :
    fHeadJ Zp cF G take P11 p12 P13 Dp .K6 plK6 s s' ↔ K6Keeps s s' ∧ formsBehind Dp plK6 s' :=
  ⟨fun clause =>
      ⟨(fHead_K6 Zp cF G take P11 p12 P13 plK6 s s').1 clause.1.1.1.1.1, clause.1.1.1.1.2⟩,
    fun both => ⟨⟨⟨⟨⟨(fHead_K6 Zp cF G take P11 p12 P13 plK6 s s').2 both.1, both.2⟩, trivial⟩,
      trivial⟩, trivial⟩, trivial⟩⟩

/-- **What the letter lays for this kind gives the kind's own clause.** No premise. -/
theorem clauseGivesKeeps (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ s s', fHeadJ Zp cF G take P11 p12 P13 Dp .K6 plK6 s s' → K6Keeps s s' :=
  fun s s' clause => ((clauseAtThisKind Zp cF G take P11 p12 P13 Dp s s').1 clause).1

/-- A control. **The clause can fail**: it fails at every state behind the member that bears a mark.
-/
theorem clauseCanFail (Dp : VerifiableInference.Desc.First.PubData) (s s' : TS)
    (marked : s'.failed ≠ none) : ¬ fHeadJ Zp cF G take P11 p12 P13 Dp .K6 plK6 s s' :=
  fun clause => marked (clauseGivesKeeps Zp cF G take P11 p12 P13 Dp s s' clause).1

end Clauses

variable {W₀ Rc X₀ : Type}

/-- **Behind a step, the kind's own clause gives what the letter lays for this kind**: KeepsIsGiven
(Honest/K6/Term/Statements.lean) at keepsByKind := fHeadJ at the hypothesis's own public data, at
all other letters of the thread. One premise: the library's hypothesis on the first chain. -/
theorem clauseIsGivenBehind {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
    {Np : H2U.Places4} {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {Ky : Type}
    (H : Prover W₀ Rc Inst Ky Cells X₀ Unit)
    (Q : Script Bk (Local W₀ Rc Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc Inst Cells → Prop)
    (riders : List (RiderCl (Local W₀ Rc Inst Cells) TS)) (w : Local W₀ Rc Inst Cells)
    (G : Ground) (take : Nat → Bool) (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (p12 : VerifiableInference.Desc.K12.P12) (P13 : VerifiableInference.Desc.K13.Where) :
    KeepsIsGiven h H Q test carryX item n₁ n₂ b₀ Vd riders
      (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD) w :=
  fun _ s s' _ kept form => (clauseAtThisKind Zp cF G take P11 p12 P13 h.𝔇.pubD s s').2
    ⟨kept, formsBehind_of_form h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf riders)
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w k6_at341 form⟩

/-- **No clause of the frame's list of riders spans border 341**: at that border the riders'
sentence holds whatever the list's three arguments are. It says nothing of the clause on the reply,
which the thread holds beside that sentence. No premise. -/
theorem noRiderSpeaksAt341 {W : Type} (nextFree : Nat) (afterDigits : Nat → TS → Prop)
    (callsReturned : Nat → Option OnBytes.Model.Forest.Heard → Prop) (input : W) (s : TS) :
    ridersOf (csHead nextFree afterDigits callsReturned) 341 input s := by
  intro clause isRider lo hi
  rcases csHead_span isRider with ⟨a, -⟩ | ⟨l, hl, e, e'⟩ | ⟨g, hg, e, e'⟩ | ⟨g, hg, e, e'⟩ <;>
    omega

/-! ## 2 The four, at the first chain's thread at a return of the maker -/

/-- **Four of the five at the first thread**, each only where the thread's invariant holds in front
of the member. Two premises: the head at A, which holds the library's hypothesis on the first chain,
and the seat: the first side of A's prover at the member's place is the row, at a reader of the
committed digits (weights) and a ground (G) that are letters. -/
theorem fourAtTheFirstThread {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (head : HeadAtReturn files A) (weights : W₀ → Weights) (G : Ground)
    (seat : K6HalfAt A.Z A.H (headWit' id weights A.Z G)) (parts : FirstThreadParts A)
    (w : Local W₀ Rc Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc Inst Cells) Unit → Prop) :
    PlaysS (FirstThread.firstThread head parts w) Said 341 ∧
    BehindS (FirstThread.firstThread head parts w) Said 341 ∧
    RidesPastS (FirstThread.firstThread head parts w) Said 341 ∧
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      AcceptedS (FirstThread.firstThread head parts w) Said fall 341 := by
  have gives : ∀ s s', firstClauses head .K6 plK6 s s' → K6Keeps s s' :=
    clauseGivesKeeps _ _ _ _ _ _ _ _
  unfold FirstThread.firstThread FirstThread.firstLetters
  exact fourAtTheHeadsRiders W₀ Rc files _ _ A.Z head.places head.firstChain head.look head.head
    weights G _ X₀ A.H seat A.B parts.script _ _ _ _ _ _ _ _ _ (firstClauses head) w Said gives
    (clauseIsGivenBehind head.head A.H parts.script _ _ _ _ _ 339 _ _ w _ _ _ _ _)

/-- **The four at the base prover**: the maker's return at the base filling; each only where the
thread's invariant holds in front of the member. Two premises: "the maker returns at the base
filling" and the head at the return. -/
theorem fourAtTheBaseProver {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (returns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (head : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins Inst Cells) Unit → Prop) :
    PlaysS (FirstThread.firstThread head parts w) Said 341 ∧
    BehindS (FirstThread.firstThread head parts w) Said 341 ∧
    RidesPastS (FirstThread.firstThread head parts w) Said 341 ∧
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      AcceptedS (FirstThread.firstThread head parts w) Said fall 341 :=
  fourAtTheFirstThread head (I.weights A.Z) A.G (seatAtTheBase head.head I S O returns) parts w Said

/-- **The four at the base filling read through two readers**; each only where the thread's
invariant holds in front of the member. The honest prover's own filling has this form; this theorem
does not set its six values. Two premises: "the maker returns at that filling" and the head at the
return. -/
theorem fourAtTheFilling {W₀' Rc' : Type} {files : VerifierAndGoals.PublicFiles} (readIndex : W₀' → W₀)
    (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (returns : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A)
    (head : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀' Rc' Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local W₀' Rc' Inst Cells) Unit → Prop) :
    PlaysS (FirstThread.firstThread head parts w) Said 341 ∧
    BehindS (FirstThread.firstThread head parts w) Said 341 ∧
    RidesPastS (FirstThread.firstThread head parts w) Said 341 ∧
    ∀ fall : Nat → TS → List Fmt.Drawn → Option String,
      AcceptedS (FirstThread.firstThread head parts w) Said fall 341 :=
  fourAtTheFirstThread head (fun index => I.weights A.Z (readIndex index)) A.G
    (seatAtTheFilling head.head readIndex readRandomness namedIndex I S O returns) parts w Said

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.clauseAtThisKind
#print axioms ProofFile.Honest.K6.Term.clauseGivesKeeps
#print axioms ProofFile.Honest.K6.Term.clauseCanFail
#print axioms ProofFile.Honest.K6.Term.clauseIsGivenBehind
#print axioms ProofFile.Honest.K6.Term.noRiderSpeaksAt341
#print axioms ProofFile.Honest.K6.Term.fourAtTheFirstThread
#print axioms ProofFile.Honest.K6.Term.fourAtTheBaseProver
#print axioms ProofFile.Honest.K6.Term.fourAtTheFilling
