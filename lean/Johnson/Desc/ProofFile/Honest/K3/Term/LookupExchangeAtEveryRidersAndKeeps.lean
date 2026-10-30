-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk and the thread's other letters are variables.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupExchangeAtEveryRidersAndKeeps.lean: the honest side of
the kind "lookup" (K3), at the first chain's letters at the library's head (`lettersHead`,
Honest/Thread/FirstHead.lean). The debt `ExchangeS` (Honest/Thread/PaysS.lean) does not read the
letter "keeps", and it passes from fewer riders to more. So it is enough to show it at no rider and
at the lookups' own clause of "keeps", and there the debt `BehindS` at a lookup's border is paid. No
definition; three theorems.

  `exchangeDoesNotReadKeeps`   one premise beside the head: `ExchangeS` at one letter "keeps"
      `ExchangeS` at every other letter "keeps", at every number b
  `lookupBehindAtNoRidersAndTheLookupsOwnClause`   three premises beside l < 25: the head;
      saidGivesWordsBelowThePrime; replyBorderIsNotBehind
      `BehindS` at `borderOf l d`, at the riders of the empty list and "keeps" := `k3KeepsAt Zp`
  `exchangeAtEveryRidersAndKeeps`   one premise beside the head: `ExchangeS` at these two letters
      `ExchangeS` at every letter "rides" and every letter "keeps", at every number b

The premises. The head: the library's hypothesis `P5J.AtMgA`, under which the letters are laid.
saidGivesWordsBelowThePrime: Said gives `SaidOk`. replyBorderIsNotBehind: the border b₀ from which
the reply's clause speaks is not the border behind this lookup.

How the proofs go. `ExchangeS` is made of the list bs, `ThrS`, the test `drawsFit`, the member's
step, the row's list owes and `Items`: none of these names the field keeps of a `Thread`: the first
theorem's proof is its premise, by unfolding. The second is a call of
`lookupBehindFromTheRidersColumns` (Honest/K3/Term/LookupBehindAndRidesPast.lean), general in the
list of riders' clauses and in the clause by kind: at the empty list its two columns ask nothing,
and at the lookups' own clause its premise on the rest of "keeps" is
`stepPaysTheLookupClauseItself`. The third: the frame's `head_exchangeS_lift`
(Honest/Thread/HeadLift.lean), then the first.

Limits. `ExchangeS` and `BehindS` are implications from `ThrS` and the member's step: no state is
shown to meet these at any border. At fewer riders `ThrS` says less, so `ExchangeS` there says more:
whoever shows it there has the heavier task. The full size alone. Nothing on soundness,
completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBehindAndRidesPast
import Johnson.Desc.ProofFile.Honest.Thread.HeadLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_exchangeS_lift)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (atHead : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **`ExchangeS` DOES NOT READ THE LETTER "keeps".** -/
theorem exchangeDoesNotReadKeeps (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (oneKeeps otherKeeps : Place → TS → TS → Prop) {b : Nat}
    (atOneKeeps : ExchangeS
      (lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd oneKeeps w).thread Said b) :
    ExchangeS (lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd otherKeeps w).thread Said b :=
  atOneKeeps

/-- **`BehindS` AT A LOOKUP's BORDER, AT NO RIDER AND AT THE LOOKUPS' OWN CLAUSE OF "keeps".**
Conditional on the head, a Said that gives `SaidOk`, and a border b₀ that is not the one behind this
lookup. -/
theorem lookupBehindAtNoRidersAndTheLookupsOwnClause
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25) (d : Bool) (replyBorderIsNotBehind : b₀ ≠ borderOf l d + 1) :
    BehindS (lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd (ridersOf [])
      (kpBy fun _ place => k3KeepsAt Zp place) w).thread Said (borderOf l d) :=
  lookupBehindFromTheRidersColumns atHead H Q test carryX item n₁ n₂ b₀ Vd []
    (fun _ place => k3KeepsAt Zp place) w Said saidGivesWordsBelowThePrime linkBelow d
    replyBorderIsNotBehind (stepPaysTheLookupClauseItself _ Said _ _)
    (fun _ isListed => absurd isListed List.not_mem_nil)
    (fun _ isListed => absurd isListed List.not_mem_nil)

/-- **FROM NO RIDER AND THE LOOKUPS' OWN CLAUSE TO EVERY LETTER "rides" AND EVERY LETTER "keeps".**
-/
theorem exchangeAtEveryRidersAndKeeps {b : Nat}
    (atNoRidersAndTheLookupsOwnClause : ExchangeS
      (lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd (ridersOf [])
        (kpBy fun _ place => k3KeepsAt Zp place) w).thread Said b)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop) :
    ExchangeS (lettersHead atHead H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b :=
  exchangeDoesNotReadKeeps atHead H Q test carryX item n₁ n₂ b₀ Vd w Said Rd
    (kpBy fun _ place => k3KeepsAt Zp place) Kp
    (head_exchangeS_lift atHead H Q test carryX item n₁ n₂ b₀ Vd (ridersOf [])
      (kpBy fun _ place => k3KeepsAt Zp place) w Vd Rd (fun _ valid => valid)
      (fun _ _ _ _ _ isListed => absurd isListed List.not_mem_nil) Said
      atNoRidersAndTheLookupsOwnClause)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.exchangeDoesNotReadKeeps
#print axioms ProofFile.Honest.K3.Term.lookupBehindAtNoRidersAndTheLookupsOwnClause
#print axioms ProofFile.Honest.K3.Term.exchangeAtEveryRidersAndKeeps
