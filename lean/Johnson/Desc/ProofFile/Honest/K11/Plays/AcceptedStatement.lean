-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedStatement.lean: THE THREAD's DEBTS `Plays` AND
`Accepted` (Honest/Thread/Pays.lean) AT THE MEMBER THAT IS THE MERGE OF THE CLAIMS ON THE WEIGHTS,
FROM "THE ROW's HALF STANDS IN THE THREAD's LIST OF HALVES": STATEMENTS ALONE: one definition that
is needed, and three definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none of the
three is one of the library's goals: they are lemmas' statements.

THE THREAD T IS A VARIABLE. The facts on its letters that are spent are named premises:
  member   the member number b is the kind's block as it stands alone at a seat (the field of that
           name of `K11Seated`, Honest/K11/Plays/ShareStatement.lean, in its own words)
  half     the half that the thread's list has at the seat's place is the row's
  ready    A DEBT, no fact on a letter: from the thread in front: `MergeReady` of the verifier's
           state

  `MergeReady P s`       no mark of failure; the head's link is open, nothing is owed by the round
                         in front, the claim and what the head heard are laid; the claim's sizes fit
                         its unit; the ledger's arrays have their size, the claim's value is laid
                         under its slot, the end value's slot is there and free, and the slots come
                         out at the plan's number: the premises on the state of
                         `HeadMergeDecideReturns`
                         (Johnson/Desc/K11/Returns/Statement.lean), and the mark. ALL ON THE STATE's
                         FORM: no value is tested
  `StepsOfHalf`          under half: the steps that the frame lays for the member are the row's, at
                         the coins that the book lends the row: so the field steps of `K11Seated`
                         follows, where its letter for the coins is what is lent
  `HeadMergePlaysHalf`   under member and half: `Plays T b`
  `HeadMergeAccepted`    under member, half and ready: `Accepted T fall b` AT EVERY fall: where the
                         row has been played, the member's own step says yes

Limits. The three premises are shown at no thread. ready is a debt on the form of a reached state.
Two premises of `Accepted` are not spent: the letter fall (this member has no fall of its own), and
that nothing of the member stops (this row has no stop). UNDER half THE SEAT's PLACE pl IS THE
KIND's OWN PLACE (`headMergePlace P`): the list's search hands back a half at pl, and the row's half
stands at that place. Nothing on what holds behind the yes. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.PlaysThrStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Claim Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind claimFits)
open Johnson.Desc.First.ForkMerge.Returns (mergeEndSlot)

/-- The verifier's state is ready for the merge's decision. Each "there is" is the one value of a
reader at the state. -/
def MergeReady (P : HeadMergeP) (s : S) : Prop :=
  s.failed = none ∧
    ∃ a claim x, s.here = .head a ∧ a.opened = true ∧ s.noneWaits = true ∧
      a.claim = some claim ∧ a.x = some x ∧ claimFits P.lay claim = true ∧ Sized a.F ∧
      Filled a.F x.sV ∧ mergeEndSlot P.lay.lk a.F < a.F.ns ∧
      ¬ Filled a.F (mergeEndSlot P.lay.lk a.F) ∧ a.F.next + 2 * P.lay.lk + 3 = P.nMsg

/-- The statement on the steps. The letters: as in `K11Seated`. Not proved here; a lemma's
statement, none of the library's goals. -/
def StepsOfHalf : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    ∀ (k : Coins Bk) w st,
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w)
          [IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl] T.hs = .ok st →
      ∃ q c,
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) pl
            (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts 0 =
          .ok ((q, (), ()), c, ()) ∧
        st = (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).steps
          (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) (T.φ.sees w) ((q, (), ()), c, ())

/-- The statement that it plays, from the half. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergePlaysHalf : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    Plays T b

/-- The statement that the member's step says yes. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadMergeAccepted : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X Pb : Type)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (name : String) (pl : Place),
    T.bs[b]? = some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) →
    (T.hs.find? fun g => g.place == pl) = some (headMergeHalf claims weights P) →
    (∀ k s m E, Thr T b k s m E → MergeReady P s) →
    ∀ fall, Accepted T fall b

end ProofFile.Honest.K11
