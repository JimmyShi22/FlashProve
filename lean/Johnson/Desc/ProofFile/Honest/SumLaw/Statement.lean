-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Statement.lean: THE STATEMENTS OF THE LAW OF THE MASKED
SUMCHECK's HONEST PART, FOR EVERY CALL OF THE VERIFIER's FIRST TEXT: seven statements, each a
definition of a proposition, and one definition with code that they need (`hidingCoin`). No proof
stands in this file: the proofs are in Law.lean and LawEnds.lean of this folder. None of the seven
is one of the library's goals: they are lemmas' statements. The prover's text is `sumPart`
(Honest/Sum.lean); the verifier's is the part's first text (Johnson/Desc/Part/MaskedSum4.lean:
`hear`, `row`). The call is any `SumJob`'s: a lead of any length; variables that are summed plainly
or at a point, each with its number of coefficients; with end values or without.

IN PLAIN WORDS. c: any coins. t: any state in front of the part. seen: whatever is shown in front of
the part: any rounds and, handed or not, any columns opened (the frame's `Seen`); the part's moves
are handed it with their own rounds laid behind, and the job's functions read it (`Front.seen`); in
a run it is the frame's `Mid.shown`: the rounds that `play` has shown so far, and the field `opened`
as the state holds it (`none` where the player hands no columns). ds: any challenges that pass
`drawsOk` at the call. k: the call as it stands in the run (`SumJob.callAt`).
  `SumSays`    played alone, all moves of the part answer: there are rounds.
  `SumHeard`   where `shapeOk k`, at every claimed form C and every ledger F that is ready for the
               call (`LedgerReady`), the verifier's `hear` accepts these rounds.
  `SumClaim`   THE CORE. Where `hear` has accepted them, at any C and F: what it hands back has the
               run's challenges; and for all σ and cf such that the caller's summand sums, round by
               round, from σ to cf (`SumsTo`): THE LAST RUNNING CLAIM READS AS the hiding
               polynomial of the coins that the part spent for it, at the challenges, plus eps cf,
               plus eps (T - σ) times the product of all psi. T: what `hear` made of C and the
               ledger (`Heard.target`). No row, no later ledger and no mask entry is named. It is,
               to the letter, the premise on the claim of `rowForm_zero`
               (Johnson/Desc/Part/MaskedSumRow.lean), at the summand's value cf.
  `SumLeft`    a corollary, for a caller that makes its row by `row`, at once or late: at every
               sized ledger F' at which `row h S0 kept F'` returns a form f and a ledger G', in the
               world of every ledger H later than G' (G' is one): if (1) under the sumcheck's own
               slots the mask entries are the coins spent for the hiding polynomial, and (2) the
               summand sums from C's value ON THE HIDDEN VALUES to cf: f is worth
               eps (S0 + kept - cf). So it is worth 0 where cf is the caller's end term plus the
               value of what it keeps.
  `SumFirst`   the first message holds the job's lead values, each plus its coin; then one scalar.
  `SumLast`    at a call with end values: the last message holds the job's end values, each plus
               beta times its coin.
  `SumEnds`    at such a call: in the world of every ledger later than the one that `hear` hands
               back, the hidden value under an end value's slot is the job's end value, if the mask
               entry under that slot is the coin that the part spent for it.

WHAT A CALLER SUPPLIES. The job. `shapeOk` and `drawsOk` at the call. THAT ITS VERIFIER's OWN CALL
IS `J.callAt t.input (frontOf t seen)`, as data: the points the same elements, word for word. A
ledger F behind its own taking of the lead, ready for the call. The claimed form C. `SumsTo`. For
`SumLeft` and `SumEnds`: which coin is the mask entry under which slot. For `SumLeft`: that F' is
sized and that `row` returns there: at the hearing's own ledger by the library's
`row_returns_ready`; at a later one by its `row_returns_later`, whose premises (the own slots have
room there and are still free) are the caller's. For `SumEnds`: that F is sized (the first clause of
`LedgerReady`). To spend `SumClaim` in `rowForm_zero`: that lemma's premises on the variables, the
lengths and the challenges come from the library's `hear_spec`
(Johnson/Desc/Part/MaskedSumShape.lean) and `readAll_lens` (Johnson/Desc/Part/MaskedSumJoint.lean).
A caller need not know the hiding polynomial, nor the term that lies wholly in the coefficient which
is not sent (eps (T - σ) times the product of all psi): σ is any element, T is whatever `hear` made.

"Later" is the library's `OnBytes.PscRun.Later` (OnBytes/Tie/Pv/Psc/PscLater.lean), which is
reflexive and transitive. The hidden values are the ledger's: what was shown under a slot less the
slot's factor times its mask entry (`Fork.worldOf`); mask and entry are parameters. The field is the
library's extension field, the reading `Reading.gl`: what a part says is laid into words below the
prime, and that reading does not see the difference.

Limits. In seen every value of the field `opened` is ranged over (the frame's `Seen`: where the
player hands them, the columns that the sub-protocols before the round have read: in the first and
in the shared chain that chain's own alone, in the second chain the first's, the shared chain's and
its own): no premise is laid on it. THE VERIFIER's OTHER TWO TEXTS OF THE SUMCHECK ARE NOT REACHED:
for a kind that verifies by one of these, `SumSays`, `SumFirst` and `SumLast` alone serve as they
stand. The part stands here as `sumPart` itself, played alone, at a state that is typed at the job's
own parameters. NOT AMONG THE SEVEN, AND WHERE IT IS, all in this folder: that the frame's `play`
yields the rounds of `alone` (Plays.lean and PlaysWhole.lean, general in the part; Fits.lean and
PlaysSum.lean at `sumPart`, lifted too); what `Part.lift`, `Move.recoin` and moves in a row make of
them (Lift.lean); which challenges the rounds bear and how many they are, the way from the frame's
test on challenges at a sub-protocol's declared rounds to `drawsOk`, `rowForm`'s worth in any world,
the coins themselves, and `SumsTo` as the library's `Chain` (More.lean); numbers of the call, and
the coins at the premises' own indices (Counts.lean); the lifted part under one premise on the lift,
and that rounds which read nothing yield no column (LiftSame.lean). A caller's further tests on a
challenge (beta is not 0; elements alone) are the caller's. `SumsTo` is asked at the run's own
challenges alone, and at this seen alone. Nothing on soundness or on any property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms
import Johnson.Desc.Part.MaskedSumReady
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE addE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open OnBytes.Desc.First.P1 (hid psiProd)
open VerifiableInference.Desc.Part.MaskedSum (Call Var shapeOk ownSlots hear row LedgerReady Heard
  scalars)

/-- The coin that the part spends for the hiding polynomial's coefficient number i, read. -/
def hidingCoin {W X : Type} {name endName : String} {J : SumJob W X} (c : SumCoins name endName J)
    (i : Nat) : GE :=
  Reading.gl.val ((firstRun c).getD (J.shape.lead + i) zeroE)

/-- The statement that, played alone, all moves of the part answer. Proved as `sumSays`
(Honest/SumLaw/Law.lean). A lemma's statement, none of the library's goals. -/
def SumSays : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
    drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    ∃ rounds, alone (sumPart (V := V) name endName J) c t seen ds = some rounds

/-- The statement that, where the call passes `shapeOk`, the verifier's `hear` accepts the part's
rounds at every ledger that is ready for the call. Proved as `sumHeard` (Honest/SumLaw/Law.lean). A
lemma's statement, none of the library's goals. -/
def SumHeard : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (C : Aff) (F : Fork),
    shapeOk (J.callAt t.input (frontOf t seen)) = true →
    drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    LedgerReady C (J.callAt t.input (frontOf t seen)) F →
    ∃ h G, hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G)

/-- The statement of what the last running claim reads as, where `hear` has accepted the part's
rounds: the core of the seven. Proved as `sumClaim` (Honest/SumLaw/Law.lean). A lemma's statement,
none of the library's goals. -/
def SumClaim : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (C : Aff) (F G : Fork) (h : Heard),
    drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G) →
    h.eps = epsOf ds ∧ h.r = varsOf (J.callAt t.input (frontOf t seen)) ds ∧
      ∀ σ cf : GE,
        SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
          (jobPoly J t.input (frontOf t seen) (endRun c)) [] h.r σ cf →
        Reading.gl.val h.claim =
          hid ((J.callAt t.input (frontOf t seen)).all.map (Var.wt Reading.gl)) (hidingCoin c)
              (h.r.map Reading.gl.val) +
            Reading.gl.val h.eps * cf +
            Reading.gl.val h.eps * (Reading.gl.val h.target - σ) *
              psiProd ((J.callAt t.input (frontOf t seen)).all.map (Var.wt Reading.gl))
                (h.r.map Reading.gl.val)

/-- The statement of what the one claim that is left is worth on the hidden values, for a caller
that makes its row by `row`, at once or late; H: any ledger later than the one that `row` hands
back, that one among them. Proved as `sumLeft` (Honest/SumLaw/Law.lean). A lemma's statement, none
of the library's goals. -/
def SumLeft : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (C : Aff) (F G F' G' H : Fork) (h : Heard) (S0 : E) (kept f : Aff) (mask : Nat → GE)
    (entry : Nat → Nat → Nat → GE) (cf : GE),
    drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G) →
    OnBytes.PscRun.Sized F' → row h S0 kept F' = some (f, G') → OnBytes.PscRun.Later G' H →
    (∀ i, i < ownSlots (J.callAt t.input (frontOf t seen)).all →
      mask (F.next + i) = hidingCoin c i) →
    SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
      (jobPoly J t.input (frontOf t seen) (endRun c)) [] h.r
      (C.value Reading.gl (H.worldOf Reading.gl mask entry)) cf →
    f.value Reading.gl (H.worldOf Reading.gl mask entry) =
      Reading.gl.val h.eps *
        (Reading.gl.val S0 + kept.value Reading.gl (H.worldOf Reading.gl mask entry) - cf)

/-- The statement that the first message holds the lead's values, each plus its coin, and one scalar
more. Proved as `sumFirst` (Honest/SumLaw/LawEnds.lean). A lemma's statement, none of the library's
goals. -/
def SumFirst : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView),
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    ∃ (r : Fmt.RoundView) (rest : List Fmt.RoundView) (s : List E), rounds = r :: rest ∧
      scalars r.vals = some s ∧ s.length = J.shape.lead + 1 ∧
      ∀ i, i < J.shape.lead → Reading.gl.val (s.getD i zeroE) =
        Reading.gl.val ((J.lead t.input (frontOf t seen)).getD i zeroE) +
          Reading.gl.val ((firstRun c).getD i zeroE)

/-- The statement that, at a call with end values, the last message holds the job's end values, each
plus beta times its coin. Proved as `sumLast` (Honest/SumLaw/LawEnds.lean). A lemma's statement,
none of the library's goals. -/
def SumLast : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (e : VerifiableInference.Desc.Part.MaskedSum.Ends),
    J.shape.ends = some e → drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = e.n ∧
      ∀ j, j < e.n → Reading.gl.val (s.getD j zeroE) =
        Reading.gl.val ((J.ends t.input (frontOf t seen)
            ((varsOf (J.callAt t.input (frontOf t seen)) ds).take
              J.shape.vs.length)).getD j zeroE) +
          Reading.gl.val ((varsOf (J.callAt t.input (frontOf t seen)) ds).getLastD zeroE) *
            Reading.gl.val ((endRun c).getD j zeroE)

/-- The statement that, at a call with end values and a sized ledger, the job's end values lie under
the end values' slots. Proved as `sumEnds` (Honest/SumLaw/LawEnds.lean). A lemma's statement, none
of the library's goals. -/
def SumEnds : Prop :=
  ∀ (V W X : Type) (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (C : Aff) (F G H : Fork)
    (rounds : List Fmt.RoundView) (h : Heard) (e : VerifiableInference.Desc.Part.MaskedSum.Ends)
    (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
    J.shape.ends = some e → OnBytes.PscRun.Sized F →
    drawsOk (J.callAt t.input (frontOf t seen)) ds = true →
    alone (sumPart (V := V) name endName J) c t seen ds = some rounds →
    hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G) → OnBytes.PscRun.Later G H →
    ∀ j, j < e.n →
      mask (h.sEnd + j) = Reading.gl.val ((endRun c).getD j zeroE) →
      (H.worldOf Reading.gl mask entry).slot (h.sEnd + j) =
        Reading.gl.val ((J.ends t.input (frontOf t seen)
          ((varsOf (J.callAt t.input (frontOf t seen)) ds).take J.shape.vs.length)).getD j zeroE)

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.hidingCoin
#print axioms ProofFile.Honest.SumLaw.SumSays
#print axioms ProofFile.Honest.SumLaw.SumHeard
#print axioms ProofFile.Honest.SumLaw.SumClaim
#print axioms ProofFile.Honest.SumLaw.SumLeft
#print axioms ProofFile.Honest.SumLaw.SumFirst
#print axioms ProofFile.Honest.SumLaw.SumLast
#print axioms ProofFile.Honest.SumLaw.SumEnds
