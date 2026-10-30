-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Terms.lean: the terms in which the law of the masked sumcheck's
honest part is stated (Honest/SumLaw/Statement.lean). Definitions with code, and one definition of a
proposition. No theorem. Nothing here is part of a prover: the prover's text is `sumPart`
(Honest/Sum.lean), the verifier's is Johnson/Desc/Part/MaskedSum4.lean.
Main names:
  seen, HERE AND IN ALL FILES OF THIS FOLDER BUT Walk.lean: a term of the frame's `Seen`
    (Honest/Frame.lean): the rounds shown in front and, where the player hands them, the columns
    that the sub-protocols before the round have read: in the first and in the shared chain that
    chain's own alone, in the second chain the first's, the shared chain's and its own. A move is
    handed it whole, as the frame's `Step.tell` hands `Mid.shown`.
    `seen.plus l` (the frame's `Seen.plus`): seen with the rounds l laid behind.
  `alone p c t seen ds`: THE ROUNDS OF A PART THAT IS PLAYED ALONE, as a view shows them: move by
    move, what the move says at the coins c, laid into words as the frame's `Step.tell` lays it,
    beside the round's challenge; the state hears the challenge and the move hands on, as in
    `Step.hear`. Nothing if a move answers with an error or the challenges are not as many as the
    moves. No stop is asked and no shape is held: `sumPart` has no stop, and the shape is another
    statement's.
  `SumCoins name endName J`: what `sumPart name endName J` is handed of coins.
  `firstRun c`, `endRun c`: its two stretches of coins, as lists of the program's elements.
  `frontOf t seen`: what the job's functions are handed of the run in front of the part: the
    challenges heard, what was handed on, and seen.
  `drawsOk k ds`: there are as many challenges as the call has entries, and each has as many
    elements as the entry for its round states. No other field of a challenge is read.
  `ownOf ds`: the part's challenges as elements. `epsOf`, `varsOf`: the first; those of the
    variables, Y's last.
  `jobPoly J w fr m rs`: the summand's polynomial of the round behind the challenges rs, as the
    job gives it: `round`, and behind all variables `inY`.
  `SumsTo ρ vs poly past rs c c'`: **what a caller has to show**: round by round, the sum of the
    summand's polynomial (cut or filled to the variable's number of coefficients) is the claim so
    far, which begins at c; the next claim is that polynomial's value at the round's challenge; the
    last is c'.

Where every variable has at least one coefficient and the challenges are as many as the variables,
`SumsTo` is the library's `Chain` (OnBytes/Desc/First/P1/SumCore.lean) at the polynomials of the
lists, cut or filled; the clause on degrees there is given by the cutting: More.lean of this folder
(`sumsTo_iff_chain`).

Limits. `SumsTo` speaks of one list of challenges. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (Var Call entries valueAt)

variable {V W X : Type}

/-- The moves of a part, played alone from a state on. -/
def aloneFrom {C : Type} (c : C) : List (Move C W X) → State W X → Seen → List Fmt.Drawn →
    Option (List Fmt.RoundView)
  | [], _, _, [] => some []
  | mv :: mvs, t, seen, d :: ds =>
    match mv.say c seen t with
    | .ok x =>
      let r : Fmt.RoundView := ⟨x.vals.map Said.got, d⟩
      (aloneFrom c mvs { t.hears d with own := mv.hand (t.hears d) } (seen.plus [r]) ds).map
          (r :: ·)
    | .error _ => none
  | _, _, _, _ => none

/-- **The rounds of a part that is played alone**, as a view shows them. -/
def alone (p : Part V W X) (c : p.Coins) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) : Option (List Fmt.RoundView) :=
  aloneFrom c p.moves t seen ds

/-- What the masked sumcheck's part is handed of coins. -/
abbrev SumCoins (name endName : String) (J : SumJob W X) : Type :=
  Handed ⟨0, 0⟩ ((name, ⟨0, ownRun J.shape⟩) :: endRuns endName J.shape.ends) []

/-- Its first stretch: the lead's mask entries, then the hiding polynomial's coefficients. -/
def firstRun {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) : List E :=
  coinsE c.2.1.1

/-- Its second stretch: the end values' mask entries. -/
def endRun {name endName : String} {J : SumJob W X} (c : SumCoins name endName J) : List E :=
  endCoins endName J.shape.ends c.2.1.2

/-- What the job's functions are handed of the run in front of the part. -/
def frontOf (t : State W X) (seen : Seen) : Front X := ⟨t.heard, t.own, seen⟩

/-- There are as many challenges as the call has entries, and each has as many elements as the entry
for its round states. -/
def drawsOk (k : Call) (ds : List Fmt.Drawn) : Bool :=
  ds.map (·.elems.length) == (entries k).map (·.drawE)

/-- The part's challenges as elements. -/
def ownOf (ds : List Fmt.Drawn) : List E := drawnE ds

/-- The first challenge. -/
def epsOf (ds : List Fmt.Drawn) : E := (ownOf ds).headD zeroE

/-- The variables' challenges, Y's last. -/
def varsOf (k : Call) (ds : List Fmt.Drawn) : List E := ((ownOf ds).drop 1).take k.all.length

/-- The summand's polynomial of the round behind the challenges rs, as the job gives it. m: the end
values' mask entries. -/
def jobPoly (J : SumJob W X) (w : W) (fr : Front X) (m rs : List E) : List E :=
  if rs.length < J.shape.vs.length then J.round w fr rs else J.inY w fr rs m

/-- **Round by round, the summand's polynomials sum from c to c'.** past: the challenges of the
variables passed. rs: those of the variables vs. -/
def SumsTo {K : Type} [CommRing K] (ρ : Reading K) :
    List Var → (List E → List E) → List E → List E → K → K → Prop
  | [], _, _, [], c, c' => c = c'
  | v :: vs, poly, past, r :: rs, c, c' =>
    ρ.val (sumOf v (padTo v.d (poly past))) = c ∧
      SumsTo ρ vs poly (past ++ [r]) rs (ρ.val (valueAt (padTo v.d (poly past)) r)) c'
  | _, _, _, _, _, _ => False

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.aloneFrom
#print axioms ProofFile.Honest.SumLaw.alone
#print axioms ProofFile.Honest.SumLaw.SumCoins
#print axioms ProofFile.Honest.SumLaw.firstRun
#print axioms ProofFile.Honest.SumLaw.endRun
#print axioms ProofFile.Honest.SumLaw.frontOf
#print axioms ProofFile.Honest.SumLaw.drawsOk
#print axioms ProofFile.Honest.SumLaw.ownOf
#print axioms ProofFile.Honest.SumLaw.epsOf
#print axioms ProofFile.Honest.SumLaw.varsOf
#print axioms ProofFile.Honest.SumLaw.jobPoly
#print axioms ProofFile.Honest.SumLaw.SumsTo
