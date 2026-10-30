-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Sum.lean: the prover's side of the masked sumcheck, as executable
definitions in the types of Honest/Frame.lean: the part that computes the sumcheck's messages
(`sumPart`), a part that sends a mask row (`maskPart`), and a candidate simulator for each
(`sumSim`, `maskSim`). Definitions only: no theorem is stated.

The verifier's side is Johnson/Desc/Part/MaskedSum4.lean, whose head explains the protocol and its
terms. The lead is the caller's own scalars at the start of the first message; the ends are a
further variable Y and the end values that are sent last; a slot is the number of a scalar that is
sent. The masked sumcheck has no place of its own in a protocol description: the sub-protocols that
sum something call it. In the same way `sumPart` has type parameters of its own, and the prover's
side of a sub-protocol puts it into its list of parts with `Part.lift`.

  1  `addL`, `scaleL`, `padTo`, `sumPow`, `sumOf`, `psiL`   polynomials as lists of coefficients,
     lowest first; the two ways of summing g over a variable: plainly, g(0) + g(1), and at a point
     z, (1 - z) g(0) + z g(1)
  2  `wOf`, `tailSum`, `hAt`, `sentOfL`   the hiding polynomial H, from its coefficients: its sum,
     and its round polynomial at the challenges so far; which coefficients of a round polynomial
     are sent
  3  `Front`, `withPoints`, `SumJob`, `SumJob.callAt`, `scalarsOf`, `runOf`, `ownRun`, `endRuns`,
     `sumPart`   what the caller supplies about its summand (a public shape, and values that depend
     on the run); the counts; the part
  4  `sumSim`   a candidate simulator for `sumPart`
  5  `MaskJob`, `maskPart`, `maskSim`   a part that sends a mask row; a candidate simulator for it

The hiding polynomial. It follows the verifier's `hidingAt`: H(X_1 .. X_k) is the sum over l of
w_l(X_l) times the product of psi_j(X_j) over all j above l, where psi_j is the polynomial in X_j
whose sum over that variable is 1. The coefficients are ordered by variable, then by degree from 1
up; only the last variable has a constant coefficient. They are the mask entries under the
sumcheck's own slots.

What is sent, under the verifier's names for the rounds. S is the caller's summand; eps and beta are
challenges.
  "PSC epsilon"   each of the caller's lead values plus its mask entry, then the sum of H
  "PSC round"     once for each variable: the round polynomial of H + eps S without the coefficient
                  that the verifier derives (`complete`), which is the linear one for a plain sum
                  and the constant one for a sum at a point
  "PSC Y"         the same for the further variable Y, in which each end value is its true value
                  plus Y times its mask entry
  "PSC values"    each end value plus beta times its mask entry
What is sent here is right, although the polynomial that the verifier completes is not the one that
is computed here. By the format's page (docs/format/11-1-machinery.md, the masked sumcheck's honest
prover) the honest round polynomial has one more term: what the claimed sum is on the shown values,
less what it is on the true ones, times the product of all psi_i(X_i). In each round that term is a
multiple of psi(X), which is X for a plain sum and 1 for a sum at a point, so it lies wholly in the
coefficient that is not sent. But the polynomial that `hAt` and `SumJob.round` give sums to the
running claim only if the mask entries under the slots that the claimed sum names are 0. These are
the lead's entries, or an earlier part's at a call without a lead. `sentOfL` is meant as the list
version of the library's `sentOf`, which works on polynomials
(Johnson/Desc/Part/MaskedSumHonest.lean); no statement here relates the two.

Coins. `sumPart` takes no coins of its own. It spends blocks of coins borrowed from other parts
(`Ahead`, Honest/Frame.lean), all of them elements of the extension field. The first block holds, in
the order of the slots, the lead's mask entries and H's coefficients. If the call has ends, a second
block under a name of its own holds the end values' mask entries; a caller can point it at the same
owner or at another. (At a merge the end value's mask is an entry of another message than the
segment's mask row; merge and segment are terms of the format's pages, docs/format/.) Every move is
given both blocks. The part leaves the state that parts pass on (`own`) unchanged.

What is public and what depends on the run. The shape of a call is fixed: the number of lead
scalars, each variable's way of summing and its number of coefficients, and the ends. The counts are
computed from the shape alone. The points at which variables are summed, and the summand, depend on
the run: in the verifier's sub-protocols a point is computed from earlier challenges, and a summand
can have a factor that was sent earlier. So the caller's functions are given, besides the input, a
`Front`: the challenges before the part, the state that was passed on, and what the move was handed
(`Seen`) with the part's own rounds cut off (`Seen.front`): the rounds shown before the part, and
the columns opened just as they were handed. They are given the part's own challenges as the
variables' values (`State.lately`).
A job that reads `Front.seen` needs this: the mask entries behind the items that it reads and the
entries that the part spends are disjoint. Two tests of `ProverCoinCounts.clauses` (Honest/Frame.lean) bear on
it. One: no coin stands in two entries that spend it. The other: no coin that a part spends goes to
an earlier part, or to the same part as carried. Nothing in this file checks the condition. It is
a condition on the rounds: of a job that reads the columns (`Front.seen.opened`) it says
nothing.

Limits.
  * The arithmetic is the programs' arithmetic on machine words, in its Lean form
    (OnBytes/Field/Ext.lean).
  * Nothing here checks what a caller puts into a `SumJob`: that `round` is the summand's partial
    sum, that `inY` and `ends` agree with it, or that the lead's values are those that the claimed
    sum names.
  * A caller's list of values that is too short is padded with 0, and one that is too long is cut;
    a variable for which `SumJob.points` has no point keeps the shape's placeholder (`withPoints`).
    A challenge without a field element counts as 0. No move returns an error. So a job that reads
    `Front.seen.opened` cannot keep that field's duty (Honest/Frame.lean, `Seen.opened`: at `none`
    it errs).
  * `scalarsOf` counts d - 1 scalars for a variable with d coefficients. `sumPart` sends that many
    if d is at least 2, which the verifier's check on the plan requires (`shapeOk`,
    Johnson/Desc/Part/MaskedSum4.lean). Nothing here requires it of a job's shape: a plainly
    summed variable with d = 1 sends one scalar and is counted as none.
  * A structure literal of a `Front` that omits `seen` stands where no round is shown and no column
    is handed (`Seen.bare []`).
  * `maskPart` is a pattern and not a sender of this protocol: one mask row alone in its own tree,
    one sample's answer, the code a parameter, no named pad.
  * `sumSim` and `maskSim` are definitions, and this file states nothing that relates them to
    `sumPart` and `maskPart`.
  * In `maskSim` the bound on positions, the output beyond it, the single answer and the symbol's
    width are this file's own choices.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.Part.MaskedSum4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Slice (toE ofE toF)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots valueAt total psiAt)

variable {V W X Pb : Type}

/-! ## 1 Polynomials as lists -/

/-- The sum of two polynomials. -/
def addL : List E → List E → List E
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => addE x y :: addL a b

/-- `k` times a polynomial. -/
def scaleL (k : E) (a : List E) : List E := a.map (mulE k)

/-- Exactly `n` coefficients: padded with zeros at the end, or cut. -/
def padTo (n : Nat) (a : List E) : List E := (a ++ List.replicate (n - a.length) zeroE).take n

/-- The sum of X ^ t over a variable: 0 ^ t + 1 for a plain sum, (1 - z) 0 ^ t + z at a point z. -/
def sumPow : Var → Nat → E
  | .plain _, 0 => addE oneE oneE
  | .plain _, _ + 1 => oneE
  | .point _ _, 0 => oneE
  | .point z _, _ + 1 => z

/-- The sum of a polynomial over a variable. -/
def sumOf (v : Var) (g : List E) : E := total (g.zipIdx.map fun x => mulE x.1 (sumPow v x.2))

/-- psi: the polynomial in the variable whose sum is 1: X for a plain sum, 1 for a sum at a point.
-/
def psiL : Var → List E
  | .plain _ => [zeroE, oneE]
  | .point _ _ => [oneE]

/-! ## 2 The hiding polynomial -/

/-- H's coefficients, split by variable: each w_l as a polynomial. -/
def wOf : List Var → List E → List (List E)
  | [], _ => []
  | [v], u => [padTo v.d u]
  | v :: vs, u => (zeroE :: padTo (v.d - 1) u) :: wOf vs (u.drop (v.d - 1))

/-- The sum, over these variables, of the terms of H that belong to them. -/
def tailSum : List (Var × List E) → E
  | [] => zeroE
  | (v, w) :: rest => addE (sumOf v w) (mulE (sumPow v 0) (tailSum rest))

/-- **H's round polynomial.** The list pairs each variable with its w. `rs`: the challenges of the
first variables. The result is the polynomial in the next variable: H with the first variables set
to `rs` and the later ones summed. It is [] if `rs` has a challenge for every variable. `a` is an
accumulator for the terms of the variables passed so far; the caller supplies 0. -/
def hAt : List (Var × List E) → List E → E → List E
  | [], _, _ => []
  | (v, w) :: rest, [], a => addL (addL (scaleL a (psiL v)) w) [tailSum rest]
  | (v, w) :: rest, r :: rs, a => hAt rest rs (addE (mulE a (psiAt v r)) (valueAt w r))

/-- What is sent of a round polynomial: all of its d coefficients except the one that the verifier
derives. -/
def sentOfL : Var → List E → List E
  | .plain d, g => (padTo d g).take 1 ++ (padTo d g).drop 2
  | .point _ d, g => (padTo d g).drop 1

/-! ## 3 The part -/

/-- What a caller's functions are given of the run, besides the input: the challenges before the
part, the state that was passed on, and the rounds shown before the part, as a view shows them
(items in the clear and challenges), and, where they are handed, the columns opened. So a summand
can depend on a value that was sent and that
depends on a coin. `seen` is what every move is given (`Seen`), cut off before the part's own
rounds; its columns opened are carried on as they were handed (`Seen.front`). It has a default
value (`Seen.bare []`: no round, and no columns handed), so a structure
literal may omit it; an anonymous constructor ⟨heard, own⟩ with two components does not typecheck.
-/
structure Front (X : Type) where
  heard : List Fmt.Drawn
  own : X
  seen : Seen := .bare []

/-- A shape's variables with points filled in: the variables that are summed at a point take them in
order. A variable for which none is left keeps the shape's placeholder, and surplus points are
dropped. -/
def withPoints : List Var → List E → List Var
  | [], _ => []
  | .plain d :: vs, zs => .plain d :: withPoints vs zs
  | .point _ d :: vs, z :: zs => .point z d :: withPoints vs zs
  | .point z d :: vs, [] => .point z d :: withPoints vs []

/-- **What the caller supplies about its summand**, as executable functions. The shape is public and
fixed. The points and the summand depend on the run: each function is given the input and a `Front`.
-/
structure SumJob (W X : Type) where
  /-- the number of lead scalars, each variable's way of summing and its number of coefficients, and
  the ends. The counts are computed from it alone and read no point: for a variable that is summed
  at a point the shape holds a placeholder -/
  shape : Call
  /-- the points of the variables that are summed at a point, in order -/
  points : W → Front X → List E
  /-- the lead's true values, `shape.lead` of them -/
  lead : W → Front X → List E
  /-- all coefficients of the summand's round polynomial in the next variable, from the challenges
  of the earlier variables -/
  round : W → Front X → List E → List E
  /-- the same in Y, from all variables' challenges and the end values' mask entries -/
  inY : W → Front X → List E → List E → List E
  /-- the true end values, from all variables' challenges -/
  ends : W → Front X → List E → List E

/-- The call in a run: the shape with the run's points. -/
def SumJob.callAt (J : SumJob W X) (w : W) (f : Front X) : Call :=
  { J.shape with vs := withPoints J.shape.vs (J.points w f) }

/-- How many scalars each round of a call sends. -/
def scalarsOf (k : Call) : List Nat :=
  [k.lead + 1] ++ k.vs.map (fun v => v.d - 1) ++
    (match k.ends with
     | none => []
     | some e => [e.dY, e.n])

/-- How many scalars a call sends in all. -/
def runOf (k : Call) : Nat := (scalarsOf k).foldl (· + ·) 0

/-- How many mask entries the first block has: the lead's entries and H's coefficients. -/
def ownRun (k : Call) : Nat := k.lead + ownSlots k.all

/-- The end values' block, as a name and a count; empty if the call has no ends. -/
def endRuns (name : String) : Option Ends → List (String × Due)
  | none => []
  | some e => [(name, ⟨0, e.n⟩)]

/-- Coins of the extension field as elements of the word-level type `E`. -/
def coinsE {d : Due} (c : Cs d) : List E := List.ofFn fun i => E.ofTriple (ofE (c.e i))

/-- The end values' mask entries, from the block that the part is given for them. -/
def endCoins (name : String) : (o : Option Ends) → CsAll (endRuns name o) → List E
  | none, _ => []
  | some _, c => coinsE c.1

/-- Scalars as a message. -/
def sayE (l : List E) : Sending := ⟨l.map fun x => .e (toE x.triple), []⟩

/-- The first field element of each challenge; 0 for a challenge that has none. -/
def drawnE (ds : List Fmt.Drawn) : List E :=
  ds.map fun d => (d.elems.head?.map E.ofTriple).getD zeroE

/-- **The masked sumcheck's part.** `name`, `endName`: the names of the blocks that it spends. Its
counts are the shape's. Each move computes the call again, from the input and the `Front`. In `ask`,
`n` is the move's number in the part, so the last `n` challenges heard are the part's own; the
`Front`'s `seen` is `s.front n`: the move hands on what it was handed, its rounds cut, its columns
as they were handed, and lays no default. `f` is
given the call's variables (Y last), the `Front`, the first block, the end values' block, the part's
own challenges as field elements (eps first), and the input. -/
def sumPart (name endName : String) (J : SumJob W X) : Part V W X :=
  let k := J.shape
  let nv := k.vs.length
  let vw (all : List Var) (u : List E) : List (Var × List E) := all.zip (wOf all (u.drop k.lead))
  let ask (f : List Var → Front X → List E → List E → List E → W → List E) (n : Nat) :
      Move (Handed ⟨0, 0⟩ ((name, ⟨0, ownRun k⟩) :: endRuns endName k.ends) []) W X :=
    ⟨fun c s t =>
        let fr : Front X := ⟨t.heard.take (t.heard.length - n), t.own,
          s.front n⟩
        .ok (sayE (f (J.callAt t.input fr).all fr (coinsE c.2.1.1)
          (endCoins endName k.ends c.2.1.2) (drawnE (t.lately n)) t.input)),
      fun t => t.own⟩
  { takes := ⟨0, 0⟩, spends := (name, ⟨0, ownRun k⟩) :: endRuns endName k.ends, carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      [ask (fun all fr u _ _ w =>
        addL (padTo k.lead (J.lead w fr)) (u.take k.lead) ++ [tailSum (vw all u)]) 0] ++
      ((List.range nv).map fun i =>
        ask (fun all fr u _ ds w =>
          sentOfL (all.getD i (.plain 0)) (addL (hAt (vw all u) (ds.drop 1) zeroE)
            (scaleL (ds.headD zeroE) (J.round w fr (ds.drop 1))))) (i + 1)) ++
      ((k.ends.map fun e =>
         [ask (fun all fr u m ds w =>
            sentOfL (.point zeroE (e.dY + 1)) (addL (hAt (vw all u) (ds.drop 1) zeroE)
              (scaleL (ds.headD zeroE) (J.inY w fr (ds.drop 1) m)))) (nv + 1),
          ask (fun _ fr _ m ds w =>
            addL (padTo e.n (J.ends w fr ((ds.drop 1).take nv)))
              (scaleL (ds.getLastD zeroE) (padTo e.n m))) (nv + 2)]).getD []) }

/-! ## 4 A candidate simulator for it -/

/-- A list of elements split into rounds of the given lengths. -/
def roundsCut : List Nat → List E → List (List E)
  | [], _ => []
  | n :: ns, l => l.take n :: roundsCut ns (l.drop n)

/-- **A candidate simulator for `sumPart`.** It takes as many coins of its own as the call sends
scalars and outputs each coin as it is. It reads none of its other arguments. `sumSim` and `maskSim`
are definitions, and this file states nothing that relates them to `sumPart` and `maskPart`. -/
def sumSim (a : Addr) (k : Call) : Sim Pb :=
  { addr := a, takes := ⟨0, runOf k⟩
    tell := fun _ _ _ _ c =>
      some ((roundsCut (scalarsOf k) (coinsE c)).map fun l => ⟨l.map fun x => .e x.triple, []⟩) }

/-! ## 5 A part that sends a mask row -/

/-- **A mask row's sizes, code and sample answer**, as parameters; the last two are functions. -/
structure MaskJob where
  /-- the number of the row's entries -/
  ell : Nat
  /-- the length of its random tail -/
  tail : Nat
  logLength : Nat
  /-- the symbol at a position, from the entries and the tail -/
  code : List E → List E → Nat → E
  /-- the answer to the out-of-domain sample at a seed, from the entries and the tail -/
  answer : List E → List E → E → E

/-- **A part that sends a mask row**: one oracle message, then its sample's answer. It takes
`ell + tail` coins of the extension field, the entries first. A symbol is one element of that field,
which is three words. -/
def maskPart (M : MaskJob) : Part V W X :=
  { takes := ⟨0, M.ell + M.tail⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [
      ⟨fun c _ _ => .ok ⟨[], [⟨M.logLength, 3, fun p j =>
          let y := M.code ((coinsE c.1).take M.ell) ((coinsE c.1).drop M.ell) p
          toF (if j.val == 0 then y.c0 else if j.val == 1 then y.c1 else y.c2)⟩]⟩,
        fun t => t.own⟩,
      ⟨fun c _ t => .ok ⟨[.answer (toE (M.answer ((coinsE c.1).take M.ell)
          ((coinsE c.1).drop M.ell) ((drawnE (t.lately 1)).headD zeroE)).triple)], []⟩,
        fun t => t.own⟩] }

/-- **A candidate simulator for `maskPart`.** It takes `1 + tail` coins of its own. The first is
output as the sample's answer. Each distinct position that is read of the table gets one of the
others as the table's symbol there; a position that is listed twice gets the same coin. It outputs
`none` if more distinct positions are listed than `tail`. Of its other arguments it reads the
positions alone. `sumSim` and `maskSim` are definitions, and this file states nothing that relates
them to `sumPart` and `maskPart`. -/
def maskSim (a : Addr) (M : MaskJob) : Sim Pb :=
  { addr := a, takes := ⟨0, 1 + M.tail⟩
    tell := fun _ _ _ asks c =>
      let ps := ((asks.headD []).headD [])
      let u := coinsE c
      if M.tail < ps.eraseDups.length then none
      else some [
        ⟨[], [ps.map fun p =>
          let y := u.getD (1 + ps.eraseDups.idxOf p) zeroE
          (p, [y.c0, y.c1, y.c2])]⟩,
        ⟨[.answer (u.headD zeroE).triple], []⟩] }

end ProofFile.Honest

#print axioms ProofFile.Honest.addL
#print axioms ProofFile.Honest.scaleL
#print axioms ProofFile.Honest.padTo
#print axioms ProofFile.Honest.sumPow
#print axioms ProofFile.Honest.sumOf
#print axioms ProofFile.Honest.psiL
#print axioms ProofFile.Honest.wOf
#print axioms ProofFile.Honest.tailSum
#print axioms ProofFile.Honest.hAt
#print axioms ProofFile.Honest.sentOfL
#print axioms ProofFile.Honest.Front
#print axioms ProofFile.Honest.withPoints
#print axioms ProofFile.Honest.SumJob
#print axioms ProofFile.Honest.SumJob.callAt
#print axioms ProofFile.Honest.scalarsOf
#print axioms ProofFile.Honest.runOf
#print axioms ProofFile.Honest.ownRun
#print axioms ProofFile.Honest.endRuns
#print axioms ProofFile.Honest.coinsE
#print axioms ProofFile.Honest.endCoins
#print axioms ProofFile.Honest.sayE
#print axioms ProofFile.Honest.drawnE
#print axioms ProofFile.Honest.sumPart
#print axioms ProofFile.Honest.roundsCut
#print axioms ProofFile.Honest.sumSim
#print axioms ProofFile.Honest.MaskJob
#print axioms ProofFile.Honest.maskPart
#print axioms ProofFile.Honest.maskSim
