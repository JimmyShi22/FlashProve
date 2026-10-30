-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/PscStep.lean: the verifier's part in one run of the blocks' zero-knowledge sumcheck
(Psc.verify, OnBytes/Iop/Psc.lean), AS A PLAIN FUNCTION ON DATA: the claim, the summand, the fresh
mask entries, and just the run's own stretch of the plan's entries and of the view's rounds.

This file holds definitions with code alone; no theorem is stated.

Typed after the program's own text (OnBytes/Iop/Psc.lean and, beneath it, OnBytes/Iop/Ground.lean),
every layer of a call unfolded to its last test.

WHAT IS THE PROGRAM's OWN, CALLED BY NAME: Psc.sizeOf and what is beneath it: pure already, and it
cannot refuse. What is handed on, with its tests on sizes, is own text: Johnson/Desc/K13/Own.lean's
runSum (for Psc.run; that the two agree at all arguments: Johnson/Desc/K13/OwnLaws.lean). WHAT IS
WRITTEN ANEW: the reading of the rounds (Psc.hear, hearMany, hearOne with Blk.recvEs, closeOne,
closeEmpty, close, item).

No context of the program and no state crosses the border: the routine reads rounds and writes
nothing. No round is open at the border: a stretch holds whole rounds.

Main names:
  sentE r: all items of a round, where each is an element of the extension field.
  closeP name nz e r: what Blk.close asks of a round and its entry, but for the items and for
    "settled": the name; the draws other than 0; the three counts of draws.
  oneL, oneP name n nz e r: a round in which n elements are sent and one is drawn: the clauses, as
    a list, so that a look can say which one refuses; and what was sent and drawn.
  valuesL, valuesP n e r: the round of the shown values.
  manyP: the rounds of the claim's variables.
  pscLen x: how many rounds a run of the sizes x takes.
  hearP x es rs: what is heard (Psc.Heard).
  pscP c S fresh es rs: the run: what is handed on (Psc.Out), or nothing.

"SETTLED". Blk.close refuses while the round closed BEFORE counts batched rows that no block has
compared. No round of this routine compares rows, so here every entry of the stretch is asked to
count none, THE LAST TOO (the program would meet that one at the next close, behind this routine).
The entry in front of the stretch is the caller's.

What is not claimed. That a test written anew is the program's. That a challenge for Y is not 0 (the
entry's count is compared; the value is the strict reader's). That a word of a sent or drawn element
is below the field's prime: sentE lays an item's words as they stand; that test belongs to the fold
that calls this reading, not to this file. The caller's duty on the order (the head of
OnBytes/Iop/Psc.lean). Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Psc
import Johnson.Desc.K13.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.End
open OnBytes

/-- All items of a round, where each is an element of the extension field. -/
def sentE (r : Fmt.RoundView) : Option (List E) :=
  r.vals.mapM fun
    | .e x => some (E.ofTriple x)
    | _ => none

/-- The entry bears the name and counts nz draws other than 0; the round draws as many elements,
positions and matrix entries as the entry says. -/
def closeP (name : String) (nz : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  e.name == name && e.drawNZ == nz && r.drawn.elems.length == e.drawE &&
    r.drawn.poss.length == e.poss && r.drawn.trits.length == e.trits

/-- The clauses on the round of the shown values: the close; no batched rows; just n items; all of
them elements. -/
def valuesL (n : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) : List Bool :=
  [closeP "PSC values" 0 e r, e.rows == 0, r.vals.length == n, (sentE r).isSome]

/-- The round of the shown values. -/
def valuesP (n : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) : Option (List E) :=
  if (valuesL n e r).all id then sentE r else none

/-- The clauses on a round in which n elements are sent and one is drawn: the close; no batched
rows; just n items; all of them elements; just one element drawn. -/
def oneL (name : String) (n nz : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) : List Bool :=
  [closeP name nz e r, e.rows == 0, r.vals.length == n, (sentE r).isSome,
   r.drawn.elems.length == 1]

/-- A round in which n elements are sent and one is drawn: what was sent, what was drawn. -/
def oneP (name : String) (n nz : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) : Option (List E × E) :=
  if (oneL name n nz e r).all id then
    match sentE r, r.drawn.elems with
    | some q, [x] => some (q, E.ofTriple x)
    | _, _ => none
  else none

/-- The rounds of the variables whose polynomials have the listed numbers of sent coefficients: one
round with its entry for each, and none beside. -/
def manyP : List Nat → List (Fmt.Entry × Fmt.RoundView) → Option (List (List E × E))
  | [], [] => some []
  | n :: ns, (e, r) :: l => do
    let a ← oneP "PSC round" n 0 e r
    let t ← manyP ns l
    pure (a :: t)
  | _, _ => none

/-- How many rounds a run takes. -/
def pscLen (x : Psc.Size) : Nat := 1 + x.degree.length + if x.withY then 2 else 0

/-- What is heard in one run, from just its entries and rounds. -/
def hearP (x : Psc.Size) (es : List Fmt.Entry) (rs : List Fmt.RoundView) : Option Psc.Heard :=
  if es.length == pscLen x && rs.length == pscLen x then
    match es.zip rs with
    | [] => none
    | (e₀, r₀) :: l => do
      let first ← oneP "PSC epsilon" 1 0 e₀ r₀
      let mu ← first.1.head?
      let inX ← manyP (x.degree.map (· - 1)) (l.take x.degree.length)
      if x.withY then
        match l.drop x.degree.length with
        | [(eY, rY), (eV, rV)] => do
          let inY ← oneP "PSC Y" x.degreeY 1 eY rY
          let values ← valuesP x.values eV rV
          pure ⟨mu, first.2, inX ++ [inY], values⟩
        | _ => none
      else pure ⟨mu, first.2, inX, []⟩
  else none

/-- **One run**: the rounds are read; what is handed on is Own.lean's runSum. -/
def pscP (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) : Option Psc.Out :=
  (hearP (Psc.sizeOf c S) es rs).bind fun h => (K13.Own.runSum c S fresh h).toOption

end VerifiableInference.Desc.First.End
