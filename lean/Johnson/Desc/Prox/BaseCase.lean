-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Prox/BaseCase.lean: the last step of a proximity test (the base case), as a block in
the form of Johnson/Desc/Block.lean.

What is tested. The test has come down to one claim on one short code word and its mask word: the
last message holds a word w under the main code C and a word u under the mask code Z, and the claim
says  ⟨c, message of w⟩ + ⟨d, message of u⟩ = τ.  With the last message the prover has sent a
masking message: a random word w* under C and u* under Z.
ROUNDS.
  1 "BASE lambda"  the prover sends τ*, what the claim's left side is at the masking words; the
                   verifier draws λ.
  2 "BASE"         the prover shows, in the clear, the messages M0, M1 and the random tails R0, R1
                   of w* + λ w and u* + λ u; the verifier draws t positions.
READS. At each drawn position the one tree that holds both messages: twelve words: a symbol of w, of
w*, of u, of u*, three words each.
FIXED BEFORE THE DRAW. That one tree: both λ and the positions are held against it. "before" names
every tree that the part opens: there is the one.
DECIDES. (i) the linear claim:  ⟨c, M0⟩ + ⟨d, M1⟩ = τ* + λ τ.  (ii) at each drawn position x: the
code word of (M0, R0) under C has at x the symbol  w*(x) + λ w(x),  and the code word of (M1, R1)
under Z at x's place in the shorter word the symbol  u*(x) + λ u(x).  Both are written out, with the
four lengths, in Johnson/Desc/Prox/BaseChecks.lean: linearOk, symbolsOk, baseChecks.
(Fmt/M1Fold.lean is imported; this file calls nothing of it.)
CLAIMS. None: the part ends the test.
THE TESTS ON THE PLAN ALONE (planOk): at least one position is drawn (else (ii) is empty); the mask
code is not longer than the main code; neither is longer than 2^32 (up to there Fmt.M1's point of a
position is the programs').

NOT HERE, AND WHOSE IT IS.
 - The rounds' entries against the plan's, the kinds and numbers of items and draws, the columns'
   key, position and width: Block.step's and FileDescription.planOk's.
 - That c, d, τ are the claim that the stages in front have come down to: the proximity test's.
 - THE CASE IN WHICH THE MASKING MESSAGE's ROOT IS SENT IN ROUND 1 IS NOT WRITTEN, AND THE PLAN's
   TESTS REFUSE IT: round 1's declared entry sends no root (roots = 0), so a plan whose entry
   "BASE lambda" sends one is not the blocks' rounds in a row; and "before" names the tree, so
   FileDescription.beforeOk asks that it is sent in front of this part's first draw. (No flag for this
   stands among the
   place's numbers: a Bool that the plan's maker sets could not fail.)
 - THE SIX TESTS THAT THE LIBRARY's HAND-WRITTEN VERIFIER PROGRAM ASKS AT THE OPENING, IN ITS RUN
   (Blk.readOpened and what it calls), AND THEIR HOMES ON THE PLAN (FileDescription.planOk's conjuncts;
   BookPlan's clauses by name):
   (1) the tree is in the book: treeSharingOk "told", with labelsOk;
   (2) what shares a leaf belongs to the same groups; beside a message without a sample to one group
       at most: treeSharingOk "alike", "oneGroup";
   (3) a tree that holds a message without a sample is opened once (so the masking message serves
       once): treeSharingOk "once";
   (4) no tree is longer than the range: treeSharingOk "range"; here both are C's log-length;
   (5) each message has a place in a tree: the sending block's "oracles" with their tenants: treeSharingOk
       "sum", "rows";
   (6) the messages asked for are all that their tree holds: NO COUNTERPART, by BookPlan's own word
       ("sum is what is left of it"): here the width 12 is held against what the sending block
       tells of the tree.
 - THAT THE TWELVE WORDS ARE THESE FOUR SYMBOLS IN THIS ORDER (two tenants, the last message first,
   each with one main row over the extension field and one mask row) IS TAKEN FOR GRANTED BY "four":
   nothing holds it against the tenants that the sending block tells (BookPlan's third limit).
No theorem here: the part's law is Johnson/Top/H0/P5Law/Law.lean. Nothing on soundness.

-/
import Johnson.Desc.Block
import Johnson.Desc.Prox.BaseChecks
import Fmt.M1Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Prox

/-- The numbers of the place. -/
structure BasePar where
  place : Place
  /-- the main code and the mask code: log-length, message length, tail length -/
  C : Fmt.M1.Code
  Z : Fmt.M1.Code
  /-- how many positions are drawn -/
  t : Nat
  /-- the tree that holds the last message and the masking message: the number in its label, and
  which of the chain's own trees it is -/
  label : Nat
  own : Nat
  /-- the bits of proof of work of the two rounds -/
  workLam : Nat
  workBase : Nat

/-- The part's record: the claim that is left. -/
structure BaseClaim where
  c : Array Fmt.M1.E
  d : Array Fmt.M1.E
  tau : Fmt.M1.E

def baseRounds (P : BasePar) : List Fmt.DeclaredRound :=
  [{ entry := { name := "BASE lambda", work := P.workLam, msg := 24, drawE := 1 } },
   { entry := { name := "BASE", work := P.workBase, msg := 24 * (P.C.l + P.Z.l + P.C.r + P.Z.r),
                poss := P.t, logN := P.C.a }
     opens := [({ a := P.C.a, W := 12, tree := P.label }, .own P.own)] }]

/-- The elements of a message. Nothing if an item is no element. -/
def elems : List Fmt.ItemValue → Option (List Fmt.M1.E)
  | [] => some []
  | .e x :: l => (elems l).map (x :: ·)
  | _ => none

/-- A column's four symbols: of the last message's main word, the masking main word, the last mask
word, the masking mask word. -/
def four : List UInt64 → Option (Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)
  | [a0, a1, a2, b0, b1, b2, c0, c1, c2, d0, d1, d2] =>
    some ((a0, a1, a2), (b0, b1, b2), (c0, c1, c2), (d0, d1, d2))
  | _ => none

def baseDecide (P : BasePar) (s : BaseClaim) :
    List Fmt.RoundView → List (List (Nat × List UInt64)) → Except String BaseClaim
  | [rL, rB], [g] =>
    match rL.vals, rL.drawn.elems, elems rB.vals with
    | [.e tauS], [lam], some sent =>
      if s.c.size == P.C.l && s.d.size == P.Z.l then
        if baseChecks P.C P.Z s.c s.d s.tau tauS lam (sent.take P.C.l)
            ((sent.drop P.C.l).take P.Z.l) ((sent.drop (P.C.l + P.Z.l)).take P.C.r)
            (sent.drop (P.C.l + P.Z.l + P.C.r)) rB.drawn.poss
            (fun x => (g.find? (·.1 == x)).bind fun y => four y.2)
        then .ok s else .error "the base case: the linear claim, or a symbol at a position"
      else .error "the base case: the claim's vectors have not the codes' message lengths"
    | _, _, _ => .error "the base case: the two messages' form"
  | _, _ => .error "the base case: two rounds and one group of columns"

/-- **The base case.** -/
def baseCase {Cl : Type} : Kind BasePar BaseClaim Cl := fun P =>
  { name := "the base case", place := P.place
    planOk := decide (0 < P.t) && decide (P.Z.a ≤ P.C.a) && decide (P.C.a ≤ 32)
    rounds := baseRounds P
    oracles := [[], []]
    before := [(P.place.chain, P.own)]
    decide := baseDecide P
    claims := []
    after := [] }

end VerifiableInference.Desc.Prox
