-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstAll.lean: THE KEY FILE's FIRST CHAIN: (B1) AND (B2) AT EVERY NUMBER OF ITS OWN FLAT
LIST, AT ONE VALUE OF THE LETTERS, WITH EVERY NAMED TEST ON VALUES WRITTEN OUT: no premise on a
sub-protocol is left. A join: calls. Sub-protocols of the verifier's: NOTHING IS SHOWN OF ANY
PROVER.

  **`Z₁A`**: E2E/KeyShapeFirstReturns.lean's `Z₁V` with E2E/KeyRangesReturns.lean's `vRng` laid in
    for the letter at the ranges' proximity test.
  **`returns_every₁`**: (B2) at every number: `returns_all₁` at `returns_rng`: CALLED.
  **`carries_every₁`**: (B1) at every number, at the same letters: `carries_whole₁`: CALLED.
  **`both_sourced`**: both, in the goals' scope, at the description that the verifier runs: the
    premises on public values by E2E/KeyShapeFullSourced.lean's `public_first_sourced`.
  **`all_sourced`**: there, AT ONE TERM (`Z₁A` at the written codes): the start state's shape is
    `T0`; the guards' run returns `T19`; the Bool that the frame's rule asks; nineteen members; (B1)
      and (B2) at every number.

Limits.
- TWO NAMED TESTS ON VALUES STAND: on the claims on the keys at "batt.1.batt" (it reads the state in
  front); `vRng` at the ranges' proximity test. That any prover's values pass them is shown nowhere
  here; no value is exhibited at which `vRng` accepts. (E2E/KeyShapeValues16.lean: the first accepts
  at every state at which a `Thread` stands there; E2E/KeyShapeValues15.lean: so do two of the
  second's three parts.) At the other seventeen numbers the named test is our own constant "asks
  nothing".
- **AT THE RANGES' PROXIMITY TEST (B2) MOVES THE WHOLE DEBT INTO THE VALUES.** `vRng` is three
  tests: two marks on the state in front, and one that runs the test's own parts and asks the base
  case's whole decision. Where the guard returns, rounds and columns fit and the two marks hold,
  that third test comes to the sub-protocol's own accept (argued; for the test's own block
  Johnson/Desc/K12/Honest/Shape/TestReturnsOneIff.lean has the like as a theorem; at the seat it is
  typed nowhere). What (B2) adds there: no other part can reject: the entering, the seat's six asks,
  the front, the batching, the folds, the switches, the leaving. Of the algebra nothing is spared.
- (B2) speaks at rounds and columns that fit: the declared items and counts, the ranges, that a
  drawn element which is declared never 0 is not 0, and the columns by key, position and width.
- `returns_every₁` and `carries_every₁` have premises on public values ("w.1.send" is there; two on
  the ranges' place); in scope they are paid. The run, the Bool and `T0` stand at the written codes
  alone.
- The first chain alone.


-/
import E2E.KeyRangesReturns
import E2E.KeyShapeFullSourced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest (Shape Carries Returns)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (FirstState Claim rangesParams Source LaterPlaces)
open AtPublicFiles.KeyShape (Pub1)

section
variable (Q : Pub1) (cs : Codes) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (N : H2U.PlaceNums)

/-- **The letters of the cut for the first chain, with every named test on values written out.** -/
def Z₁A : Shape FirstState := Z₁V Q cs D told N (vRng N)

/-- **(B2) at every number, with no premise on a sub-protocol**; one on public values. -/
theorem returns_every₁ (ft : Nat) (bw : Block FirstState Claim)
    (hw : sendWAt Q D told = some bw) (j : Nat) :
    Returns (flat₁ Q D told N) ft (Z₁A Q cs D told N) j :=
  returns_all₁ Q cs D told N (vRng N) ft bw hw (returns_rng Q cs N ft) j

/-- **(B1) AT EVERY NUMBER, AT THE SAME LETTERS.** -/
theorem carries_every₁ (ft : Nat) (bw : Block FirstState Claim)
    (hw : sendWAt Q D told = some bw) (he : (rangesParams N).early = true)
    (ha : (rangesParams N).answers = 1) (j : Nat) :
    Carries (flat₁ Q D told N) ft (Z₁A Q cs D told N) j :=
  carries_whole₁ Q cs D told N ft _ bw hw he ha j

end

/-- **BOTH, IN SCOPE, AT THE DESCRIPTION THAT THE VERIFIER RUNS.** -/
theorem both_sourced {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) (cs : Codes) (ft j : Nat) :
    Carries (keyFileDescription X N P).first.blocksInOrder ft (Z₁A (pubOf X) cs X.Y.D.1 X.Y.told.1 N) j ∧
      Returns (keyFileDescription X N P).first.blocksInOrder ft (Z₁A (pubOf X) cs X.Y.D.1 X.Y.told.1 N) j := by
  obtain ⟨bw, hw, he, ha, -⟩ := Full.public_first_sourced hs scope
  exact ⟨carries_every₁ (pubOf X) cs X.Y.D.1 X.Y.told.1 N ft bw hw he ha j,
    returns_every₁ (pubOf X) cs X.Y.D.1 X.Y.told.1 N ft bw hw j⟩

open Full in
/-- **ALL AT ONE TERM, IN SCOPE, AT THE DESCRIPTION THAT THE VERIFIER RUNS.** -/
theorem all_sourced {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) (ft : Nat) :
    (∀ x, (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).sh ((keyFileDescription X N P).start₁ x) = T0) ∧
      (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).run 19 T0 = .ok T19 ∧
      (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N).yes T0 19 = true ∧
      (keyFileDescription X N P).first.blocksInOrder.length = 19 ∧
      (∀ j, Carries (keyFileDescription X N P).first.blocksInOrder ft (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) j) ∧
      ∀ j, Returns (keyFileDescription X N P).first.blocksInOrder ft (Z₁A (pubOf X) CF X.Y.D.1 X.Y.told.1 N) j := by
  obtain ⟨-, -, -, hlen, hT0, hrun, hyes, -⟩ := first_of_sourced hs scope
    (vOf ((gvAll₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N (vRng N)).map (·.2)))
  exact ⟨fun x => (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hT0, hrun, hyes,
    hlen, fun j => (both_sourced hs scope CF ft j).1, fun j => (both_sourced hs scope CF ft j).2⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.returns_every₁
#print axioms AtPublicFiles.AtFiles.carries_every₁
#print axioms AtPublicFiles.AtFiles.both_sourced
#print axioms AtPublicFiles.AtFiles.all_sourced
