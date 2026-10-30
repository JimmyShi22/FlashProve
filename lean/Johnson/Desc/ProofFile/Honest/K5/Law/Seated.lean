-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Seated.lean: what it means that the honest side of an attention
segment's own rounds (`k5Half`, Honest/K5/Row.lean) stands at a member of a chain's `Thread`
(Honest/Thread/Thr.lean). One definition of a proposition, which the laws of this folder take as a
premise, and the number of the border at the full size. No theorem.

  `K5Seated T b cells Z p blk`   blk is the member number b of T's flat list; it stands at the place
      of the public data Z; its rounds and its (empty) lists of oracle messages are those that the
      verifier's text lays for the numbers p (`rounds`, Johnson/Desc/First/Att/K5AttentionKind.lean); p's
      numbers of these rounds are Z's; the half that T's list of halves holds for that place is
      `k5Half cells Z`; and Z passes its first test (`Seat5.fits`, Honest/K5/Row.lean) at every list
      of challenges that the rounds in front can draw
  `borderOf g`   the number of the border in front of that member for the group g of layers, in a
      first chain of fourteen members a segment in which attention segments have the odd numbers

General in T: in the verifier's state, the claims, the book and all of T's letters.
Nothing is asked of the member's name or of its decision.

Why the last clause. In one arm of that test, where the verifier's own function for the named points
refuses at Z's key points, no move refuses: by their texts some of the row's values are then empty
lists and zeros, which the parts fill up, and the others are computed of the cells at empty points
and have no meaning (by reading: Honest/K5/Row.lean, at `Seat5.fits`; no theorem says it): the fault
would pass in silence. Of the test's other arms (the count of the rounds in front; the sizes) this
is not said. So the test rides as a named public premise into every law on this row, also where a
proof does not read it. With the clause on the challenges heard (`Thread.Fit`) it gives the test at
a run's own challenges.

Who is meant to show each clause. `member`, `place`, `rounds`, `oracles`: whoever ties T's flat list
to the description: the member is the kind's block, wrapped, and wrapping leaves these fields.
`own`: whoever makes Z of the public files. `half`: whoever lays T's list of halves: one half at a
place. `fits`: whoever makes Z: `seatAt` asks the test at challenges that are all 0; that the test
reads lengths alone, and that `base` counts the rounds in front, is not shown in this file.

Limits. A premise's form: nothing here shows that it is met at a description of the protocol.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.K5.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.Att (P.Par P.rounds)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **The kind's half stands at the member number b.** It is a definition: a premise's form.
Nothing is claimed of it. -/
structure K5Seated (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (Z : Seat5) (p : P.Par) (blk : Block S Cl) : Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- it stands at the place of the public data -/
  place : blk.place = Z.place
  /-- its rounds are the verifier's, at the numbers p -/
  rounds : blk.rounds = P.rounds p
  /-- no round has an oracle message -/
  oracles : blk.oracles = (P.rounds p).map fun _ => []
  /-- the numbers of these rounds are the public data's -/
  own : p.own = Z.P.x
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some (k5Half cells Z)
  /-- THE PUBLIC DATA FIT (`Seat5.fits`: a test with code), at every list of challenges
  that the rounds in front of the member can draw -/
  fits : ∀ front, drawsFit (T.ahead ++ declsTo T.bs b) front = true → Z.fits front = true

/-- The border in front of the attention segment's own rounds, for the group g of layers. A written
number: nothing here ties it to a flat list. -/
def borderOf (g : Nat) : Nat := 14 * (2 * g + 1) + 4

end ProofFile.Honest.K5
