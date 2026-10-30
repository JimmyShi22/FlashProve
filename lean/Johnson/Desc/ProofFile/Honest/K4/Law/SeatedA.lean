-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeatedA.lean: A DEFINITION OF A HYPOTHESIS, and one statement
by projection.

What is here. THE FOUR OF `K4Seated`'s NINE FIELDS (Law/Seated.lean) THAT THE STATEMENTS ON THE
MEMBER's ACCEPTING STEP SPEND, as a structure of its own, so that these statements ask no more than
they spend. K4 is the sub-protocol of the feed-forward layers' own rounds; `K4Seated` says what it
means that K4's honest side stands at a member of a chain's thread. General in the thread T.

  `K4SeatedA`   member · rounds · own · half, each in K4Seated's own text.
  `K4Seated.toA`   whoever has K4Seated has it: so Lean holds that the four are K4Seated's own.

Not shown here. A HYPOTHESIS's FORM: nothing here shows it of any thread, and this file gives no
example. Of the five fields that are left out (place, oracles, seg, front, fits) nothing is said.
Who takes it as a hypothesis, among the files of this folder: Law/Accepted.lean,
Law/TapeAccepts.lean, Law/HearsSeated.lean, Law/ReadyHead.lean; who gives it at a thread, from
further hypotheses: `k4SeatedA_head` (Law/ElevenHead.lean): these five files are no part of the
library yet. Following import lines, and stopping unopened at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its
imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies behind the two is
not counted. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **What the statements on the accepting step spend of the seat.** A hypothesis's form. Nothing is
claimed by the definition. -/
structure K4SeatedA (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (p : OnBytes.Desc.First.K4.Par) (blk : Block S Cl) : Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- its rounds are the verifier's, at the parameters p -/
  rounds : blk.rounds = (OnBytes.Desc.First.K4.blockAtC p).rounds
  /-- the parameters are the public data's -/
  own : p.P = Q.P ∧ p.hp = Q.hp ∧ p.g = Q.g ∧ p.link = Q.link ∧ p.piece = Q.piece
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some (k4Half cells weights tokens look Q)

/-- Whoever has the seat whole has these four. -/
theorem K4Seated.toA {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub}
    {p : OnBytes.Desc.First.K4.Par} {blk : Block S Cl}
    (Se : K4Seated T b cells weights tokens look Q p blk) :
    K4SeatedA T b cells weights tokens look Q p blk :=
  ⟨Se.member, Se.rounds, Se.own, Se.half⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4SeatedA
#print axioms ProofFile.Honest.K4.K4Seated.toA

