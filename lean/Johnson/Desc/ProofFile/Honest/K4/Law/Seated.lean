-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Seated.lean: A DEFINITION OF A HYPOTHESIS. No statement.

What is here. WHAT IT MEANS THAT THE HONEST SIDE OF K4 (`k4Half`, Honest/K4/Part.lean) STANDS AT A
MEMBER OF A CHAIN's `Thread` (Honest/Thread/Thr.lean). K4 is the sub-protocol of the feed-forward
layers' own rounds. It is meant as a hypothesis of statements on what K4's row plays. In this
folder a "parameter" is a free variable or a field of a thread; T is a variable throughout. General
in T: in the verifier's state, the claims, the book and all of T's parameters.

  `K4Seated T b cells weights tokens look Q p blk`   ON PUBLIC PARAMETERS ALONE. NINE FIELDS:
      * member: blk is the member number b of T's flat list;
      * place: it stands at the place of the public data Q;
      * rounds, oracles: its rounds are those of the sub-protocol at the parameters p, at the
        first chain's state (`blockAtC`, Johnson/Desc/First/K4/AtC.lean); none has an oracle
        message;
      * own: p's public parameters, plan, group, link and piece are Q's;
      * seg: Q reads the cells under the link's number, which is twice the group's;
      * half: the half that T's list of halves holds for that place is `k4Half` at Q;
      * front: as many rounds stand in front of the member as Q counts;
      * fits: the public data fit the parts (`k4Fits`, a test with code) at every list of challenges
        that the rounds in front can sample and every valid input.

ONE p IS MEANT IN ALL FILES OF THIS FOLDER: the member's as the chain seats it, at which the lookup
states its own claims (p.k3Runs = true). No field here reads that flag: the member's place, rounds
and decision do not hang on it, its runs of claims do: `K4FrontAt` (Honest/K4/Law/Kept.lean) asks
it, with what the link's two runs do.

Why front and fits. Every value that the parts read of the challenges is read by its number,
counted from `K4Pub.r0`; and where `k4Fits` is false a part may send its mask entries over zeros,
and no move says so. With the thread's clauses on the challenges heard (`Thread.Fit`) and on the
input (`T.valid`) fits gives the test at a run's own challenges.

Kin. Other sub-protocols' forms of the same make, of other writers: `K5Seated`
(Honest/K5/Law/Seated.lean: seven of these nine fields in the like text; no seg, no front),
`K6Seated` (Honest/K6/Law/Seated.lean: five). None is called.

Not shown here. A HYPOTHESIS's FORM: nothing here shows that it holds at a description of the
protocol, and this file gives no example of it. Nothing is asked of the member's name or of its
decision. Who is meant to prove each field. member, place, rounds, oracles: whoever ties T's flat
list to the description: the member is the sub-protocol, wrapped, and wrapping leaves these fields.
own, seg, front: whoever makes Q of the public files (`k4PubOf`, Honest/K4/Part.lean, lays the
segment's number as twice the group's, and reads the number of rounds off a named step). half:
whoever lays T's list of halves: one half at a place. fits: whoever makes Q and `look`: FITS IS
UNIVERSAL OVER THE CHALLENGES: it can be given only where `k4Fits` holds at every list that the
rounds in front can sample; that the test reads of the challenges in front the sizes of what `look`
returns alone is not shown here. Who gives `K4Seated`, from further hypotheses: `k4Seated_of_laid`
(Law/SeatedAt.lean), `k4Seated_head` (Law/SeatedHead.lean): BOTH TAKE half, front AND fits AS THEY
STAND: neither pays fits. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies
behind these is not counted. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **The kind's half stands at the member number b.** A hypothesis's form. Nothing is claimed by
the definition. -/
structure K4Seated (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Q : K4Pub)
    (p : OnBytes.Desc.First.K4.Par) (blk : Block S Cl) : Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- it stands at the place of the public data -/
  place : blk.place = k4Place Q
  /-- its rounds are the verifier's, at the parameters p -/
  rounds : blk.rounds = (OnBytes.Desc.First.K4.blockAtC p).rounds
  /-- no round has an oracle message -/
  oracles : blk.oracles = blk.rounds.map fun _ => []
  /-- the parameters are the public data's -/
  own : p.P = Q.P ∧ p.hp = Q.hp ∧ p.g = Q.g ∧ p.link = Q.link ∧ p.piece = Q.piece
  /-- the segment under whose number the cells are read is the member's link, which is twice the
  group's number: a matrix that an earlier group has committed to is read under twice that group's
  number (`k4Owner`) -/
  seg : Q.seg = Q.link ∧ Q.link = 2 * Q.g
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some (k4Half cells weights tokens look Q)
  /-- as many rounds stand in front of the member as the public data count -/
  front : Q.r0 = T.front + roundsTo T.bs b
  /-- THE PUBLIC DATA FIT (`k4Fits`: a test with code), at every list of challenges that the rounds
  in front of the member can sample, and every valid input's tokens -/
  fits : ∀ front w, drawsFit (T.ahead ++ declsTo T.bs b) front = true → T.valid w →
    k4Fits Q (look Q front) (tokens w.x) = true

end ProofFile.Honest.K4
#print axioms ProofFile.Honest.K4.K4Seated
