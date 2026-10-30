-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtParts.lean: CONDITIONAL: `ExactMember`
(Honest/Small/Field.lean: the text of `Good.exact`, Honest/Side.lean, without its hypothesis on the
opened columns; it gives that field's text at the member, at every `pre`) at the parts of the row of
the layers' own rounds (kind K4; `k4Sorts`, Honest/K4/Part.lean) but the last two, each at a member
written out: a number, rounds, the part under the row's way of seating, the simulator. Statements
and proofs: each proof is one call; at the six masked sumchecks: of its own premise.

A part is named by two numbers, a · b: its number in the row, from 0, in the first group of layers ·
in a later group; "–" where a later group has no such part.
  the examples       the row's terms, written out: Lean compares each with the frame's.
  `k4_exact_quiet`   the parts 0 · 0, 1 · –, 2 · –, 4 · 2, 6 · 4, 10 · 8, 13 · 11, 14 · 12, 16 · 14.
      (Part 15 of a later group, the row's last but one, is a quiet round too: see Limits.)
  `k4_exact_3_1`, `k4_exact_7_5`   the two rounds that send scalars by themselves.
  `k4_exact_5_3`, `k4_exact_8_6`, `k4_exact_9_7`, `k4_exact_11_9`, `k4_exact_12_10`,
  `k4_exact_15_13`   the six masked sumchecks.

Limits. Each statement is an equation of two laws over uniform coins, at one member by itself, all
else fixed in front of the coins: what the part shows over the runs that it spends, and what its
simulator yields over its own coins. THE SIX AT A MASKED SUMCHECK ARE INSTANCES UNDER A FORM: each
is one call of its own premise `MSForm marked` (Law/ExactFresh/Forms.lean), at a test `marked` that
is a variable here: BY THEMSELVES THEY COUNT AS NO LAW SHOWN, whatever Lean answers on their axioms.
THE FORM IS SHOWN AT ONE TEST ALONE, `betaMarked`, in Law/ExactFresh/Paid.lean, by one call of the
law on the frame's masked sumcheck's part (Honest/SumLaw/SumExact.lean). The three others are one
call each of a law on the frame's two small parts (Honest/Small/). Every statement is conditional on
the sentence `StatedBy` on the rounds at which the member is seated, and at a masked sumcheck on
`marked` there: THAT THE ROUNDS OF ANY DESCRIPTION's MEMBER MEET THEM IS NOT SHOWN. TWO BEAR A
PREMISE ON THE PLAN's PUBLIC NUMBERS, BY NAME: `k4RowEnds Q` at part 8 · 6, `k4TermEnds Q` at part 9
· 7: whoever lays the plan shows them; no file here evaluates them at a model's plan. THE NUMBER j
AND THE ROUNDS rs ARE VARIABLES: nothing here ties a statement to its part's number in the row: that
is Law/ExactFresh/Join.lean's. Each statement is at K4's own job or values, and is drawn from a
sentence that is general in the job or the values: so it says nothing on whether the job is the
protocol's. In all nine the type Pb is free: a statement says something only where a face exists. Of
the row's last two parts, 17 · 15 and 18 · 16, none is stated by name here:
Law/ExactFresh/Whole.lean has them. IN A LATER GROUP PART 15 IS A QUIET ROUND: `k4_exact_quiet`,
which is at every number j, is at its member too.
What a caller still owes beside these equations, and none of it is shown here: that a member of a
side is one of those written out here, and `Side.fits` (stated in Law/ExactFresh/Join.lean); `fresh`
at the owners of the runs that are spent (the senders of the segment's mask row); that the book
lends these runs; that no coin stands in two runs; the condition on a job that reads what has been
seen (the head of Honest/Sum.lean); `exact` at the parts that carry these coins later.

No statement takes `k4Fits` (Honest/K4/Part.lean) as a premise: they are stated also where that test
is false. Beyond the six premises of `ExactMember` nothing is asked of the input, of the challenges
heard, of what has been seen, of a challenge, of the verifier's answer, or of the book. NOR OF THE
OPENED COLUMNS: `ExactMember` binds the state m by "∀", so each statement is at every value of
`m.opened` at which On holds. The one job that reads what has been seen (part 11 · 9) reads the
rounds shown (`fr.seen.rounds`) and not the opened columns.

Kin. Each statement is an instance of what it calls: `quietPart_exact_lift`
(Honest/Small/Quiet.lean), `scalarsPart_exact_lift` (Honest/Small/Scalars.lean), both of other
writers, or its own premise `MSForm marked`. The six at a masked sumcheck stand again without that
premise, and without `k4RowEnds` and `k4TermEnds`, at `betaMarked`, as `k4_closed_5_3` to
`k4_closed_15_13` (Law/ExactFresh/Closed.lean). Other kinds' files state `ExactMember` at every
member of a row of theirs, among others: `head_exact` (Honest/K6/Law/GoodRow.lean: under a premise
on the masked sumcheck's law, as here), `exact_quiet` and `exact_split` (Honest/K14/GoodCalls.lean),
`exact_side` (Honest/K12/Sim/ExactSide.lean): of other writers; none of these three files lies
beneath this one. Sought: by statement, to the letter and up to the bound letters, and by short
name, among the theorems of the library as it lay with the writer, and by short name among the
definitions under Honest/: no hit. The search by statement does not see a statement that has a
binder in front of the colon where ours has it behind, or the other way round. The kin told here
were found by the name `ExactMember`.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Forms
import Johnson.Desc.ProofFile.Honest.K4.Law.ShapesOk
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.Small.Scalars

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.Small (ExactMember quietPart_exact_lift scalarsPart_exact_lift stated_quiet_one_of
  stated_scalars_of)
open ProofFile.Honest.SumLaw (StatedBy)

/-! ## The row's terms, written out -/

example (Q : K4Pub) (i : Nat) : k4Addr Q i = ⟨⟨1, some Q.link, Q.piece, .K4⟩, i⟩ := rfl

example : k4Quiet = (quietPart 1 : Part Unit K4In Unit) := rfl

example (Q : K4Pub) (n : Nat) (f : K4Pub → K4In → Pts → List OnBytes.E) (i : Nat) :
    k4Scalars Q n f i =
      scalarsPart (runName maskRowRun (k4Addr Q i) "scalars") n
        fun w fr => f Q w (ptsOf Q w fr.heard) := rfl

example (Q : K4Pub) (k : Call) (owner : String) (job : K4Pub → K4In → Pts → Option Job)
    (i : Nat) :
    k4Sum Q k owner job i =
      sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName owner (k4Addr Q i) "ends")
        (k4SumJob k fun w fr => job Q w (ptsOf Q w fr.heard)) := rfl

example (Q : K4Pub) (k : Call) (job : K4Pub → K4In → Pts → Array OnBytes.E → Option Job)
    (i : Nat) :
    k4SumSeen Q k job i =
      sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName maskRowRun (k4Addr Q i) "ends")
        (k4SumJob k fun w fr =>
          job Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q))) := rfl

example (k : Call) (job : K4In → Front Unit → Option Job) : (k4SumJob k job).shape = k := rfl

-- What the job's five functions read: the caller's function at (w, fr), and their own arguments.
example (k : Call) (job : K4In → Front Unit → Option Job) :
    (k4SumJob k job).points = fun w fr => ((job w fr).map (·.cube.points)).getD [] := rfl

example (k : Call) (job : K4In → Front Unit → Option Job) :
    (k4SumJob k job).lead = fun w fr => ((job w fr).map (·.lead)).getD [] := rfl

example (k : Call) (job : K4In → Front Unit → Option Job) :
    (k4SumJob k job).round = fun w fr rs => ((job w fr).map (·.cube.round rs)).getD [] := rfl

example (k : Call) (job : K4In → Front Unit → Option Job) :
    (k4SumJob k job).inY = fun w fr rs m =>
      ((job w fr).map fun j => polyInY j.dY (j.atEnds rs) (j.ends rs) m).getD [] := rfl

example (k : Call) (job : K4In → Front Unit → Option Job) :
    (k4SumJob k job).ends = fun w fr rs => ((job w fr).map (·.ends rs)).getD [] := rfl

example (mu : Nat) :
    k4LevelShape mu = ⟨0, List.replicate mu (.point OnBytes.zeroE 3), some ⟨2, 2⟩⟩ := rfl

example (lt dY n : Nat) :
    k4TokenShape lt dY n = ⟨1, List.replicate lt (.point OnBytes.zeroE 3), some ⟨dY, n⟩⟩ := rfl

example (lam dY n : Nat) :
    k4PlainShape lam dY n = ⟨0, List.replicate lam (.plain 3), some ⟨dY, n⟩⟩ := rfl

/-! ## The parts -/

variable {S Cl W₀ Rc Xi Tr X Pb : Type}
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
  (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
  {marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool}

/-- **A part of one round in which nothing is sent**: nine parts of the row in the first group of
layers; eight in a later group: the seven of the head's list and part 15, the row's last but one.
CONDITIONAL on `StatedBy` at the member's round. At every number j and all rounds rs. -/
theorem k4_exact_quiet (h0 : StatedBy [0] rs) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look k4Quiet, quietSim (k4Addr Q j)⟩ :=
  quietPart_exact_lift φ σ chain firstTree On bud j 1 rs (k4Addr Q j) _ _ _ _
    (stated_quiet_one_of h0)

/-- **Part 3 · 1: the sums of limb products.** CONDITIONAL on `StatedBy` at the member's round. At
every number j and all rounds rs. -/
theorem k4_exact_3_1 (h0 : StatedBy [ledNS Q.P.y.h.xl * Q.P.y.NI] rs) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Scalars Q (ledNS Q.P.y.h.xl * Q.P.y.NI) wSums j),
        scalarsSim (k4Addr Q j) (ledNS Q.P.y.h.xl * Q.P.y.NI)⟩ :=
  scalarsPart_exact_lift φ σ chain firstTree On bud j _ rs (k4Addr Q j) _ _ _ _ _ _
    (stated_scalars_of h0)

/-- **Part 7 · 5: the row products.** CONDITIONAL on `StatedBy` at the member's round. At every
number j and all rounds rs. -/
theorem k4_exact_7_5 (h0 : StatedBy [ledNP Q.P.y.h.xl * Q.P.y.NI] rs) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Scalars Q (ledNP Q.P.y.h.xl * Q.P.y.NI) rowProducts j),
        scalarsSim (k4Addr Q j) (ledNP Q.P.y.h.xl * Q.P.y.NI)⟩ :=
  scalarsPart_exact_lift φ σ chain firstTree On bud j _ rs (k4Addr Q j) _ _ _ _ _ _
    (stated_scalars_of h0)

/-- **Part 5 · 3: the sumcheck on the norms' squares.** CONDITIONAL on `MSForm marked`, on
`StatedBy` and on the test `marked` at the member's rounds. At every number j and all rounds rs. -/
theorem k4_exact_5_3 (hMS : MSForm marked)
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muV)) rs)
    (hY : marked (k4LevelShape Q.P.rd.muV) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muV)⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobSquares Q w (ptsOf Q w fr.heard)) j rs (k4Addr Q j)
    (shapeOk_level _) h0 hY

/-- **Part 8 · 6: the token sumcheck on the row products.** CONDITIONAL on `MSForm marked`, on
`k4RowEnds`, on `StatedBy` and on the test `marked` at the member's rounds. At every number j and
all rounds rs. -/
theorem k4_exact_8_6 (hMS : MSForm marked) (hn : k4RowEnds Q = true)
    (h0 : StatedBy (scalarsOf (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))) rs)
    (hY : marked (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))
          maskRowRun jobRows j),
        sumSim (k4Addr Q j) (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobRows Q w (ptsOf Q w fr.heard)) j rs (k4Addr Q j)
    (shapeOk_token _ (by decide) (of_decide_eq_true hn)) h0 hY

/-- **Part 9 · 7: the second token sumcheck.** CONDITIONAL on `MSForm marked`, on `k4TermEnds`, on
`StatedBy` and on the test `marked` at the member's rounds. At every number j and all rounds rs. -/
theorem k4_exact_9_7 (hMS : MSForm marked) (hn : k4TermEnds Q = true)
    (h0 : StatedBy (scalarsOf (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))) rs)
    (hY : marked (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms j),
        sumSim (k4Addr Q j) (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobTerms Q w (ptsOf Q w fr.heard)) j rs (k4Addr Q j)
    (shapeOk_token _ (Nat.le_refl 1) (of_decide_eq_true hn)) h0 hY

/-- **Part 11 · 9: the batched sumcheck, whose job reads what has been seen (the caller's condition
on such a job: see the head).** CONDITIONAL on `MSForm marked`, on `StatedBy` and on the test
`marked` at the member's rounds. At every number j and all rounds rs. -/
theorem k4_exact_11_9 (hMS : MSForm marked)
    (h0 : StatedBy (scalarsOf (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)))) rs)
    (hY : marked (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4SumSeen Q (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) jobStack j),
        sumSim (k4Addr Q j) (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)))⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => 
      jobStack Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q))) j rs (k4Addr Q j)
    (shapeOk_plain _ (by decide) (by omega)) h0 hY

/-- **Part 12 · 10: the first product layer of the gated products.** CONDITIONAL on `MSForm marked`,
on `StatedBy` and on the test `marked` at the member's rounds. At every number j and all rounds rs.
-/
theorem k4_exact_12_10 (hMS : MSForm marked)
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muH)) rs)
    (hY : marked (k4LevelShape Q.P.rd.muH) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muH)⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobGated Q w (ptsOf Q w fr.heard)) j rs (k4Addr Q j)
    (shapeOk_level _) h0 hY

/-- **Part 15 · 13: the second product layer of the gated products.** CONDITIONAL on `MSForm
marked`, on `StatedBy` and on the test `marked` at the member's rounds. At every number j and all
rounds rs. -/
theorem k4_exact_15_13 (hMS : MSForm marked)
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muH2)) rs)
    (hY : marked (k4LevelShape Q.P.rd.muH2) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muH2)⟩ :=
  hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)) j rs (k4Addr Q j)
    (shapeOk_level _) h0 hY

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_exact_quiet
#print axioms ProofFile.Honest.K4.k4_exact_3_1
#print axioms ProofFile.Honest.K4.k4_exact_7_5
#print axioms ProofFile.Honest.K4.k4_exact_5_3
#print axioms ProofFile.Honest.K4.k4_exact_8_6
#print axioms ProofFile.Honest.K4.k4_exact_9_7
#print axioms ProofFile.Honest.K4.k4_exact_11_9
#print axioms ProofFile.Honest.K4.k4_exact_12_10
#print axioms ProofFile.Honest.K4.k4_exact_15_13
