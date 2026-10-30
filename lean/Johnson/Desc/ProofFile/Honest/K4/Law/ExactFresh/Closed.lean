-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/Closed.lean: CONDITIONAL: the statements of
Law/ExactFresh/AtParts.lean at the six masked sumchecks, and the two of Law/ExactFresh/Join.lean on
`ExactMember`, WITHOUT the premise `MSForm marked`, at the test `betaMarked`, and WITHOUT the two
premises on the plan's public numbers. "Closed": with no law as a premise. Statements and proofs.

  `k4_closed_5_3`, `k4_closed_8_6`, `k4_closed_9_7`, `k4_closed_11_9`, `k4_closed_12_10`,
  `k4_closed_15_13`   the six masked sumchecks (a part's two numbers: see AtParts.lean's head).
  `shapeFair_level`, `shapeFair_token`, `shapeFair_plain`, `k4Kinds_fair`   `shapeFair` at the row's
      shapes, at every plan.
  `closed_of_kind`, `walk_member`   by the sort: the three calls; from the test part by part to a
      member's own.
  `k4_closed_at`    one member of K4's side but the last two, under the test on its own rounds.
  `k4_closed_row`   every member but the last two, under ONE test on the sub-protocol's rounds.

Limits. Nine of the fourteen statements end in `ExactMember`: the six at a part, `closed_of_kind`,
`k4_closed_at`, `k4_closed_row`; the five others are on shapes, lists and tests alone. Each of the
nine is an equation of two laws over uniform coins, at one member by itself, all else fixed in front
of the coins: what the part shows over the runs that it spends, and what its simulator yields over
its own coins. `ExactMember` (Honest/Small/Field.lean) is the text of `Good.exact`
(Honest/Side.lean) at one member, without its hypothesis on the opened columns; it gives that
field's text at the member, at every `pre` (`exactAt_of_exact`, in that file); it binds the state m
by "∀": so each of the nine is at every value of `m.opened` at which On holds. Of what stands in
front of its part, the one job of the six that reads what has been seen (part 11 · 9) reads the
rounds shown (`fr.seen.rounds`) and not the opened columns; the five others read the challenges
heard alone. `closed_of_kind` IS AT EVERY JOB, one that reads the opened columns (`fr.seen.opened`)
among them: in its equation the rounds shown and the columns are fixed in front of the coins. Each
of the six at a part is one call of `exact_sumPart_field_fair` (Honest/SumLaw/SumExact.lean);
`k4_closed_at` and `k4_closed_row` gather, over the row, THE LAWS AND NOT THESE SIX: by a member's
sort they go through `closed_of_kind`, which calls that law at every masked sumcheck: so the six at
a part are called by no file that its writers know of, and they and the two are the same instances
twice. That law's test on a shape, `shapeFair` (Honest/SumLaw/ShapeFair.lean), does not read the
number of end values, so `k4RowEnds` and `k4TermEnds` are not premises here. At a shape that passes
`shapeFair` and not the library's `shapeOk`, the library's hearing of a masked sumcheck's call
returns nothing (`hear`, Johnson/Desc/Part/MaskedSum4.lean, whose first line is that test): so the
statements cover shapes more: a premise less, nothing more. K4's own verifier text is another;
nothing is said of it here. EACH OF THE SIX IS THE STATEMENT OF THE SAME NUMBER IN AtParts.lean, AND
THE TWO ON THE ROW ARE `k4_exact_at` AND `k4_exact_row` OF Join.lean, AT marked := `betaMarked`,
WITH PREMISES FEWER: ONE LAW, NOT A SECOND. In the six at a part the type Pb is free: a statement
says something only where a face exists; in the three others Pb is Xi, where `Face.own` is one. Each
of the nine is conditional on `StatedBy`, and at a masked sumcheck on `betaMarked`, at the rounds at
which the member is seated (in the three others as tests with code: `K4Kind.statedB`, `k4StatedB`):
THAT THE ROUNDS OF ANY DESCRIPTION's MEMBER MEET THEM IS NOT SHOWN (what is shown, of the longer
test `k4StatedAllB` on all the row's parts, Law/ExactFresh/Whole.lean: Law/ExactFresh/AtSide.lean:
it accepts all rounds with the entries of the verifier's table and no oracle message; no statement
that its writers know of leads from that test to `k4StatedB betaMarked`, the premise of
`k4_closed_row`); Law/ExactFresh/JoinTest.lean (no part of the library yet) evaluates `k4StatedB
betaMarked` at a small synthetic plan alone. The statements say nothing on whether a job is the
protocol's. The row's last two parts are not touched: no term of `Good` is made. THAT `k4Kinds`
LACKS JUST THE ROW's LAST TWO PARTS IS SHOWN BY NO STATEMENT HERE: `k4_closed_row` is at the members
whose number is below `(k4Kinds Q).length`; `k4Sided_length` (Law/ExactFresh/Whole.lean) counts the
row as that list with two sorts more. This file imports Law/ExactFresh/Paid.lean for
Honest/SumLaw/SumExact.lean beneath it, which Join.lean does not bring: `k4_msForm` is not called
here.
What a caller still owes beside these equations, and none of it is shown here: `fresh` at the owners
of the runs that are spent (the senders of the segment's mask row); that the book lends these runs;
that no coin stands in two runs; the condition on a job that reads what has been seen: for the items
that it reads, the head of Honest/Sum.lean; for opened columns, which no job of K4's row reads, the
head of Honest/SumLaw/SumExact.lean lays it on the caller and says that no file of its folder states
it; `exact` at the parts that carry these coins later.

Kin. In this folder: the six at a part and the two on the row: see Limits. `k4Kinds_fair` goes
beside `k4Kinds_ok` (Law/ExactFresh/Join.lean: the same list, at `shapeOk`, under the two tests on
the plan's numbers): its proof goes the same way, case by case, and does not call it.
`closed_of_kind` and `walk_member` state by themselves what the proofs of `k4_exact_at` and
`k4_exact_row` (Join.lean) do in line, with the law where these call their premise.
Law/ExactFresh/Whole.lean, which lies above this file, has the like over all the row's parts:
`k4KindsAll_fair`, and `k4_closed_all`: `ExactMember` at every member, the last two among them,
under the longer test `k4StatedAllB`. Its proofs call `closed_of_kind`, `walk_member` and the three
on a shape, and none of `k4Kinds_fair`, `k4_closed_at`, `k4_closed_row`: so these three too are
called by no file but this one that its writers know of; at the members but the last two
`k4_closed_row` and `k4_closed_all` have one end, the first under the shorter test.
`shapeFair_level`, `shapeFair_token` and `shapeFair_plain` go beside `shapeOk_level`,
`shapeOk_token` and `shapeOk_plain` (Law/ShapesOk.lean), whose head tells the library's like laws on
`shapeOk`: the first is had from its fellow by `shapeFair_of_ok` (Honest/SumLaw/ShapeFair.lean, of
other writers); the two others are shown from the test's text, without their fellows' premise on the
number of end values. Other kinds' files state `ExactMember` at every member of a row, among others:
`head_exact_all` (Honest/K6/Law/GoodRowSum.lean: with no law as a premise, as here), `exact_side`
(Honest/K12/Sim/ExactSide.lean): of other writers; neither file lies beneath this one. Sought: by
statement, to the letter and up to the bound letters, and by short name, among the theorems of the
library as it lay with the writer, and by short name among the definitions under Honest/: no hit.
The search by statement does not see a statement that has a binder in front of the colon where ours
has it behind, or the other way round. The kin told here were found by the names `ExactMember` and
`shapeFair`; those in this folder by a reader.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Join
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.Small (ExactMember scalarsPart_exact_lift stated_scalars_of)
open ProofFile.Honest.SumLaw (StatedBy betaMarked shapeFair shapeFair_of_ok exact_sumPart_field_fair)

/-! ## `shapeFair` at the row's shapes -/

/-- A product level's shape passes `shapeFair`: from `shapeOk_level`. -/
theorem shapeFair_level (mu : Nat) : shapeFair (k4LevelShape mu) = true :=
  shapeFair_of_ok (shapeOk_level mu)

/-- A token sumcheck's shape passes `shapeFair` where its degree in the further variable is at least
1: at every number of end values, 0 among them. -/
theorem shapeFair_token (lt n : Nat) {dY : Nat} (h1 : 1 ≤ dY) :
    shapeFair (k4TokenShape lt dY n) = true := by
  simp [shapeFair, k4TokenShape, VerifiableInference.Desc.Part.MaskedSum.Var.d, h1]

/-- So does a plain sumcheck's. -/
theorem shapeFair_plain (lam n : Nat) {dY : Nat} (h1 : 1 ≤ dY) :
    shapeFair (k4PlainShape lam dY n) = true := by
  simp [shapeFair, k4PlainShape, VerifiableInference.Desc.Part.MaskedSum.Var.d, h1]

/-- **The shapes that `k4Kinds` lists pass `shapeFair`**, at every plan. -/
theorem k4Kinds_fair (Q : K4Pub) {i : Nat} {k : Call}
    (hx : (k4Kinds Q)[i]? = some (.ms k)) : shapeFair k = true := by
  unfold k4Kinds at hx
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by cases Option.some.inj hx
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 6, hx => by cases Option.some.inj hx
    | 7, hx => by cases Option.some.inj hx
    | 8, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (by decide)
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (Nat.le_refl 1)
    | 10, hx => by cases Option.some.inj hx
    | 11, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (by decide)
    | 12, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 13, hx => by cases Option.some.inj hx
    | 14, hx => by cases Option.some.inj hx
    | 15, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 16, hx => by cases Option.some.inj hx
    | n + 17, hx => by simp at hx
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by cases Option.some.inj hx
    | 6, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (by decide)
    | 7, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_token _ _ (Nat.le_refl 1)
    | 8, hx => by cases Option.some.inj hx
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_plain _ _ (by decide)
    | 10, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 11, hx => by cases Option.some.inj hx
    | 12, hx => by cases Option.some.inj hx
    | 13, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeFair_level _
    | 14, hx => by cases Option.some.inj hx
    | n + 15, hx => by simp at hx

/-! ## The six masked sumchecks -/

section
variable {S Cl W₀ Rc Xi Tr X Pb : Type}
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
  (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))

/-- **Part 5 · 3: the sumcheck on the norms' squares.** CONDITIONAL on `StatedBy` and on
`betaMarked` at the member's rounds, and on nothing else. At every number j and all rounds rs. -/
theorem k4_closed_5_3
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muV)) rs)
    (hY : betaMarked (k4LevelShape Q.P.rd.muV) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muV) maskRowRun jobSquares j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muV)⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobSquares Q w (ptsOf Q w fr.heard))
    (shapeFair_level _) rs h0 hY j (k4Addr Q j)

/-- **Part 8 · 6: the token sumcheck on the row products.** CONDITIONAL on `StatedBy` and on
`betaMarked` at the member's rounds, and on nothing else (none on the number of end values). At
every number j and all rounds rs. -/
theorem k4_closed_8_6
    (h0 : StatedBy (scalarsOf (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))) rs)
    (hY : betaMarked (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))
          maskRowRun jobRows j),
        sumSim (k4Addr Q j) (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI))⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobRows Q w (ptsOf Q w fr.heard))
    (shapeFair_token _ _ (by decide)) rs h0 hY j (k4Addr Q j)

/-- **Part 9 · 7: the second token sumcheck.** CONDITIONAL on `StatedBy` and on `betaMarked` at the
member's rounds, and on nothing else (none on the number of end values). At every number j and all
rounds rs. -/
theorem k4_closed_9_7
    (h0 : StatedBy (scalarsOf (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))) rs)
    (hY : betaMarked (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) maskRowRun jobTerms j),
        sumSim (k4Addr Q j) (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobTerms Q w (ptsOf Q w fr.heard))
    (shapeFair_token _ _ (Nat.le_refl 1)) rs h0 hY j (k4Addr Q j)

/-- **Part 11 · 9: the batched sumcheck, whose job reads what has been seen (the caller's condition
on such a job: see the head).** CONDITIONAL on `StatedBy` and on `betaMarked` at the member's
rounds, and on nothing else. At every number j and all rounds rs. -/
theorem k4_closed_11_9
    (h0 : StatedBy (scalarsOf (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)))) rs)
    (hY : betaMarked (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4SumSeen Q (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) jobStack j),
        sumSim (k4Addr Q j) (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)))⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => 
      jobStack Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q)))
    (shapeFair_plain _ _ (by decide)) rs h0 hY j (k4Addr Q j)

/-- **Part 12 · 10: the first product layer of the gated products.** CONDITIONAL on `StatedBy` and
on `betaMarked` at the member's rounds, and on nothing else. At every number j and all rounds rs. -/
theorem k4_closed_12_10
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muH)) rs)
    (hY : betaMarked (k4LevelShape Q.P.rd.muH) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muH) maskRowRun jobGated j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muH)⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobGated Q w (ptsOf Q w fr.heard))
    (shapeFair_level _) rs h0 hY j (k4Addr Q j)

/-- **Part 15 · 13: the second product layer of the gated products.** CONDITIONAL on `StatedBy` and
on `betaMarked` at the member's rounds, and on nothing else. At every number j and all rounds rs. -/
theorem k4_closed_15_13
    (h0 : StatedBy (scalarsOf (k4LevelShape Q.P.rd.muH2)) rs)
    (hY : betaMarked (k4LevelShape Q.P.rd.muH2) rs = true) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, k4Lift Q cells weights tokens look
        (k4Sum Q (k4LevelShape Q.P.rd.muH2) maskRowRun jobGated2 j),
        sumSim (k4Addr Q j) (k4LevelShape Q.P.rd.muH2)⟩ :=
  exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
    (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl)
    _ _ (k4SumJob _ fun w fr => jobGated2 Q w (ptsOf Q w fr.heard))
    (shapeFair_level _) rs h0 hY j (k4Addr Q j)

end

section
variable {S Cl W₀ Rc Xi Tr X : Type}
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **A part of a sort beside its simulator, at whatever number and rounds**: the three calls by the
sort: the quiet round's law, the law on a round of scalars, the masked sumcheck's under `shapeFair`.
At every job, every function f that yields the scalars, and any two names of runs; the member need
not be the side's. NO LAW MORE THAN THE THREE THAT IT CALLS. CONDITIONAL on the sort's test at these
rounds. `k4_closed_at` calls it (`k4_closed_row` through that one), and `k4_closed_all`
(Law/ExactFresh/Whole.lean). -/
theorem closed_of_kind {x : K4Kind} {t : Nat}
    {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (hof : x.Of Q cells weights tokens look t y) (hfair : ∀ k, x = .ms k → shapeFair k = true)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (h0 : x.statedB betaMarked rs = true) :
    ExactMember φ σ chain firstTree On bud ⟨t, rs, y.1, y.2⟩ := by
  unfold K4Kind.statedB at h0
  rw [Bool.and_eq_true] at h0
  cases x with
  | quiet =>
    obtain rfl : y = _ := hof
    exact k4_exact_quiet φ σ chain firstTree On bud Q cells weights tokens look t _
      (statedBy_of_B _ _ h0.1)
  | lone n =>
    obtain ⟨f, rfl⟩ : ∃ f, y = _ := hof
    exact scalarsPart_exact_lift φ σ chain firstTree On bud t _ _ (k4Addr Q t) _ _ _ _ _ _
      (stated_scalars_of (statedBy_of_B _ _ h0.1))
  | ms k =>
    obtain ⟨J, rfl, name, endName, rfl⟩ : ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y = _ := hof
    exact exact_sumPart_field_fair φ σ chain firstTree On bud (fun _ => ())
      (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl)
      (fun _ => rfl) name endName J (hfair _ rfl) _ (statedBy_of_B _ _ h0.1) h0.2 t (k4Addr Q t)

/-- **The test part by part gives each member's own test**, where each listed sort's part stands in
the row at its number. On lists and tests alone. -/
theorem walk_member (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool)
    (ks : List K4Kind)
    (row : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi))
    (hk : ∀ (i : Nat) (x : K4Kind), ks[i]? = some x →
      ∃ y, row[i]? = some y ∧ x.Of Q cells weights tokens look i y)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hw : statedWalk marked ks rs = true) {t : Nat}
    {x : K4Kind} {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (hx : ks[t]? = some x) (hy : row[t]? = some y) :
    x.statedB marked
      ((rs.drop ((row.map (·.1.moves.length)).take t).sum).take y.1.moves.length) = true := by
  have e := statedWalk_at marked ks rs t x hw hx
  obtain ⟨y', hy', hof⟩ := hk t x hx
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  have hp : (row.map (·.1.moves.length)).take t = (ks.map (·.sent.length)).take t := by
    refine take_eq_of_below t fun i hi => ?_
    have hi' : i < ks.length := Nat.lt_trans hi (List.getElem?_eq_some_iff.1 hx).1
    have hxi := List.getElem?_eq_getElem hi'
    obtain ⟨yi, hyi, hofi⟩ := hk i _ hxi
    rw [List.getElem?_map, List.getElem?_map, hyi, hxi]
    exact congrArg some (hofi.moves Q cells weights tokens look)
  rw [hp, hof.moves Q cells weights tokens look]
  exact e

/-- **One member of K4's side, but the last two**, under the test on its own rounds. CONDITIONAL:
see the head. -/
theorem k4_closed_at (hr : σ.row = k4Sided Q cells weights tokens look)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hu : u ∈ σ.members) {x : K4Kind}
    (hx : (k4Kinds Q)[u.number]? = some x) (h0 : x.statedB betaMarked u.rounds = true) :
    ExactMember φ σ chain firstTree On bud u := by
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  rw [hr] at hy
  have hx' : (k4Kinds Q)[t]? = some x := by
    rw [← Nat.zero_add t]
    exact hx
  obtain ⟨y', hy', hof⟩ := k4_kind_of (Rc := Rc) (X := X) Q cells weights tokens look hx'
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  simp only [Nat.zero_add]
  exact closed_of_kind φ σ chain firstTree On bud Q cells weights tokens look hof
    (fun k hk => k4Kinds_fair Q (hk ▸ hx')) _ h0

/-- **Every member of K4's side but the last two**, under one test on the rounds of the side's own
sub-protocol. CONDITIONAL: see the head. -/
theorem k4_closed_row (hr : σ.row = k4Sided Q cells weights tokens look)
    (h0 : k4StatedB betaMarked Q (σ.block.rounds.zip σ.block.oracles) = true) :
    ∀ u ∈ σ.members, u.number < (k4Kinds Q).length →
      ExactMember φ σ chain firstTree On bud u := by
  intro u hu hlt
  have hx := List.getElem?_eq_getElem hlt
  refine k4_closed_at φ σ chain firstTree On bud Q cells weights tokens look hr hu hx ?_
  generalize (k4Kinds Q)[u.number] = x at hx
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  have hx' : (k4Kinds Q)[t]? = some x := by
    rw [← Nat.zero_add t]
    exact hx
  exact walk_member Q cells weights tokens look betaMarked (k4Kinds Q) σ.row
    (fun i x hi => hr ▸ k4_kind_of (Rc := Rc) (X := X) Q cells weights tokens look hi) _ h0 hx' hy

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shapeFair_level
#print axioms ProofFile.Honest.K4.shapeFair_token
#print axioms ProofFile.Honest.K4.shapeFair_plain
#print axioms ProofFile.Honest.K4.k4Kinds_fair
#print axioms ProofFile.Honest.K4.k4_closed_5_3
#print axioms ProofFile.Honest.K4.k4_closed_8_6
#print axioms ProofFile.Honest.K4.k4_closed_9_7
#print axioms ProofFile.Honest.K4.k4_closed_11_9
#print axioms ProofFile.Honest.K4.k4_closed_12_10
#print axioms ProofFile.Honest.K4.k4_closed_15_13
#print axioms ProofFile.Honest.K4.closed_of_kind
#print axioms ProofFile.Honest.K4.walk_member
#print axioms ProofFile.Honest.K4.k4_closed_at
#print axioms ProofFile.Honest.K4.k4_closed_row
