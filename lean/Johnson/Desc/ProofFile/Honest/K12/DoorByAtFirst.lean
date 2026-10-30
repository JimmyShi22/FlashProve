-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorByAtFirst.lean

A conditional on a letter.

What it holds. A state function for a proximity test's job, doorBy: the description's own fold over
the blocks in front, at the rounds shown and at columns that a reader hands it, then the seat's way
in. And, at a called part of the first chain, at a run of the frame's walking prover (runC): where
the reader hands just the columns with which the first view begins, and the start is the chain's:
doorBy gives what the way in makes of the state that the description's own fold returns at the run's
own rounds and columns (door_by_at_first). General in the description, the book, the prover, the
side, the member and the blocks in front: no block in front is named.

Names.
  doorBy             the state function.
  doorBy_doorOf      at the type of claims Unit it is doorOf (JobShared.lean).
  door_by_at_first   the statement.

By what. called_at_first (CalledAtFirst.lean); the texts of doorBy and doorOf.

Limits.
- The reader is a letter, and no reader that meets the premise hcols is typed here. A part's front
  holds the rounds shown and, where the player hands them, the columns opened so far (Seen.opened,
  Honest/Frame.lean); the walk (runC) hands them. That a reader which takes them from there meets
  hcols is not shown here. At a test behind blocks which open the run's own trees the columns are
  not a function of the input and the rounds: by reading, no theorem.
- Nothing on whether the way in returns at the state: the conclusion keeps the fall-back. Never "the
  verifier's state" of doorBy without "the fold and the way in return" by name.
- It is called_at_first and an unfolding: its use is the form: one text for the letter "door".
  doorBy is a second text of doorOf, wider in the type of claims alone; the tie is doorBy_doorOf.
- The reader is handed the input: what it may read of it is not said here.
- A conditional: nothing on whether ready or runC returns or the part is called. Of the walk (runC),
  not of play (run).
- The stand is the state that midAtW (Honest/MidW.lean) returns. That runC's own walk goes through
  that state is not said here.
- It moves no count. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledAtFirst
import Johnson.Desc.ProofFile.Honest.K12.JobShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest

/-- **A state function that folds the description's own blocks in front over the rounds shown and
over columns that a reader hands it.** pre: the blocks in front. start: the chain's first state, of
the input. enter: the seat's way in. cols: the reader: a letter: which columns a part can be handed
is the frame's to say. fall: what is given where the fold or the way in refuses. With code. It is
doorOf (JobShared.lean), of which doorUF and doorOmegaF are made, at any type of claims:
doorBy_doorOf. What the fold leaves over is dropped, as there. -/
def doorBy {S Cl W X : Type} (pre : List (Block S Cl)) (start : W → S)
    (enter : S → Except String T12) (cols : W → Front X → List OpenedColumn) (fall : T12) :
    W → Front X → T12 := fun w fr =>
  ((foldBlocks 0 pre (start w) fr.seen.rounds (cols w fr)).bind fun r => enter r.1).toOption.getD
    fall

/-- At the type of claims Unit it is doorOf (JobShared.lean). -/
theorem doorBy_doorOf {S W X : Type} (bs : List (Block S Unit)) (s₀ : W → S)
    (enter : S → Except String T12) (cols : W → Front X → List OpenedColumn) (fall : T12) :
    doorBy bs s₀ enter cols fall = doorOf bs s₀ enter cols fall := by
  funext w fr
  unfold doorBy doorOf
  cases foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) <;> rfl

/-- **The door at a called part of the first chain, on a letter**: general in the description, the
book, the prover, the side, the member and the blocks in front. Where ready and runC return and the
part is called: there are the stand m that midAtW returns, with the first chain's own input, the
state s and the columns cs, with which the first view's columns begin and which are the filling of
what the blocks in front read at what was drawn, such that the description's own fold over the
blocks in front, from the first chain's start, at the rounds that m has seen of them and at cs,
returns s; and at every way in, every fall-back, every front that has seen these rounds, every
reader that hands just cs there (hcols) and every start that is the chain's there (hstart): doorBy
gives what the way in makes of s; the fall-back where the way in refuses.
Public: hpl. On the filling and the book: hR, S. On the run: hrun, hc. On the two letters: hstart,
hcols.
A conditional on a letter: a part's front holds the rounds shown and, where they are handed, the
columns opened so far (Seen.opened); no reader that meets hcols at a test behind blocks which open
the run's own trees is typed here.
Nothing on whether the way in returns. Of the walk (runC), not of play (run). -/
theorem door_by_at_first {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₁ F.Cl)) (i : ℕ) (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) :
    ∃ (m : Mid (Local W₀ Rc Xi Tr) Y) (s : F.S₁) (cs more : List OpenedColumn) (tr : Tr),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre (F.start₁ (F.pub x)) (m.seen.take (pre.flatMap (·.rounds)).length) cs =
        .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (start : Local W₀ Rc Xi Tr → F.S₁) (enter : F.S₁ → Except String T12)
        (cols : Local W₀ Rc Xi Tr → Front Y → List OpenedColumn) (fall : T12) (fr : Front Y),
        start m.st.input = F.start₁ (F.pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        cols m.st.input fr = cs →
        doorBy pre start enter cols fall m.st.input fr = (enter s).toOption.getD fall := by
  obtain ⟨m, s, cs, more, -, tr, hm, htr, hin, -, hlen, hcols, hfold, hfill⟩ :=
    called_at_first hpl hR σ u pre t i S hrun hc
  refine ⟨m, s, cs, more, tr, hm, htr, hin, hlen, hcols, hfold, hfill, ?_⟩
  intro start enter cols fall fr h1 h2 h3
  unfold doorBy
  rw [h1, h2, h3, hfold]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.doorBy
#print axioms ProofFile.Honest.K12.Light.doorBy_doorOf
#print axioms ProofFile.Honest.K12.Light.door_by_at_first
