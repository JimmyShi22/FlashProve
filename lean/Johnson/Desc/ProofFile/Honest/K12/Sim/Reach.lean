-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Reach.lean: a test with code (a definition of type `Bool`) on
the numbers of a proximity test's place (`P12`, Johnson/Desc/K12/Frame.lean), and a theorem on what
its "true" gives. The test, `reachB`, gathers the hypotheses on public numbers of the theorem
`law_of_coreB` (Sim/AllRest.lean), with two facts more: on the declared openings and on the first
fold's own table. It is for finding the places at which these hypotheses can be met:
Sim/ReachAt.lean evaluates it at the places that the library has as closed terms. The test takes the
place as its only argument, and `reach_gives` holds at every place. In the limits, "the law" is
`law_of_coreB`, and its premises are its hypotheses. Definitions and theorems. Public numbers alone:
no input, no coin, no challenge's value. No property is claimed.

In the list: a stage is a `Fmt.M1.Stage`: two codes C and Z, each with the numbers a (codewords of
length 2^a), l and r, and the numbers k, h, t. `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean) is the
stage in the library's form, with g := k - h. The place's stages are `p.nums.stages`. Its declared
rounds are those of `laidOf p` (Johnson/Desc/K12/Law/ReadsK.lean), numbered from 0, "BAT" being
round 0. The first reading round is round number `firstLen p.nums.stages + 1` (`firstLen`:
Johnson/Desc/ProofFile/Honest/K12/Parts.lean). A family of challenges is D : ℕ → `Fmt.Drawn`, by the
round's number, and `(D i).poss` is the list of positions that round i samples. A job is a `TestJob`
(Johnson/Desc/ProofFile/Honest/K12/Test.lean).

  `reach_gives`: where `reachB p` is true: the place has three stages or more, a first, then next,
    nx' and the list rest'; `p.nums.ownMask` is false; h ≤ k at every stage after a; `opensOf p` is
    the one depth `(sgOf a).C.a`; and `FitsBody D (next :: nx' :: rest') a 1` holds at every family
    of challenges D in which every round i samples `declared p i` positions. The clauses on the
    stages, on h ≤ k and on `FitsBody` are the hypotheses `hst`, `hlow` and `hF` of `law_of_coreB`
    at a job whose place is p
  `reachL p`: a definition: the clauses, each a name with a `Bool`. At a place with three stages or
    more, five: the place's numbers say that the first fold sends no table of its own (`ownMask` is
    false); h ≤ k at every stage after the first; the first reading round is declared to open one
    tree (`opensOf p` has length 1); of the first stage's depth (every entry of `opensOf p` is
    `(sgOf a).C.a`); the sizes at the declared counts (`sizesB (declared p)` along the stages, from
    round 1). At every other place one clause, "three stages or more", which is false
  `reachB p`, `reachNo p`: definitions: all clauses of `reachL p` hold; the names of those that do
    not
  `sizesB cnt rest cur o`: a definition: `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean) as a
    `Bool`, with the number `cnt i` in the place of the length of `(D i).poss`, and `csFitB`
    (Johnson/Desc/K12/Law/PubOk.lean) in the place of `CsFit`
  `fits_of_sizesB`: where every round i of D samples `cnt i` positions and `sizesB cnt rest cur o`
    is true, `FitsBody D rest cur o` holds
  `declared p i`: a definition: how many positions the place's declared round number i samples
    (`entry.poss`); 0 where `laidOf p` has no round number i
  `opensOf p`: a definition: the depths of the trees that the first reading round is declared to
    open (its field `opens`); the empty list where `laidOf p` has no such round
  `counts_of_drawsFit`: for a list l of declared rounds and a list ds of challenges of the declared
    form (`drawsFit l ds` is true; `drawsFit`: the frame, Johnson/Desc/ProofFile/Honest/Frame.lean):
    challenge number i of ds samples as many positions as round number i of l declares. After the
    lists' end both numbers are 0: there the challenge is `noDraw` (Sim/Sims.lean)

By what. `fits_of_sizesB` goes along the stages, unfolds `sizesB` and calls `csFit_of_B`
(Johnson/Desc/K12/Law/ChainOf.lean). `reach_gives` unfolds `reachB` and `reachL` and calls
`fits_of_sizesB`. `counts_of_drawsFit` goes along the two lists and unfolds `drawsFit` and `drawFit`
(the frame).

Limits.
- It counts nothing by itself: "true" says that the law's public premises can be met at the place;
  the law's other premises (the test with code `coreB` on input, carried coins and challenges; that
  the job's trees are the declared ones; the columns; the positions asked) are not touched.
- That a job's list of trees has the declared openings' length and depth is not shown here.
- "The place's numbers say that the first fold sends no table of its own" is the field `ownMask`; a
  job's own word on it is tied to that field by `TestJob.freshFits` (…/K12/Test.lean), which is not
  asked here. The job's own word is its field `fresh`: `freshFits` compares `J.fresh.isNone` with
  `J.p.nums.ownMask`.
- Sufficient for these premises: `reach_gives`. No converse is proved: a "false" names the clauses
  that fail; that the law's premises then cannot be met is by reading: "three stages or more",
  "h ≤ k" and the sizes are the law's own premises (the sizes at "at most" the counts); "one tree"
  is a count of declared openings, and the law speaks of the job's list of trees.
- `reach_gives` gives `FitsBody` at families that sample just the declared counts. That challenges
  of the declared form do so at the place is no theorem here: `counts_of_drawsFit` speaks of a list
  of declared rounds, and it is joined to `declared p` inside proofs of other files
  (Sim/ExactPlan.lean).
- The hypothesis of `counts_of_drawsFit`, `drawsFit`, reads the challenges' values; its conclusion
  speaks of the lengths of the lists of positions only.
- `laidOf p` pairs the declared rounds (`roundsOfNums`, Johnson/Desc/K12/TestEntries.lean) with
  `p.oracles` and ends with the shorter list. At a round that is cut off so, `declared p i` is 0,
  and the clause on the sizes compares 0: its comparisons of that count with the numbers r of the
  two codes then pass at every r, so its "true" says nothing of that round. No clause asks that the
  two lists have one length.
- That round number `firstLen p.nums.stages + 1` is the first declared round that opens a tree, the
  first round "CS", is by reading `roundsOfNums` and `Fmt.M1.laterRounds` (Fmt/M1Plan.lean): no
  theorem here says so.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.LinkSim.AtText.SpecShift
import Johnson.Desc.K12.Law.ChainOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody)

/-- How many positions the place's declared round number i samples, "BAT" being round 0; 0 where
`laidOf p` has no round number i. -/
def declared (p : P12) (i : ℕ) : ℕ := (((laidOf p)[i]?).map (·.1.entry.poss)).getD 0

/-- The depths of the trees that the first reading round, round number `firstLen p.nums.stages + 1`,
is declared to open; the empty list where `laidOf p` has no such round. -/
def opensOf (p : P12) : List ℕ :=
  (((laidOf p)[firstLen p.nums.stages + 1]?).map fun d => d.1.opens.map (·.1.a)).getD []

/-- `FitsBody` as a `Bool`, with the given counts `cnt i` in the place of the sampled lists' lengths
`(D i).poss.length`, and `csFitB` in the place of `CsFit`. -/
def sizesB (cnt : ℕ → ℕ) : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → Bool
  | [], cur, o =>
    decide (cnt (o + 1) ≤ (sgOf cur).C.r) && decide (cnt (o + 1) ≤ (sgOf cur).Z.r) &&
      decide ((sgOf cur).h = 0) && decide ((sgOf cur).g = 0)
  | next :: rest, cur, o =>
    decide (cnt (o + 2 + ((sgOf cur).h + (sgOf cur).g)) ≤ (sgOf cur).C.r) &&
      decide (cnt (o + 2 + ((sgOf cur).h + (sgOf cur).g)) ≤ (sgOf cur).Z.r) &&
      decide ((sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l) && H2K.Pub.csFitB cur next &&
      sizesB cnt rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)

theorem fits_of_sizesB (D : ℕ → Fmt.Drawn) (cnt : ℕ → ℕ) (hD : ∀ i, (D i).poss.length = cnt i) :
    ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ), sizesB cnt rest cur o = true →
      FitsBody D rest cur o
  | [], cur, o, h => by
    simp only [sizesB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨by rw [hD]; exact h1, by rw [hD]; exact h2, h3, h4⟩
  | next :: rest, cur, o, h => by
    simp only [sizesB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨by rw [hD]; exact h1, by rw [hD]; exact h2, h3, H2K.Pub.csFit_of_B h4,
      fits_of_sizesB D cnt hD rest next _ h5⟩

/-- The clauses, each under its name. At a place with fewer than three stages: the one clause "three
stages or more", which is false. -/
def reachL (p : P12) : List (String × Bool) :=
  match p.nums.stages with
  | a :: next :: nx' :: rest' =>
    [("the first fold sends no table of its own", !p.nums.ownMask),
     ("h ≤ k behind the first stage", (next :: nx' :: rest').all fun st => decide (st.h ≤ st.k)),
     ("the first reading round opens one tree", decide ((opensOf p).length = 1)),
     ("of the first stage's depth", (opensOf p).all fun d => decide (d = (sgOf a).C.a)),
     ("the sizes at the declared counts", sizesB (declared p) (next :: nx' :: rest') a 1)]
  | _ => [("three stages or more", false)]

/-- All clauses of `reachL p` hold. -/
def reachB (p : P12) : Bool := (reachL p).all (·.2)

/-- The names of the clauses of `reachL p` that do not hold. -/
def reachNo (p : P12) : List String := ((reachL p).filter (!·.2)).map (·.1)

/-- Challenges of the declared form sample as many positions as are declared, round by round; after
the lists' end both numbers are 0. -/
theorem counts_of_drawsFit : ∀ (l : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    drawsFit l ds = true → ∀ i, (ds.getD i noDraw).poss.length = ((l[i]?).map (·.entry.poss)).getD 0
  | [], [], _, i => by simp [noDraw]
  | [], _ :: _, h, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _ => by simp [drawsFit] at h
  | d :: l, R :: Rs, h, i => by
    simp only [drawsFit, drawFit, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hB⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hr⟩ := h
    cases i with
    | zero => simpa using hB
    | succ i => simpa using counts_of_drawsFit l Rs hr i

/-- **What the test's "true" gives**: three stages or more; `ownMask` is false; h ≤ k at every stage
after the first; the first reading round is declared to open one tree, of the first stage's depth;
and `FitsBody` at every family of challenges that samples the declared counts. -/
theorem reach_gives (p : P12) (h : reachB p = true) :
    ∃ a next nx' rest', p.nums.stages = a :: next :: nx' :: rest' ∧ p.nums.ownMask = false ∧
      (∀ st ∈ next :: nx' :: rest', st.h ≤ st.k) ∧ opensOf p = [(sgOf a).C.a] ∧
      ∀ D : ℕ → Fmt.Drawn, (∀ i, (D i).poss.length = declared p i) →
        FitsBody D (next :: nx' :: rest') a 1 := by
  unfold reachB reachL at h
  split at h
  · rename_i a next nx' rest' hst
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at h
    obtain ⟨c1, ⟨c2a, c2b, c2c⟩, c3, c4, c5⟩ := h
    refine ⟨a, next, nx', rest', hst, c1, ?_, ?_, fun D hD =>
      fits_of_sizesB D (declared p) hD _ _ _ c5⟩
    · intro st hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact c2a
      rcases List.mem_cons.1 hs with rfl | hs
      · exact c2b
      exact of_decide_eq_true (List.all_eq_true.1 c2c st hs)
    · obtain ⟨d, hd⟩ := List.length_eq_one_iff.1 c3
      rw [hd] at c4 ⊢
      simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq] at c4
      rw [c4]
  · simp at h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fits_of_sizesB
#print axioms ProofFile.Honest.K12.counts_of_drawsFit
#print axioms ProofFile.Honest.K12.reach_gives
#print axioms ProofFile.Honest.K12.declared
#print axioms ProofFile.Honest.K12.opensOf
#print axioms ProofFile.Honest.K12.sizesB
#print axioms ProofFile.Honest.K12.reachL
#print axioms ProofFile.Honest.K12.reachB
#print axioms ProofFile.Honest.K12.reachNo
