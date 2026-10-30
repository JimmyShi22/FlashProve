-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainSeats.lean: CLOSED FACTS ON PUBLIC DATA AT THE COPY's FILE's WRITTEN
LETTERS, THE FULL SIZE: which round sends which own tree; the plan's lists of the trees that the
proximity test's rounds open; Dealt (Johnson/Desc/K12/OpenLaws.lean) at the first stage; and the
clause on the declared tree at stage 0. A definition, statements and proofs.

  frOwn         the five own trees: number, the round that sends it, depth, width
  fr_seatOf, fr_treeSh, fr_seatTree   own tree number n is the first tree of round r, with that
                shape: by seatOf (Johnson/Prover/Link/LinkFrame.lean), by the library's treeSh, and
                by place in dsFull
  fr_lists      listsOf (p12Of frP).nums, written: five lists of one tree: these five
  fr_depths, fr_hk   the stages' main codes' depths are the trees'; h ≤ k at each stage
  fr_dealt      Dealt at the first stage, at the laid rounds behind "BAT": off the library's
                open_top. (That the test's block's own test on the plan says yes is planOk_entry,
                Johnson/Desc/K1/Law/PortNumbersAtMembers.lean [not in this library]; here it is had,
                without that file's imports, of test_planOk, descV_planOk and planOk_full.)
  fr_width0     the one tree in which the link's message is laid is 645 words wide
  decl_full     the tree that the plan's first round "CS" declares has the number 0, the first
                stage's depth and the width of that one tree

fr_seatOf, fr_treeSh, fr_seatTree, fr_lists, fr_depths, fr_hk and fr_width0 are by the kernel's
evaluation of a test with code, each under "set_option maxRecDepth 100000 in", as the library's own
closed facts at these letters are (Johnson/Desc/K15/TypedV.lean): a limit of elaboration is raised;
the kernel checks the term.

Kin: fr_trees (Johnson/Prover/Link/ChainTrees.lean) lists, round by round, the trees' depths and
widths; here a tree is named by its own number and its whole shape is given.

Limits. Public numbers alone. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkFrame
import Johnson.Prover.Link.DeclPlan
import Johnson.Desc.K12.Law.ReadsK
import Johnson.Desc.K15.TypedV
import Johnson.Desc.K15.HsemOf
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.Link.LinkWrittenMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15
open OnBytes.Flat (dsFull)
open TypedOracleCompiler.Run.PQ (treeSh)
open H2K.JointK (laidOf)

/-- The copy's file's own trees at the full size: number, the round that sends it, depth, width. -/
def frOwn : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 1, 24, 645), (1, 15, 21, 120), (2, 23, 17, 72), (3, 30, 13, 72), (4, 37, 14, 12)]

set_option maxRecDepth 100000 in
/-- Own tree number n is the first tree of round r. -/
theorem fr_seatOf : ∀ q ∈ frOwn, seatOf dsFull q.1 = some (q.2.1, 0) := fun q hq =>
  of_decide_eq_true (List.all_eq_true.1
    (show (frOwn.all fun q => decide (seatOf dsFull q.1 = some (q.2.1, 0))) = true by
      decide +kernel) q hq)

set_option maxRecDepth 100000 in
/-- Its shape. -/
theorem fr_treeSh : ∀ q ∈ frOwn, treeSh dsFull q.1 = some ⟨q.2.2.1, q.2.2.2, false, q.1⟩ :=
  fun q hq => of_decide_eq_true (List.all_eq_true.1
    (show (frOwn.all fun q =>
      decide (treeSh dsFull q.1 = some ⟨q.2.2.1, q.2.2.2, false, q.1⟩)) = true by
      decide +kernel) q hq)

set_option maxRecDepth 100000 in
/-- The round's data and the tree, by place. -/
theorem fr_seatTree : ∀ q ∈ frOwn, ∃ d, dsFull[q.2.1]? = some d ∧
    d.trees[0]? = some ⟨q.2.2.1, q.2.2.2, false, q.1⟩ := fun q hq => by
  have h : (dsFull[q.2.1]?).bind (·.trees[0]?) = some ⟨q.2.2.1, q.2.2.2, false, q.1⟩ :=
    of_decide_eq_true (List.all_eq_true.1
      (show (frOwn.all fun q => decide ((dsFull[q.2.1]?).bind (·.trees[0]?) =
        some ⟨q.2.2.1, q.2.2.2, false, q.1⟩)) = true by decide +kernel) q hq)
  obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨d, hd, ht⟩

set_option maxRecDepth 100000 in
/-- **The plan's lists of trees, written.** -/
theorem fr_lists : listsOf (p12Of frP).nums =
    frOwn.map fun q => [((⟨q.2.2.1, q.2.2.2, false, q.1⟩ : Fmt.Shape), Fmt.TreeSource.own q.1)] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stages' main codes' depths are the trees'. -/
theorem fr_depths : (p12Of frP).nums.stages.map (·.C.a) = frOwn.map (·.2.2.1) := by decide +kernel

set_option maxRecDepth 100000 in
/-- h ≤ k at each stage. -/
theorem fr_hk : ∀ s ∈ (p12Of frP).nums.stages, s.h ≤ s.k := fun s hs =>
  of_decide_eq_true (List.all_eq_true.1
    (show ((p12Of frP).nums.stages.all fun s => decide (s.h ≤ s.k)) = true by decide +kernel) s hs)

/-- **Dealt at the first stage**, at the laid rounds behind "BAT". -/
theorem fr_dealt (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : (p12Of frP).nums.stages = first :: rest) :
    Dealt first rest (listsOf (p12Of frP).nums) ((laidOf (p12Of frP)).drop 1) := by
  obtain ⟨f, r, ds, hs, hr, -, hD⟩ := open_top (Cl := Unit) guardedProximityTestParts (p12Of frP)
    (test_planOk frP _ _ (descV_planOk frP _ _ planOk_full))
  rw [h] at hs
  obtain ⟨rfl, rfl⟩ := List.cons.inj hs
  have e : laidOf (p12Of frP) = ds.zip (p12Of frP).oracles := by
    unfold laidOf
    rw [hr]
    rfl
  rw [e]
  exact hD

set_option maxRecDepth 100000 in
/-- The one tree in which the link's message is laid is 645 words wide. -/
theorem fr_width0 : ((layTrees frP.codes (linkMessage frP.S 1)).bind (·.shapes[0]?)).map
    (fun t => t.mainWidth + t.maskWidth) = some 645 := by decide +kernel

/-- **The clause on the declared tree, at stage 0, at the full size.** -/
theorem decl_full (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : (p12Of frP).nums.stages = cur :: next :: rest) (T : Tree) (hn : T.number = 0)
    (_hl : T.shape.logN = cur.C.a)
    (hT : ∃ lay, layTrees frP.codes (linkMessage frP.S 1) = some lay ∧
      lay.shapes[0]? = some T.shape)
    (dS dC : Fmt.DeclaredRound)
    (hcut : ((((laidOf (p12Of frP)).drop 1).drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]) :
    ∃ o, dC.opens = [o] ∧ o.1.tree = T.number ∧ o.1.a = cur.C.a ∧
      o.1.W = T.shape.mainWidth + T.shape.maskWidth := by
  have hD := fr_dealt cur (next :: rest) h
  rw [fr_lists] at hD
  have ha : cur.C.a = 24 := by
    have := fr_depths
    rw [h] at this
    exact (List.cons.inj this).1
  have hw : T.shape.mainWidth + T.shape.maskWidth = 645 := by
    obtain ⟨lay, h1, h2⟩ := hT
    have := fr_width0
    rw [h1] at this
    simp only [Option.bind_some, h2, Option.map_some, Option.some.injEq] at this
    exact this
  refine ⟨_, (cs_opens cur next rest _ _ _ hD dS dC hcut).2, hn.symm, ha.symm, hw.symm⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.fr_seatOf
#print axioms Johnson.Prover.Link.fr_treeSh
#print axioms Johnson.Prover.Link.fr_seatTree
#print axioms Johnson.Prover.Link.fr_lists
#print axioms Johnson.Prover.Link.fr_depths
#print axioms Johnson.Prover.Link.fr_hk
#print axioms Johnson.Prover.Link.fr_dealt
#print axioms Johnson.Prover.Link.fr_width0
#print axioms Johnson.Prover.Link.decl_full
