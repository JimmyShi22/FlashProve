-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyCuts.lean: THE FOUR PUBLIC NUMBERS OF StageYes
(Johnson/Prover/Link/BodyYes.lean), FROM THE PLAN's CUTS: how many rounds and how many openings the
fold's and the switch's blocks have inside the proximity test's frame. Statements and proofs; no
record, no view, no value is read.

  nF_of   foldCut at the frame's cut for the fold · h ≤ k ⟹ the fold's block has 1 + (s.h + s.g)
          rounds
  oF_of   foldCut ⟹ it has no opening (by nOpen_foldCut, FormFoldPlan.lean)
  nS_of   the frame's cut for the switch is two declared rounds ⟹ the switch's block has 2 rounds
  oS_of   these two open no stored table; the first opens no tree, the second one ⟹ 1 opening

Not shown here. That a plan's cuts are such (foldCuts_of_nums has the folds'). Nothing on a
decision, on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyYes
import Johnson.Prover.Link.FormFoldPlan
import Johnson.Prover.Link.FoldCutLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

variable (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool) (l : Laid)

theorem nF_of (hF : foldCut cur.k ((l.take (1 + cur.k)).map (·.1)) = true) (hk : cur.h ≤ cur.k) :
    (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length =
      1 + ((sgOf cur).h + (sgOf cur).g) := by
  show ((l.take (1 + cur.k)).map (·.1)).length = 1 + (cur.h + (cur.k - cur.h))
  rw [length_of_foldCut hF, Nat.add_sub_cancel' hk]

theorem oF_of (hF : foldCut cur.k ((l.take (1 + cur.k)).map (·.1)) = true) :
    (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings = 0 :=
  nOpen_foldCut hF

theorem nS_of (dS dC : Fmt.DeclaredRound)
    (hS : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]) :
    (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).rounds.length = 2 := by
  show (((l.drop (1 + cur.k)).take 2).map (·.1)).length = 2
  rw [hS]
  rfl

theorem oS_of (dS dC : Fmt.DeclaredRound)
    (hS : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC])
    (s1 : dS.stored = []) (s2 : dC.stored = []) (o1 : dS.opens = []) (o2 : dC.opens.length = 1) :
    (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).openings = 1 := by
  show (((l.drop (1 + cur.k)).take 2).map (·.1)).foldl
    (fun n r => n + r.stored.length + r.opens.length) 0 = 1
  rw [hS]
  show 0 + dS.stored.length + dS.opens.length + dC.stored.length + dC.opens.length = 1
  rw [s1, s2, o1, o2]
  rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.nF_of
#print axioms Johnson.Prover.Link.oF_of
#print axioms Johnson.Prover.Link.nS_of
#print axioms Johnson.Prover.Link.oS_of
