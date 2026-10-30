-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/RenumberEnd.lean: THE PREMISE ON THE LAST CLAIM AT THE
RENUMBERED PLACE IS THE PREMISE AT THE PLACE; SO THE LIBRARY's INVARIANT BEHIND THE FIRST SWITCH, AT
THE RENUMBERED PLACE, GIVES IT AT THE PLACE. Statements and proofs; no definition. All at a variable
place; none asks that the first fold sends its own mask.

What for. The law over the second part's own random values (`core_own_trees`, Sim/TreesLaw.lean in
the folder above) stands on the premise `EndOkT`: the last sampled element is 0, or the claim that
is left at the last stage is true. `endOk_of_body_trees` (same file) draws it from the library's
invariant `BehindFirstT`. At a place whose first fold sends its own mask that invariant cannot be
met, by its text (`PlanFrom` asks `ownMask = false`). At `renumP p` (Renumber.lean in this folder)
the plan's half holds at the library's three written places of such a test, by an evaluation in
Lean's kernel (`planOB_O_full` and its like, with `planAll_of_OB`: PlanOwn.lean in this folder).

  `stagesEnd_renum`, `restEnd_renum`, `endOwnT_renum`   the last stage's letters: the same at both
  `endTrue_renum`, `endOk_renum`   "the last claim is true"; the premise
  `endOk_of_behind_renum`   THE BRIDGE: `BehindFirstT (renumP p) …` gives `EndOkT p …`
  `behindFirstT_renum`   the invariant at `renumP p` with the state behind the first stage written
                 at p

By what. `EndOkT` reads the place through `aRec1`, `aAns`, `aRec3`
(Johnson/Desc/K12/Honest/Stages.lean) and `claimAtEnd` (Sim/Text.lean) alone; these read it through
`guardedProximityTestParts.fold`, `switch`, `batBehind` and `stageAt`, which are the same at both places by `rfl`.
The base case's part is not read.

Limits.
- AT `renumP p` THE FIRST FOLD's OWN MASK TREE IS LEFT OUT OF THE LISTS (`lists_own`,
  Renumber.lean). SO NOTHING THAT IS DRAWN AT `renumP p` MAY BE QUOTED OF STAGE 0, OF "ALL THE
  TEST's TREES", OR OF ANY COUNT OR BUDGET OVER THEM. SIX OF THIS FILE's STATEMENTS ARE HELPERS:
  they conclude at the renumbered place, as equations between the two places. The bridge has it in
  its premise alone: it concludes at p, and of the last claim alone.
- THE BRIDGE's PREMISE IS NOT SHOWN TO HOLD ANYWHERE: that `BehindFirstT (renumP p) …` can be
  reached from the first stage of a test whose first fold sends its own mask is not treated here.
- `renumP p` is a term of comparison (Renumber.lean's second limit).
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.Renumber
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

theorem stagesEnd_renum (p : P12) (K : BCoins) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (trees : List Tree) (D : ℕ → Fmt.Drawn),
      stagesEnd (renumP p) K rest j cur l o t P trees D = stagesEnd p K rest j cur l o t P trees D
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: rest, _, _, _, _, _, _, _, _ => stagesEnd_renum p K rest _ _ _ _ _ _ _ _

theorem restEnd_renum (p : P12) (K : BCoins) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t₁ : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn) :
    restEnd (renumP p) K cur next rest l o t₁ P trees D =
      restEnd p K cur next rest l o t₁ P trees D :=
  stagesEnd_renum p K rest _ _ _ _ _ _ _ _

theorem endOwnT_renum (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (hide : ℕ → GE) (trees : List Tree) (D : ℕ → Fmt.Drawn) (c : ℕ → GE) :
    endOwnT (renumP p) s next rest l tB P₀ hide trees D c =
      endOwnT p s next rest l tB P₀ hide trees D c :=
  restEnd_renum p _ s next rest l 1 _ P₀ trees D

theorem endTrue_renum (p : P12) (e : EndAt) : EndTrue (renumP p) e = EndTrue p e := rfl

theorem endOk_renum (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (hide : ℕ → GE) (trees : List Tree) (D : ℕ → Fmt.Drawn) (c : ℕ → GE) :
    EndOkT (renumP p) s next rest l tB P₀ hide trees D c =
      EndOkT p s next rest l tB P₀ hide trees D c := by
  unfold EndOkT
  rw [endOwnT_renum, endTrue_renum]

/-- **THE BRIDGE: the library's invariant behind the first switch at the renumbered place gives the
premise on the last claim at p.** -/
theorem endOk_of_behind_renum (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (tB : T12) (P₀ : PS) (hide : ℕ → GE) (trees : List Tree) (D : ℕ → Fmt.Drawn)
    (hf : FitAll next rest) (c : ℕ → GE)
    (h : BehindFirstT (renumP p) s next rest l tB P₀ hide trees D c) :
    EndOkT p s next rest l tB P₀ hide trees D c :=
  (endOk_renum p s next rest l tB P₀ hide trees D c) ▸
    endOk_of_body_trees (renumP p) s next rest l tB P₀ hide trees D hf c h

/-- `BehindFirstT` at the renumbered place, with the state behind the first stage written at p: what
the way in has to reach. -/
theorem behindFirstT_renum (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (hide : ℕ → GE) (trees : List Tree) (D : ℕ → Fmt.Drawn) (c : ℕ → GE) :
    BehindFirstT (renumP p) s next rest l tB P₀ hide trees D c =
      BodyInv (renumP p) (coinsOf (s :: next :: rest) hide c) (PlanAll (renumP p)) D rest 1 next
        (l.drop (s.k + 3)) (1 + ((sgOf s).h + (sgOf s).g) + 3)
        (t3At p (coinsOf (s :: next :: rest) hide c) rest 0 s next l 1 tB P₀ trees D)
        (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D)
        (aCol rest.isEmpty next
          (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D)) := rfl

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.stagesEnd_renum
#print axioms ProofFile.Honest.K12.Own.restEnd_renum
#print axioms ProofFile.Honest.K12.Own.endOwnT_renum
#print axioms ProofFile.Honest.K12.Own.endTrue_renum
#print axioms ProofFile.Honest.K12.Own.endOk_renum
#print axioms ProofFile.Honest.K12.Own.endOk_of_behind_renum
#print axioms ProofFile.Honest.K12.Own.behindFirstT_renum
