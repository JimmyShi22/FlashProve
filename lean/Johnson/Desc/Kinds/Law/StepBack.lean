--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/StepBack.lean: THE MEMBER's WAY AT A BLOCK's STEP: FROM A YES OF decide TO A YES OF Block.step, AND FROM "NO DRAWN ELEMENT IS BAD" FOR A RULE ON THE ROUNDS WITHOUT THEIR SEALED DIGESTS TO THE SAME FOR THE RULE THAT STRIKES THE DIGESTS ITSELF: THE CONVERSES OF Law/RowPins.lean's step_decide AND noBad_noDigest, which go the law's way: STATED AND PROVED, GENERAL IN THE BLOCK; AND AT K6: what carries a member
of Law/RowRides.lean's rowRides to the antecedent of Law/RowPins.lean's rowStep.
  wantOf firstTree b rs   key, position and width of every column that the step takes at these rounds: Block.step's own letter "want".
  decide_step    the rounds fit (Block.lean: roundsFit) · the next columns are those that are read · decide says yes on the rounds without their digests and the columns laid in groups ⇒ b.step … = .ok (s', the number of columns read). (By unfolding: the step IS these three tests.)
  noBad_digest   NoBad b (rs.map noDigest) ⇒ NoBad (fun g => b (g.map noDigest)) rs.     noBad_ruleStep   the same at K6's two rules: NoBad (ruleK6T …) on the struck rounds ⇒ NoBad (ruleStep W s d) rs.
  canonical_digest   Canonical (rs.map noDigest) ⇒ Canonical rs.
WHAT IT DOES NOT SAY. That an honest prover's rounds fit, or that its columns are those read: premises. That K6's block is owed no column (so that the second test is idle there): not shown here. THE OTHER THINGS THAT rowStep's ANTECEDENT ASKS BEYOND rowRides's NINE: K6On's two further clauses (public; Law/K6OnB.lean) · "the lookup was heard" · **JoinOpened at the truth: SHOWN NOWHERE**. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Sound (cutTo)
open VerifiableInference.Desc.First (S)

/-- Key, position and width of every column that the step takes at these rounds. -/
def wantOf {S' Cl : Type} (firstTree : Nat) (b : Block S' Cl) (rs : List Fmt.RoundView) :
    List (Nat × Nat × Nat) :=
  (groupsOf firstTree b.rounds (rs.map (·.drawn))).flatMap id

namespace Came

/-- **From a yes of decide to a yes of the step.** -/
theorem decide_step {S' Cl : Type} (firstTree : Nat) (b : Block S' Cl) (s : S') (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S') (hfit : roundsFit b.rounds rs = true)
    (hcols : ((cols.take (wantOf firstTree b rs).length).map fun c => (c.1, c.2.1, c.2.2.length))
      = wantOf firstTree b rs)
    (hd : b.decide s (rs.map noDigest)
      (regroup ((groupsOf firstTree b.rounds (rs.map (·.drawn))).map (·.length))
        (cols.take (wantOf firstTree b rs).length)) = .ok s') :
    b.step firstTree s rs cols = .ok (s', (wantOf firstTree b rs).length) := by
  unfold wantOf at hcols hd ⊢
  unfold Block.step
  simp only [need, hfit, hcols, beq_self_eq_true, if_true, bind, Except.bind, pure, Except.pure, hd]

/-- **The rule that strikes the digests itself, from the rule on the struck rounds.** -/
theorem noBad_digest {b : List Fmt.RoundView → List E} {rs : List Fmt.RoundView}
    (h : Sound.NoBad b (rs.map noDigest)) : Sound.NoBad (fun g => b (g.map noDigest)) rs := by
  intro i r hi j x hj hm
  have hi' : (rs.map noDigest)[i]? = some (noDigest r) := by
    rw [List.getElem?_map, hi]
    rfl
  refine h i (noDigest r) hi' j x hj ?_
  have e : ([] ++ rs.take i ++ [cutTo r j]).map noDigest
      = [] ++ (rs.map noDigest).take i ++ [cutTo (noDigest r) j] := by
    rw [List.nil_append, List.nil_append, List.map_append, List.map_take]
    rfl
  rw [← e]
  exact hm

/-- Rounds whose struck forms are written canonically are written canonically. -/
theorem canonical_digest {rs : List Fmt.RoundView} (h : Canonical (rs.map noDigest)) : Canonical rs :=
  fun r hr => h (noDigest r) (List.mem_map_of_mem hr)

/-- The same at K6's two rules. -/
theorem noBad_ruleStep (W : OnBytes.Model.Verify.Public) (s : S) (d : Pinned) (rs : List Fmt.RoundView)
    (h : Sound.NoBad (ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 d.2)
      (rs.map noDigest)) : Sound.NoBad (ruleStep W s d) rs :=
  noBad_digest h

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.decide_step
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.noBad_digest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.canonical_digest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.noBad_ruleStep
