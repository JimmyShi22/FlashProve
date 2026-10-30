-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/GameOne.lean: against the adversary that asks nothing and requests one batch, the real
experiment of index privacy (`ZKCP.Gen.realExp`) is the scheme's own run.

Summary. The environment names one fixed instance as the adversary's own. The result is an equation
of programs and holds for any scheme. E2E/StringsInGameOne.lean and E2E/StringsOpenInGame.lean use
it to restate bounds on the scheme's run as bounds in the experiment.

Main results.
  `realExp_one`: `realExp A oneAdv (oneEnv x w) i 1` is: the committer; the prover on the batch of
    the one pair (x, w); the view with the key, what that batch releases, no query and no coin.
  `pr_one_le`: so a property of (key, proof) fails for some proof in the view at most as often as
    for some proof of the run.

Terms: E2E/HidingTerms.lean.

Limits. One adversary, which asks no oracle query, and one environment, which reads nothing of the
view: so the instance is fixed before the oracles are sampled. Nothing is proved about any other. No
security property of any scheme is stated.

Definitions and helper lemmas.
  `oneAdv`, `oneEnv x w`: that adversary and that environment.
  `runArg`, `realExp_one_run`: the scheme's own run as a program; the experiment is that run with
    its result put into a view.
  `released_mem`: a proof that a batch releases is one of those that the prover returned.


-/
import Johnson.Prover.All.End
import ZKCP.Gen

set_option autoImplicit false

namespace AtPublicFiles.Shown
open Rom Prob
open OnBytes.Prover (PrFrom_bind_pure PrFrom_mono)
open ZKCP.Gen

variable {S : OSpec} {I X W IVK ISK Pf : Type}

/-- The adversary that asks nothing and requests one batch. -/
def oneAdv : IVK → AdvVerifier S X Pf := fun _ => .request fun _ => .halt

/-- The environment that names, whatever the view, one batch of the one instance x with the witness
w, as the adversary's own. -/
def oneEnv (x : X) (w : W) : ViewEnv S IVK X W Pf := fun _ => some [(x, w, true)]

theorem realExp_one (A : Arg S I X W IVK ISK Pf) (i : I) (x : X) (w : W) :
    realExp A oneAdv (oneEnv x w) i 1 =
      (A.C i).bind fun key => (A.P key.2 [(x, w)]).bind fun πs =>
        .pure ⟨key.1, [Batch.released [(x, w, true)] πs.val], [], []⟩ := rfl

theorem released_mem (b : Batch X W) (πs : List Pf) (y : X × Pf) (h : y ∈ b.released πs) :
    y.2 ∈ πs := by
  unfold Batch.released at h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h
  exact (List.of_mem_zip (List.mem_filter.1 hs).1).2

/-- **The scheme's own run**: its committer, then its prover at the batch of one pair. -/
def runArg (A : Arg S I X W IVK ISK Pf) (i : I) (x : X) (w : W) : OComp S (IVK × List Pf) :=
  (A.C i).bind fun key => (A.P key.2 [(x, w)]).bind fun πs => .pure (key.1, πs.val)

/-- The experiment is that run, with its result put into a view. -/
theorem realExp_one_run (A : Arg S I X W IVK ISK Pf) (i : I) (x : X) (w : W) :
    realExp A oneAdv (oneEnv x w) i 1 =
      (runArg A i x w).bind fun z =>
        .pure ⟨z.1, [Batch.released [(x, w, true)] z.2], [], []⟩ := by
  rw [realExp_one]
  unfold runArg
  simp only [OComp.bind_assoc]
  rfl

/-- **A property of (key, proof) fails for some proof in that experiment's view at most as often as
it fails for some proof of the scheme's own run.** -/
theorem pr_one_le (A : Arg S I X W IVK ISK Pf) (i : I) (x : X) (w : W) (P : IVK → Pf → Prop) :
    Rom.Pr (realExp A oneAdv (oneEnv x w) i 1)
        (fun _ => {v | ¬ ∀ s ∈ v.sessions, ∀ y ∈ s, P v.ivk y.2}) ≤
      PrFrom (Table.empty S) (runArg A i x w) {z | ¬ ∀ π ∈ z.2, P z.1 π} := by
  rw [Pr_eq_PrFrom, realExp_one_run, PrFrom_bind_pure]
  refine PrFrom_mono _ _ fun z hz hA => hz fun s hs y hy => ?_
  obtain rfl := List.mem_singleton.1 hs
  exact hA y.2 (released_mem _ _ y hy)

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.realExp_one_run
#print axioms AtPublicFiles.Shown.pr_one_le
#print axioms AtPublicFiles.Shown.realExp_one
#print axioms AtPublicFiles.Shown.released_mem
