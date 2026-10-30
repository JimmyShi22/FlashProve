-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/GameKey.lean: in the real experiment of index privacy (`ZKCP.Gen.realExp`) the key in the
adversary's view is the committer's key.

Summary. So a property of the key fails in the view at most as often as it fails for the committer's
key, run from the empty table of oracle answers. This holds for any scheme, against every adversary
and environment, for any number of queries and batches. E2E/StringsInGame.lean uses it to carry "the
key's proofs are produced" into the experiment.

Main results.
  `game_key`: `Rom.Pr (realExp A Vt Z i N) {v | ¬ P v.ivk} ≤ PrFrom (Table.empty S) (A.C i) {key | ¬
    P key.1}`.

Terms: E2E/HidingTerms.lean.

Limits. About the key alone: nothing about what a session releases. No security property of any
scheme is stated.

Definitions and helper lemmas.
  `PrFrom_bind_event`: if the second of two programs in a row, started after a value without P,
    never ends in E, then the two end in E at most as often as the first ends in P.
  `loop_keeps`: steps 3 and 4 of the real experiment never change the view's key.


-/
import Johnson.Prover.All.End
import ZKCP.Gen

set_option autoImplicit false

open scoped ENNReal

namespace AtPublicFiles.Shown
open Rom Prob
open OnBytes.Prover (PrFrom_bind_le PrFrom_pure PrFrom_sample_le PrFrom_le_one)
open ZKCP.Gen (Arg AdvVerifier ViewEnv View realLoop realExp)

/-! ## 1. An event that the second program cannot bring about -/

/-- If the second program, started after a value without P, never ends in E, then the two in a row
end in E at most as often as the first ends in P. -/
theorem PrFrom_bind_event {S : OSpec} {α β : Type} (T : Table S) (c : OComp S α)
    (g : α → OComp S β) (P : α → Prop) (E : Set β)
    (h : ∀ a T', ¬ P a → PrFrom T' (g a) E = 0) :
    PrFrom T (c.bind g) E ≤ PrFrom T c {a | P a} := by
  classical
  rw [PrFrom_bind, PrFrom_eq_lazy, pr_map, pr_eq_expect]
  refine expect_mono _ fun out => ?_
  by_cases hP : P out.1
  · rw [if_pos (show out ∈ Prod.fst ⁻¹' {a | P a} from hP)]
    exact PrFrom_le_one _ _ _
  · rw [h _ _ hP]
    exact zero_le _

/-! ## 2. The real experiment never changes the key in the view -/

section
variable {S : OSpec} {I X W IVK ISK Pf : Type} (A : Arg S I X W IVK ISK Pf)
  (Z : ViewEnv S IVK X W Pf) (isk : ISK) (P : IVK → Prop)

theorem loop_keeps : ∀ (adv : AdvVerifier S X Pf) (n : ℕ) (v : View S IVK X Pf) (T : Table S),
    P v.ivk → PrFrom T (realLoop A Z isk adv n v) {v' | ¬ P v'.ivk} = 0
  | .halt, _, v, T, h => PrFrom_pure T v _ fun c => c h
  | .query o q k, n, v, T, h => by
    refine le_antisymm ?_ (zero_le _)
    have e : realLoop A Z isk (.query o q k) n v =
        (OComp.query o q .pure).bind fun r =>
          realLoop A Z isk (k r) n { v with trace := v.trace ++ [⟨o, q, r⟩] } := rfl
    rw [e]
    exact PrFrom_bind_le _ _ _ _ fun out _ =>
      (loop_keeps (k out.1) n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2 h).le
  | .sample m k, n, v, T, h => by
    refine le_antisymm ?_ (zero_le _)
    exact PrFrom_sample_le T m _ _ fun r =>
      (loop_keeps (k r) n { v with coins := v.coins ++ [r.val] } T h).le
  | .request _, 0, v, T, h => PrFrom_pure T v _ fun c => c h
  | .request k, n + 1, v, T, h => by
    unfold realLoop
    cases hz : Z v with
    | none => exact PrFrom_pure T v _ fun c => c h
    | some b =>
      refine le_antisymm ?_ (zero_le _)
      exact PrFrom_bind_le _ _ _ _ fun out _ =>
        (loop_keeps (k (b.released out.1.val)) n
          { v with sessions := v.sessions ++ [b.released out.1.val] } out.2 h).le

/-- **In the real experiment, against every adversary and every environment, the key in the view
lacks P at most as often as the committer's key does.** -/
theorem game_key (Vt : IVK → AdvVerifier S X Pf) (i : I) (N : ℕ) :
    Rom.Pr (realExp A Vt Z i N) (fun _ => {v | ¬ P v.ivk}) ≤
      PrFrom (Table.empty S) (A.C i) {key | ¬ P key.1} := by
  rw [Pr_eq_PrFrom]
  exact PrFrom_bind_event _ (A.C i)
    (fun key => realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) (fun key => ¬ P key.1) _
    fun key T' hk => loop_keeps A Z key.2 P _ N _ T' (not_not.1 hk)

end

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.PrFrom_bind_event
#print axioms AtPublicFiles.Shown.loop_keeps
#print axioms AtPublicFiles.Shown.game_key
