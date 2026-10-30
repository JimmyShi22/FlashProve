-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandLe.lean: what one instance needs of an oracle message is at most what N ≥ 1
instances need.

Statements (each a `Prop` in `Cb.Spec`) and proofs.
Cb/Ld/LdLinCloseDemand.lean counts, test by test, the long positions that a closing needs of each
oracle message at one instance (`D.need`); Cb/Ld/LdLinCloseDemandV.lean the same for a test that is
run in every one of N slots (`D.needV`: a shared oracle message counts N times). Both bounds are
used of a plan for the online phase; the record asks of it those for N alone (`LdObjP.HypR`,
Cb/Obj/LdObjectPlan.lean).

Main names:
  `Spec.ldDemandLe_need`: D.need b' o ≤ D.needV N sh b' o, for N ≥ 1.
  `Spec.ldDemandLe_mono`: `D.need` is monotone in what is needed afterwards.
  `Spec.ldDemandLe_plan`: for the plan's two tests, and N ≥ 1: the number for one instance is at
    most the number for N (the second test run in every slot). So the bounds for one instance follow
    from those for N.

Limits: this file says nothing at N = 0.
-/
import Cb.Ld.LdLinCloseDemandV

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

def ldDemandLe_need : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (N : ℕ) (sh : S.O → Prop)
      [DecidablePred sh] (b' : (S.sub D.kp).O → ℕ) (o : S.O),
    1 ≤ N → D.need b' o ≤ D.needV N sh b' o

def ldDemandLe_mono : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (b₁ b₂ : (S.sub D.kp).O → ℕ),
    (∀ a, b₁ a ≤ b₂ a) → ∀ o, D.need b₁ o ≤ D.need b₂ o

/-- The plan: one instance against N. -/
def ldDemandLe_plan : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype κ] [Fintype J] [Fintype Y]
      (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (N : ℕ) (b' : p.S₂.O → ℕ) (o : C.S.O),
    1 ≤ N → T.D₁.need (T.D₂.need b') o ≤ T.D₁.need (T.D₂.needV N (fun a => C.isSh a.1) b') o

end Spec

theorem ldDemandLe_need : Spec.ldDemandLe_need := by
  intro E _ _ S D N sh _ b' o hN
  unfold LdRunD.need LdRunD.needV
  refine Nat.add_le_add_right ?_ _
  by_cases hm : D.G.mem o
  · rw [if_pos hm, if_pos hm]
    by_cases hs : sh o
    · rw [if_pos hs]
      exact Nat.le_mul_of_pos_left _ hN
    · rw [if_neg hs]
  · rw [if_neg hm, if_neg hm]

theorem ldDemandLe_mono : Spec.ldDemandLe_mono := by
  intro E _ _ S D b₁ b₂ h o
  unfold LdRunD.need
  refine Nat.add_le_add_left ?_ _
  by_cases hk : D.kp o
  · rw [dif_pos hk, dif_pos hk]
    exact h _
  · rw [dif_neg hk, dif_neg hk]

theorem ldDemandLe_plan : Spec.ldDemandLe_plan := fun E _ _ _ _ _ _ _ _ _ C p T N b' o hN =>
  ldDemandLe_mono E C.S T.D₁ _ _
    (fun a => ldDemandLe_need E p.S₁ T.D₂ N (fun a => C.isSh a.1) b' a hN) o

end Cb
