-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOneProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanOne.lean
(the rest of the plan without a splitting, with one group). By composition.
Named tools: `LdRowsD.supp_all` (a test that takes all rows and keeps nothing has the named
condition `X.Supp`). Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanOne.lean):
  `ldRowsOne_three`: the three clauses that a plan asks of "the rest"
  `ldRowsOne_tail`: the test for linear constraints with the plan's three tests
-/
import Cb.Ld.LdLinClosePlanOne

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- a test that takes all rows and keeps nothing: each row reads entries of its group, whatever its
coefficients -/
theorem LdRowsD.supp_all {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
    {Wp Cl B : Type} [Fintype B] {rows : B → Slf E Cl S.Ent} (X : LdRowsD S E₀ Wp rows)
    (hn : ∀ b, X.now b) (hk : ∀ o, ¬ X.kp o) : X.Supp :=
  ⟨fun _ _ _ n hm => absurd ((X.hc n.1).resolve_right (hk n.1)) hm, fun b hb => absurd (hn b) hb⟩

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldRowsOne_three : Spec.ldRowsOne_three E ι κ J Y := by
  intro C p B _ rowsA tgA X w₀ q₀ hn hk hrel hrelR hkeep hX hq
  haveI : IsEmpty {b // ¬ X.now b} := ⟨fun b => b.2 (hn b.1)⟩
  haveI : IsEmpty (p.S₂.sub X.kp).O := ⟨fun o => hk o.1 o.2⟩
  have hS : (X.one tgA w₀).Says :=
    ldRowsQ_cons E p.S₂ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ (X.supp_all hn hk)
      (ldRowsQ_nil E _ C.E₀ C.Wpa C.Sta _ X.rest (fun cl b => tgA cl b.1) w₀)
  refine ⟨ldRowsQ_saysA E ι κ J Y C p B rowsA tgA (X.one tgA w₀) hrel hrelR hkeep hS,
    ldRowsQ_ok E p.S₂ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ hX (ldChain_nil E _ C.E₀ C.Wpa w₀),
    fun V hV => ?_⟩
  obtain ⟨h1, h2⟩ := ldRowsQ_demand E p.S₂ C.E₀ C.Wpa C.Sta B (p.rowsL rowsA) tgA X _ q₀
    (fun _ => 0) (ldDemand_nil E _ C.E₀ C.Wpa w₀ q₀ _ hq) V hV
  exact ⟨h1,
    fun o =>
      (h2 o).trans
        ((ldDemand_le E p.S₂ X.run (fun _ => 0) o).trans (by rw [dif_neg (hk o)]; exact le_refl _))⟩

theorem ldRowsOne_tail : Spec.ldRowsOne_tail E ι κ J Y := by
  intro C p T B _ rowsA tgA X w₀ on0 εf Sn qa d q₀ ba hF hpy hS hr hD₁ hD₂ hn hk hrel hrelR
    hkeep hX hq hqa i1 i2 i3 i4
  obtain ⟨a1, a2, a3⟩ :=
    ldRowsOne_three E ι κ J Y C p B rowsA tgA X w₀ q₀ hn hk hrel hrelR hkeep hX hq
  exact ldLinPlan_tail E ι κ J Y C p (T.withRest (X.one tgA w₀)) on0 εf Sn qa d q₀ ba (fun _ => X.t)
    hF hpy hS hr a1 hD₁ hD₂ a2 a3 hqa i1 i2 i3 i4

end
end Cb
