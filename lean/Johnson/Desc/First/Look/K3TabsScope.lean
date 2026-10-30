-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3TabsScope.lean: IN THE GOALS' SCOPE, AT EVERY ATTENTION LINK's OWN PLACE:
THE TWO PUBLIC PREMISES OF THE CLAUSE ON ATTENTION's KEYS: "every row of the verifier's table of a
call is a row of the library's" (TabsAre, Johnson/Desc/First/Look/K3CallerAttMeans.lean) and "the
pieces of each call fit into it". A carrying of a theorem in scope
(Meaning.Att.tabsA_in_scope, Johnson/Goal/Meaning/AttForInScope.lean) from its letters to the
lookups': four small equations. On public data alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: sentences on Verify.publicOf's value.
Used by K3CallsLeftR.lean, K3CallsOwedScope.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: Z, pp, lay, X as in the scope's theorems; g: a group below 12; x: what lookAt answers at
  link 2 g + 1.

THE FOUR EQUATIONS: x.fs = fsA X g (`fs_is_fsA`: by lookAt_att) · Ends.kN = Port.kOf (one body:
  rfl) · FoNums.tauN = Ends.tauN below the number of calls (tauF_eq, Johnson/Road/Lane5Rec.lean) ·
  the shape's call's n = Port.nOf (`nOf_is`: by SameCalls.callAt, Johnson/Road/Lane5ForIn.lean).

Main names: `tabsAre_of_tabsA` (no scope: from TabsA and SameCalls) · `tabsAre_scope`.

Limits. The full size's scope alone. Attention alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttMeans
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open Inst.Model.AttSeg

/-- The shape's call's n is the lookup's. -/
theorem nOf_is {S : Attention.Shape} {fs : Forest.Shape} (C : SameCalls S fs) (c : Fin 4) :
    Cb.LdLkp.Port.nOf fs c.val = (S.calls.getD c.val default).call.n := by
  unfold Cb.LdLkp.Port.nOf
  rw [C.callAt c.isLt]
  rfl

/-- **From the letters of TabsA (Johnson/Road/Lane5BridgeA.lean) to the lookups'.** -/
theorem tabsAre_of_tabsA {S : Attention.Shape} {fs : Forest.Shape} (T : TabsA S fs)
    (C : SameCalls S fs) :
    TabsAre S fs ∧ ∀ c : Fin 4, (dimOf S).used c ≤ 2 ^ Cb.LdLkp.Port.nOf fs c := by
  have hsz : fs.calls.size = 4 := by
    rw [C.calls, Array.size_map, C.size]
  refine ⟨fun c u hu => ?_, fun c => ?_⟩
  · obtain ⟨ι, hι, e⟩ := T.row c u hu
    refine ⟨ι, hι, ?_⟩
    rw [← e]
    have et : FoNums.tauN fs c.val u = OnBytes.Ends.tauN fs c.val u :=
      tauF_eq (by rw [hsz]; exact c.isLt) u
    rw [et]
  · rw [nOf_is C c]
    exact T.room c

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- The place's shape of the lookup is the plan's. -/
theorem fs_is_fsA {g : ℕ} {x : Place} (hp4 : X.p4 = true) (hN : X.NGr = 12) (hg : g < 12)
    (e : lookAt X (2 * g + 1) false = some x) : x.fs = Meaning.Att.fsA X g := by
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos hp4
  obtain ⟨a, ha, -, e1, -⟩ := lookAt_att e
    (by rw [hst, hN]; omega) (by rw [hst]; omega)
  rw [hst, show (2 * g + 1) / 2 = g by omega] at ha
  unfold Meaning.Att.fsA
  rw [ha, e1]
  rfl

/-- **hT AND hU, IN SCOPE.** -/
theorem tabsAre_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {x : Place}
    (e : lookAt X (2 * g + 1) false = some x) :
    TabsAre (Hd.shapeA X g) x.fs ∧
      ∀ c : Fin 4, (dimOf (Hd.shapeA X g)).used c ≤ 2 ^ Cb.LdLkp.Port.nOf x.fs c := by
  obtain ⟨hp4, hN, -, -⟩ := Meaning.scope_plans hZ hR h
  rw [fs_is_fsA hp4 hN hg e]
  exact tabsAre_of_tabsA (Meaning.Att.tabsA_in_scope hZ hR h hg)
    (Meaning.Att.sameCalls_in_scope hZ hR h hg)

end

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.tabsAre_of_tabsA
#print axioms VerifiableInference.Desc.First.Look.tabsAre_scope
