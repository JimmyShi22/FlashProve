-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LayerJoint.lean: the layers' joint: at all public files in the goals' scope,
the library's record on a group of layers (LayerOrd, Johnson/Road/FormsKeysLinkL.lean) follows from
two named relations at the group's own matrices.

LayerOrd has five clauses under the names of Johnson/Road/Rows/LayerTop.lean: SmallM, NormField,
HotField, EmbField, KeyField. The two relations, both in the library (Johnson/Road/Lane5SplitG.lean;
Johnson/Road/Lane5Split.lean):
  LayerR0: the group's meaning without its lookup clause.
  CallsAt.InTables, at the calls Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf: every key of each of the
    eight calls lies in the call's table, as the verifier's records of the calls have it.
WHICH CLAUSE HANGS ON WHICH.
  layerR0_iff: LayerR0 is SmallM, NormField, HotField and EmbField together: four of the five.
    General.
  keyField_in_scope: InTables gives KeyField, the fifth. In scope; it is layerBridge_in_scope
    (Johnson/Goal/Meaning/BridgeScope.lean) under KeyField's name.
  layerOrd_in_scope: so the two give LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x, for all
    matrices Mz and Wi and every request x.
  layerOrds_in_scope: the same for all twelve groups at a family of lists.
Premises beside the three facts on the files and g < 12: that layTables and weighedOf return (hl,
hw: functions of public data; a run of the check that has returned has computed both).
Not claimed: LayerR0 or InTables of anything. Who gives SmallM is not said.
-/
import Johnson.Goal.Meaning.BridgeScope
import Johnson.Road.Rows.LayerTop

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5 OnBytes.Ends OnBytes.Road.Rows.Norms
open OnBytes.Model.Layer (Lay Shape Scales TableAsk TableAt layTables tableAsks)
open OnBytes.Model.Verify (publicOf Public layerShape)
open Inst.Model (Mat)

/-- LayerR0 is four of the five clauses. -/
theorem layerR0_iff {h : Shape} {sc : Scales} {y : Lay} {g : ℕ} {Mz : Mats ℤ} {Wi : Mat}
    {x : Cm.Seg.XI} :
    LayerR0 h sc y g Mz Wi x ↔
      SmallM y Mz ∧ NormField h sc y g Mz Wi x ∧ HotField h sc y g Mz Wi x ∧
        EmbField h sc y g Mz Wi x :=
  ⟨fun R => ⟨R.1, fun k ν i hv => R.2 (.jn k ν i) hv, fun l i hv => R.2 (.j10 l i) hv,
      fun j i hv => R.2 (.j11 j i) hv⟩,
    fun ⟨hS, hN, hH, hE⟩ => ⟨hS, fun j hv => by
      cases j with
      | jn k ν i => exact hN k ν i hv
      | j10 l' i => exact hH l' i hv
      | j11 j' i => exact hE j' i hv⟩⟩

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- InTables gives the fifth clause. -/
theorem keyField_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} (I : (Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf).InTables) :
    KeyField (layerShape X.P) X.layers.sc X.y g Mz Wi :=
  layerBridge_in_scope hZ hR h tokv hg hl hw Mz Wi I

/-- THE LAYERS' JOINT. -/
theorem layerOrd_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) {g : ℕ} (hg : g < 12)
    {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks X.y X.layers.rd g) 0 = some r)
    (hw : ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    {Mz : Mats ℤ} {Wi : Mat} {x : Cm.Seg.XI}
    (R : LayerR0 (layerShape X.P) X.layers.sc X.y g Mz Wi x)
    (I : (Alg.callsG (pubAt X tokv) g Mz Wi nOf kOf).InTables) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x :=
  layerOrd_iff_split.2 ⟨R, layerBridge_in_scope hZ hR h tokv hg hl hw Mz Wi I⟩

/-- All twelve groups, at a family of lists: own (2 g) is the list of group g. -/
theorem layerOrds_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (tokv : Array ℕ) (own : ℕ → Mats ℤ) {Wi : Mat}
    {x : Cm.Seg.XI}
    (hl : ∀ g < 12, ∃ mats r, layTables mats (tableAsks X.y X.layers.rd g) 0 = some r ∧
      ∀ cd ∈ X.y.calls, ∃ wg, (Alg.envG (pubAt X tokv) g r.1).weighedOf cd = some wg)
    (R : ∀ g < 12, LayerR0 (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x)
    (I : ∀ g < 12, (Alg.callsG (pubAt X tokv) g (own (2 * g)) Wi nOf kOf).InTables) :
    ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (own (2 * g)) Wi x := by
  intro g hg
  obtain ⟨mats, r, h1, h2⟩ := hl g hg
  exact layerOrd_in_scope hZ hR h tokv hg h1 h2 (R g hg) (I g hg)

#print axioms layerR0_iff
#print axioms keyField_in_scope
#print axioms layerOrd_in_scope
#print axioms layerOrds_in_scope

end Meaning.P34
