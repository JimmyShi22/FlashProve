-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/K3FormsLayersJoint.lean

«FORMS AGAINST KEYS», THE LAYERS: THE TABLE OF JOINTS' OWN TERM.
Nothing on hiding. No property of a release.
K3FormsLayers.lean has: keyVec at the casts of Mz, Wi = G.kvG at cellMW Mz Wi, in scope. HERE THAT IS LAID AT THE VERY TERM OF THE CALLER OF
THE PROVED LOOKUP BLOCK AT A LAYERS' LINK (Johnson/Desc/First/Look/K3CallerLay.lean): (layLay p fs lm first ns tl nr nc).K () (msgLay … m) c n,
at p := the public record's shape, scales, layout and the group g, UNDER THAT FILE's TWO NAMED READINGS MatsAre m Mz and WeightsAre g m Wi:
  layers_joint_key_is_kvG: at any Mz, Wi.
  layers_joint_key_is_named_key_at_theTrace: at Mz := theTrace X i x (2 g), Wi := i.mat, a served request: the right side in the lookups' named
    letters: G.kvG X.layers g (fromG X (cellOf X (theTrace X i x)) (entryOf i) g) (Honest/K3/Law/Thread/ExchangeFillAt.lean: fills_layers):
    not guarded by Lean here.
LEFT AS PREMISES: MatsAre, WeightsAre, n < 2 ^ aC DF c.
-/
import Johnson.HonestTrace.Joint.K3FormsLayers
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Goal.HonestTrace.FromCellsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Look

namespace K3Forms

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Road.Alg (cellMW)
open OnBytes.HonestTrace (theTrace ServesAt fromG cellOf entryOf)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (aC)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {x₁ : Place} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : Nat}

/-- **The caller's key at a layers' link is G.kvG**, under the two named readings, in the goals' scope. -/
theorem layers_joint_key_is_kvG (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) (fs : Forest.Shape) (lm first : Nat)
    (m : (laySg x₁ D rad oW).Msg) (Mz : OnBytes.Road.Mats ℤ) (hM : MatsAre x₁ tl D rad oW wOf nr nc m Mz)
    (Wi : Inst.Model.Mat) (hW : WeightsAre x₁ tl D rad oW wOf nr nc g m Wi) (c : Fin 8) (n : ℕ)
    (hn : n < 2 ^ aC DF c) :
    (layLay ⟨layerShape X.P, X.layers.sc, X.y, g⟩ fs lm first x₁.ns tl nr nc).K ()
        (msgLay x₁ tl D rad oW wOf nr nc m) c.val n =
      Ends.G.kvG X.layers g (cellMW Mz Wi) c.val n := by
  rw [layLay_K, hM, show (fun l => Inst.Model.FFSeg.layerR Inst.Model.ppref Inst.Model.Layout.kRef
      (wOfE (msgLay x₁ tl D rad oW wOf nr nc m)) (4 * g + l)) =
    fun l => Inst.Model.FFSeg.layerR Inst.Model.ppref Inst.Model.Layout.kRef
      (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l) from funext hW]
  exact OnBytes.Road.Alg.K3Forms.layers_key_vector_is_kvG_in_scope hZ hR h hg Mz Wi c n hn

/-- **AT theTrace, IN THE LOOKUPS' NAMED LETTERS.** -/
theorem layers_joint_key_is_named_key_at_theTrace (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx}
    {x : Inst.Model.Instance Inst.Model.ppref} (S : ServesAt X i x) {g : ℕ} (hg : g < 12)
    (fs : Forest.Shape) (lm first : Nat) (m : (laySg x₁ D rad oW).Msg)
    (hM : MatsAre x₁ tl D rad oW wOf nr nc m (theTrace X i x (2 * g)))
    (hW : WeightsAre x₁ tl D rad oW wOf nr nc g m i.mat) (c : Fin 8) (n : ℕ)
    (hn : n < 2 ^ aC DF c) :
    (layLay ⟨layerShape X.P, X.layers.sc, X.y, g⟩ fs lm first x₁.ns tl nr nc).K ()
        (msgLay x₁ tl D rad oW wOf nr nc m) c.val n =
      Ends.G.kvG X.layers g (fromG X (cellOf X (theTrace X i x)) (entryOf i) g) c.val n := by
  rw [OnBytes.HonestTrace.fromG_cellOf (OnBytes.HonestTrace.namesFit_theTrace hZ hR h S) i hg]
  exact layers_joint_key_is_kvG hZ hR h hg fs lm first m _ hM _ hW c n hn

end K3Forms

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.K3Forms.layers_joint_key_is_kvG
#print axioms VerifiableInference.Desc.First.Look.K3Forms.layers_joint_key_is_named_key_at_theTrace
