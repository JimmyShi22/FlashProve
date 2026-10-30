-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/Pub34All.lean: all fields of the record Pub34
(Johnson/Road/Rows/LayerEnds34.lean:182 ff.) that speak of the public files alone, in one statement,
at all public files in the goals' scope.

From the three facts VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp,
publicOf Z.pol Z.KL lay = .ok X, and Numerals ρ (for the reading Reading.gl that is
gl_numerals, Johnson/Road/FormsKeysKit.lean:589). The letters: h := layerShape X.P,
pc := X.P.polCalls, y := X.y, sc := X.layers.sc, rd := X.layers.rd, D := DF, tb := tbRef,
s := weightShape X.P X.y, lk := kRef.

In the record's names: hy · S · hs · hrd · Z · hc · hN · hfl · Zw · hsL · hlw · h4 (pub34_public);
that there are twelve groups, against which hg is to be held; hs0 (shape_of_layout,
Johnson/Road/FormsKeysShape.lean:99); htm | hNM for the plan of every group; the rows and columns of
the matrices that a group's check takes from the public record (no field of the record: the list at
which hl lays the tables); hpad; R.
The other fields are letters of a run. Two of them, hl and hTS, are functions of X.y, X.layers.rd
and the group alone: that these two functions return is not shown here; a run that has returned
pays it. On R: which layers have the rotary step is a fact of the goals' scope, not of a test of the
verifier: the goals' reader refuses a scale file with other flags; the verifier takes any flag that
is 0 or 1.
-/
import Johnson.Goal.Meaning.PadScope
import Johnson.Goal.Meaning.RopeScope
import Johnson.Road.FormsKeysShape

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv layout scalesHeld readsOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (used lut)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- All fields of Pub34 that speak of the public files alone, at all public files in the goals'
scope. hg is not among them: it speaks of the caller's group, and stays a premise here too
(c.v.g < 12); what is shown is the number against which it is held: twelve groups. -/
theorem pub34_all (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) :
    (layout (layerShape X.P) X.P.polCalls = .ok X.y ∧ Switches (layerShape X.P) ∧
      scalesHeld (layerShape X.P) X.layers.sc = .ok () ∧ readsOf X.y = .ok X.layers.rd ∧
      Sized (layerShape X.P) DF ∧ DF.cap = (layerShape X.P).lidb ∧ LinesAre X.y ∧
      (∀ k : Fin 8, (layerShape X.P).nmin - (layerShape X.P).ll - (layerShape X.P).lt ≤
        Nat.clog 2 (used DF k)) ∧
      SizedW (weightShape X.P X.y) DF.P ∧ (weightShape X.P X.y).L = (layerShape X.P).L ∧
      wsLayOf (weightShape X.P X.y) true kRef = .ok X.layers.wsLay ∧
      (layerShape X.P).p4 = true) ∧
    X.y.NGr = 12 ∧
    (∃ s0 pub, Forest.shape X.y.cl X.y.h.lidb = .ok s0 ∧ X.y.fo = { s0 with pub := pub }) ∧
    (∀ g hp, X.G[g]? = some hp →
      (hp.tl.mats.map fun M => (M.m, M.k)) = matsR X.y g ∧ hp.tl.NM = hp.tl.mats.size) ∧
    (∀ g, ((X.layers.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR X.y g) ∧
    (∀ k : Fin 8, ρ.val (ofF ((X.y.cl.getD k.val {}).tauAt (X.y.cl.getD k.val {}).t0)) =
      (((lut tbRef k).pad : ℤ) : K)) ∧
    ∀ c : ClaimEnv, c.v.y = X.y → c.v.sc = X.layers.sc → c.rope = X.layers.rope → c.v.g < 12 →
      ∀ lam, lam < c.v.y.Lam → RopeFits ρ c DF tbRef (c.v.g * c.v.y.Lam) lam :=
  ⟨pub34_public hZ hR h, (Hd.public_of_core h (Hd.core_of_scope hZ hR h)).groups,
    shape_of_layout (pub34_public hZ hR h).1, fun _ _ hg => tails_of_public h hg,
    mats_of_public h, hpad_in_scope hZ hR h hρ,
    fun c hy hsc hrp hg => Rope.ropeFits_in_scope hZ hR h hρ c hy hsc hrp hg⟩

#print axioms pub34_all

end Meaning.P34
