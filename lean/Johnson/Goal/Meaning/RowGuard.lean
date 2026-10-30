-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RowGuard.lean: the clauses of Means (Johnson/Goal/Meaning/Row.lean) ask neither
too much nor too little.

Means X pp i x w says what the hidden values w of a proof must say, sub-proof by sub-proof: 12
groups of layers, 12 attention sub-proofs, the head. Johnson/Goal/Meaning/Row.lean shows that Means
gives the plain statements of Johnson/Meaning/Says.lean (says_of_means), and so that the request is
true under its policy. This file shows the way back: at public files in the goals' scope, for every
index i and every request x that is true at i under the files' policy, there are hidden values that
meet Means, and their token is the request's own.

Main theorems:
  means_of_true: the way back.
  means_iff_true: some hidden values meet Means exactly if the request is true under its policy.

The hidden values: the lists are those that the library makes of the honest trace (ordsL_of_true,
Johnson/Road/Lane5TopLTrue.lean), read by list numbers (lists_of_ordsL, Johnson/Meaning/Lists.lean).
The head's last stream is the stream that the last group's list holds; that it is the integer
program's last stream is the second conclusion of layersSay (Johnson/Goal/Meaning/LayersSay.lean),
whose premise, the bound 2^39, holds wherever all 25 sub-proofs are in order (lastOf_bound_of_ords).

What is not claimed. That an honest prover's files hold these values. Nothing on a protocol.
-/
import Johnson.Goal.Meaning.Row
import Johnson.Goal.Meaning.LayersSay
import Johnson.Road.Lane5TopLTrue

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **Every true request has hidden values that meet Means**, and their token is the request's. -/
theorem means_of_true (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref)
    (T : Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x) :
    ∃ w : Hid, w.tok = x.y ∧ Means X pp i x w := by
  have A := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS' ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  have T' : Policy.IsTrueUnder (scalesAt X) (Hd.polOf X.hS) i x := by
    rw [← tS', ← tP]
    exact T
  have hre : x.r < x.e := T.2.1.1
  obtain ⟨Zl, ZA, O⟩ : ∃ (Zl : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
        (Hd.shapeA X) i.mat x Zl ZA :=
    ⟨_, _, ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1
      E.2.2.2.2 E.2.2.1 E.2.2.2.1 hs hpol i x T'⟩
  have N := lists_of_ordsL B.groups O
  have bound := lastOf_bound_of_ords hR h A hre O
  obtain ⟨-, same⟩ := layersSay Z pp lay X hR h A i x _ _ N.layer N.att N.seamFF N.seamA bound
  have S : Says pp i.index.val x (streamOf pp i.index.val x) := says_of_true T
  refine ⟨⟨x.y, fun g => mzA X.y (Zl (2 * g)) g, ZA, lastOf X.y (mzA X.y (Zl (2 * 11)) 11)⟩, rfl,
    fun g hg => ?_, fun g hg => ?_, fun _ _ _ _ => rfl, ?_⟩
  · obtain ⟨a, b, c, d, e⟩ := layer_fields (N.layer g hg)
    exact ⟨a, b, c, d, e, fun h0 => N.seamFF g h0 hg⟩
  · have R := (N.att g hg).rel
    exact ⟨R.1, R.2.1, fun k b g' n hv => R.2.2 (.at1 k b g' n) hv,
      fun b g' n hv => R.2.2 (.at2 b g' n) hv, fun b g' n hv => R.2.2 (.at3 b g' n) hv,
      N.seamA g hg⟩
  · exact (says_iff_halves.1 S).2.congr (fun a ha j hj => (same a ha j hj).symm)
      fun _ _ _ => rfl

/-- **Means asks neither too much nor too little.** -/
theorem means_iff_true (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) :
    (∃ w : Hid, Means X pp i x w) ↔ Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x :=
  ⟨fun ⟨_, M⟩ => (isTrueUnder_iff_says (Cm.Scales.of pp) pp.pol i x).2
      ⟨_, says_of_means layersSay hR h (Hd.core_of_scope hZ hR h) M⟩,
    fun T => let ⟨w, _, M⟩ := means_of_true hZ hR h i x T; ⟨w, M⟩⟩

end Meaning

#print axioms Meaning.means_of_true
#print axioms Meaning.means_iff_true
