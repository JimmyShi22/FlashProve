-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberOwesFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/MemberOwes.lean AND
OF `ref_lines_pub` (Johnson/Road/K4/MemberFront.lean): THE PLAN's PUBLIC LINES, THE LOOKUP's SHAPE
AND THE ROTARY TABLES' FIT, AT THE FIRST GROUP's VALUE AT THE REFERENCE SIZES (`refLF`,
Johnson/Road/K4/RefValueFirst.lean) and the record that the verifier's own `publicOf` returns. Two
statements: `pubLines_all` (MemberOwes.lean), `shape_of_layout` (Johnson/Road/FormsKeysShape.lean)
and `rope_of_record` (Johnson/Road/K4/PubLinesRec.lean), which speak of every group, laid at these
letters.

  `refF_lines_pub`: one s0 serves the public lines at every list of tokens, and the plan's shape of
    the lookup is s0 with another field pub.
  `refF_rope`: the rotary tables' fit at every yes of a piece.

Limits. Premises that stay: `publicOf`'s return; the tests `recordB` (both) and `tablesB` (lines)
say true: a run, no theorem (Johnson/Road/Ends/GuardRec.lean); hcap (lines): in neither test; the
place holds the record's layers and, for lines, the group's plan. `refF_lines_pub` gives SOME s0.
`refF_rope` does not ask the promise in front. No premise says that the group is the first. The same
two from the record of sentences `RefPub` in the tests' place: Johnson/Road/K4/RefPubFirst.lean. No
soundness is concluded. What is a theorem, what a run and what a premise: also the heads of
RefValue.lean and PubLinesRec.lean.
-/
import Johnson.Road.K4.RefValueFirst
import Johnson.Road.K4.MemberOwes
import Johnson.Road.FormsKeysShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Road.Alg (recordB tablesB returns_of_record)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)

variable [scl : Scl] {M Xs T Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **One s0 serves the public lines and the lookup's shape.** -/
theorem refF_lines_pub (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (tt : tablesB X.layers.y = true) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hcap : Dim.ref.cap = (layerShape X.P).lidb) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refLF R tok nT nI).planF.fullF.D (refLF R tok nT nI).planF.fullF.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∃ pb, p.P.y.fo = { s0 with pub := pb } := by
  obtain ⟨s0, H⟩ := pubLines_all h t tt hG hcap
  obtain ⟨s1, pb, hs, e⟩ := shape_of_layout (returns_of_record h t).1
  obtain rfl : s1 = s0 := Except.ok.inj (hs.symm.trans (H tk).hs0)
  refine ⟨s1, fun tk' => ?_, ?_⟩
  · rw [hP]
    exact H tk'
  · rw [hP]
    exact ⟨pb, e⟩

/-- **The rotary tables' fit.** -/
theorem refF_rope (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (L : Seat T)
    (pc : Piece (ckP .two) Fr T Cl Wt) :
    ∀ a τ fo o G, Yes L p pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < p.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := p.P.wsLay, rope := p.P.rope, rs := o.K.rs, rt := rt }
          (refLF R tok nT nI).planF.fullF.D (refLF R tok nT nI).planF.fullF.tb
          (p.g * p.P.y.Lam) lam := by
  intro a τ fo o G Y rt lam hlam
  obtain ⟨vy, vsc, vg, _⟩ := env_of_hear Y.hears
  rw [hP] at vy vsc hlam ⊢
  exact rope_of_record h t vy vsc vg o.K.rs rt hlam

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.refF_lines_pub
#print axioms OnBytes.Road.K4.refF_rope
