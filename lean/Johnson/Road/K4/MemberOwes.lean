-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberOwes.lean: TWO FIELDS OF THE RECORD `Plan4L.Owes`
(Johnson/Road/K4/CloseK.lean), THE PLAN's PUBLIC LINES AND THE ROTARY TABLES' FIT, AT THE VALUE AT
THE REFERENCE SIZES (`refL`, Johnson/Road/K4/RefValue.lean) and the record that the verifier's own
`publicOf` returns. Three statements: `pubLines_of_record` and `rope_of_record`
(Johnson/Road/K4/PubLinesRec.lean), laid near the fields' own forms (see the limits).

  `pubLines_all`: one s0 serves every list of tokens.
  `ref_lines`: the field lines, at s := weightShape X.P X.y, lk := `kRef`, tl := the group's plan's.
  `ref_rope`: the field rope, at every yes of a piece.

Limits. Premises that stay: `publicOf`'s return; the tests `recordB` (both) and `tablesB` (lines)
say true: a run, no theorem (Johnson/Road/Ends/GuardRec.lean); hcap (lines): in neither test; the
place holds the record's layers and, for lines, the group's plan. `ref_lines` gives SOME s0.
`ref_rope` does not ask the promise in front, which the field has. The same two fields stand in
`Plan4L.Owes2` (Johnson/Road/K4/CloseK2.lean). No soundness is concluded. What is a theorem, what a
run and what a premise: also the heads of RefValue.lean and PubLinesRec.lean.
-/
import Johnson.Road.K4.RefValue
import Johnson.Road.K4.NormWordsOfHear
import Johnson.Road.K4.CloseK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Road.Alg (recordB tablesB)
open Inst.Model (Scl tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- One s0 serves every list of tokens. -/
theorem pubLines_all {g : ℕ} (h : publicOf pol KL lay = .ok X) (t : recordB X g = true)
    (tt : tablesB X.layers.y = true) {hp : HPlan2} (hG : X.G[g]? = some hp)
    (hcap : Dim.ref.cap = (layerShape X.P).lidb) :
    ∃ s0, ∀ tk : Array Nat, PubLines { X.layers with tokv := tk } g (layerShape X.P) X.P.polCalls
      Dim.ref tbRef (weightShape X.P X.y) kRef s0 hp.tl := by
  obtain ⟨s0, P0⟩ := pubLines_of_record h t tt hG hcap #[]
  refine ⟨s0, fun tk => ?_⟩
  obtain ⟨s1, P1⟩ := pubLines_of_record h t tt hG hcap tk
  have e : s1 = s0 := Except.ok.inj (P1.hs0.symm.trans P0.hs0)
  exact e ▸ P1

variable [scl : Scl] {M Xs T Wt Cl : Type} {Fr : Frame} {p : Par} {tk : Array Nat}

/-- **The field lines.** -/
theorem ref_lines (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (tt : tablesB X.layers.y = true) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hcap : Dim.ref.cap = (layerShape X.P).lidb) :
    ∃ s0, ∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
      (refL R p.g hg nT nI).plan.full.D (refL R p.g hg nT nI).plan.full.tb
      (weightShape X.P X.y) kRef s0 p.hp.tl := by
  obtain ⟨s0, H⟩ := pubLines_all h t tt hG hcap
  refine ⟨s0, fun tk' => ?_⟩
  rw [hP]
  exact H tk'

/-- **The field rope.** -/
theorem ref_rope (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (L : Seat T)
    (pc : Piece (ckP .two) Fr T Cl Wt) :
    ∀ a τ fo o G, Yes L p pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < p.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := p.P.wsLay, rope := p.P.rope, rs := o.K.rs, rt := rt }
          (refL R p.g hg nT nI).plan.full.D (refL R p.g hg nT nI).plan.full.tb
          (p.g * p.P.y.Lam) lam := by
  intro a τ fo o G Y rt lam hlam
  obtain ⟨vy, vsc, vg, _⟩ := env_of_hear Y.hears
  rw [hP] at vy vsc hlam ⊢
  exact rope_of_record h t vy vsc vg o.K.rs rt hlam

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pubLines_all
#print axioms OnBytes.Road.K4.ref_lines
#print axioms OnBytes.Road.K4.ref_rope
