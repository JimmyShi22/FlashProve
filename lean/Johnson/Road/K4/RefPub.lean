-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefPub.lean: ONE RECORD OF PUBLIC FACTS, `RefPub X g`, FROM WHICH THE PUBLIC
PREMISES OF THE THEOREMS ON K4's BLOCK FOLLOW AT THE VALUE AT THE REFERENCE SIZES (`refL`,
Johnson/Road/K4/RefValue.lean), IN THE PLACE OF THE BOOLEAN TESTS. WHY: the statements `ref_meets`,
`ref_valueIs`, `ref_hk`, `ref_lines_pub`, `ref_rope` take "the tests `recordB` and `tablesB` say
true", "K4's text covers the record" and hcap as premises. At a closed record a run can evaluate
these; a caller who has the record only as `publicOf`'s return on files of some scope cannot hand
them in. The record below holds what these statements spend of the tests, as sentences. It has two
doors: `refPub_of_tests` (here), for runs, and `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean),
at all public files of the goals' scope, with no test.

  `RefPub X g`: three fields: lines (for every plan of the group: one s0 at which the nineteen
    public lines `PubLines` hold for all tokens, and the layout's shape of the lookup is s0 with
    another field pub) · rope (the rotary tables' fit at every environment with the record's layout,
    scales and group) · covers.
  `refPub_of_tests`: the record from the two tests, covers and hcap.
  `pub_ok`: the layout's shape of the lookup passes `FoNums.ok`, from `publicOf`'s return alone.
  `refP_meets`, `refP_valueIs`, `refP_hk`, `refP_lines_pub`, `refP_rope`: the five statements named
    above, to the letter in their conclusions, from `RefPub` in the place of the tests. In `refP_hk`
    a plan of the group is asked for beside.

Limits. THE PUBLIC SIDE ALONE. `RefPub` is a premise of the five; that it holds anywhere is the two
doors' matter. The proofs are those of the five statements named, with the record's fields in the
tests' parts' places. A group that is not the first (`refP_meets`, `refP_valueIs`). No soundness is
concluded.
-/
import Johnson.Road.K4.MemberK
import Johnson.Road.K4.MemberFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (HPlan2 Env nEndT)
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open OnBytes.Road.Alg (recordB tablesB returns_of_record)
open Inst.Model (Scl tbRef)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (covers Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- **What the statements at the reference value spend of the public record**, at group g. -/
structure RefPub (X : Public) (g : ℕ) : Prop where
  /-- the nineteen public lines, at one s0 for all tokens; the layout's shape of the lookup -/
  lines : ∀ hp : HPlan2, X.G[g]? = some hp →
    ∃ s0, (∀ tk : Array Nat, PubLines { X.layers with tokv := tk } g (layerShape X.P)
        X.P.polCalls Dim.ref tbRef (weightShape X.P X.y) kRef s0 hp.tl) ∧
      ∃ pb, X.layers.y.fo = { s0 with pub := pb }
  /-- the rotary tables' fit -/
  rope : ∀ v : Env, v.y = X.layers.y → v.sc = X.layers.sc → v.g = g →
    ∀ (rs rt : Array E) (lam : ℕ), lam < X.layers.y.Lam →
      RopeFits Reading.gl
        { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt } Dim.ref
        tbRef (g * X.layers.y.Lam) lam
  /-- K4's text covers the record -/
  covers : covers X.layers = true

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- **The door for runs**: the record from the two tests, covers and hcap. -/
theorem refPub_of_tests {g : ℕ} (h : publicOf pol KL lay = .ok X) (t : recordB X g = true)
    (tt : tablesB X.layers.y = true) (hc : covers X.layers = true)
    (hcap : Dim.ref.cap = (layerShape X.P).lidb) : RefPub X g where
  lines := fun hp hG => by
    obtain ⟨s0, H⟩ := pubLines_all h t tt hG hcap
    obtain ⟨s1, pb, hs, e⟩ := shape_of_layout (returns_of_record h t).1
    obtain rfl : s1 = s0 := Except.ok.inj (hs.symm.trans (H #[]).hs0)
    exact ⟨s1, H, pb, e⟩
  rope := fun _ vy vsc vg rs rt _ hl => rope_of_record h t vy vsc vg rs rt hl
  covers := hc

/-- The layout's shape of the lookup passes the lookup's test on numbers, wherever `publicOf`
returns. -/
theorem pub_ok (h : publicOf pol KL lay = .ok X) : FoNums.ok X.layers.y.fo = true :=
  _root_.Fo.Pay.shapeOf_ok (_root_.Fo.layout_shape (Hd.publicH_of_public h).lay)

variable [scl : Scl] {M Xs T Wt Cl : Type} {Fr : Frame} {p : Par} {tk : Array Nat}

/-- **`Meets` holds of the value**, under `RefPub`, in a group that is not the first, whatever the
table of scales. -/
theorem refP_meets (R : RefLetters M Xs) (hg : p.g < 12) (h : publicOf pol KL lay = .ok X)
    (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (nT nI : ℕ) :
    (refL R p.g hg nT nI).plan.Meets p (layerShape X.P) X.P.polCalls := by
  obtain ⟨s0, H, _⟩ := B.lines p.hp hG
  exact (refL R p.g hg nT nI).plan.meets_public h hP hG B.covers (H #[]).Z
    (wsLayOf_units (H #[]).hlw).1.symm hg0

/-- **`ValueIs` holds of the value at the record's own two numbers of end values**, under `RefPub`,
in a group that is not the first, where the section's table of scales is `sclX X p.g`. -/
theorem refP_valueIs (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (hg : p.g < 12)
    (h : publicOf pol KL lay = .ok X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) :
    Plan4L.ValueIs (refL R p.g hg (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))))
      p (layerShape X.P) := by
  have A := refP_meets R hg h B hP hG hg0 (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))
  have S7 := sevenSizes_of_meets A tk
  have L := laySizes_of_layout A.hy
  have eLam : p.P.y.Lam = 4 := by
    rw [L.Lam, ← A.Z.lL]
    rfl
  have e := S7.hEnd
  rw [hP] at e
  exact ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, e, (ref_room R p.g hg _ _).1, rfl, rfl,
    by rw [hscl, hP], by rw [eLam]; rfl⟩

/-- **The shifts of queries and keys**, in every layer, under `RefPub` at a group that has a plan,
under the table of scales `sclX X g`. -/
theorem refP_hk {g : ℕ} (hscl : scl = sclX X g) (B : RefPub X g) {hp : HPlan2}
    (hG : X.G[g]? = some hp) :
    ∀ l, (Dim.ref.Pl l).kq = (Dim.ref.Pl l).kk ∨
      (16 ≤ (Dim.ref.Pl l).kq ∧ 16 ≤ (Dim.ref.Pl l).kk) := by
  subst hscl
  obtain ⟨s0, H, _⟩ := B.lines hp hG
  exact hk_of_scalesHeld (admitted_of_layout (H #[]).hy (H #[]).S.p3) (H #[]).hs (H #[]).hg Dim.ref

/-- **One s0 serves the public lines and the lookup's shape**, under `RefPub`. -/
theorem refP_lines_pub (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refL R p.g hg nT nI).plan.full.D (refL R p.g hg nT nI).plan.full.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∃ pb, p.P.y.fo = { s0 with pub := pb } := by
  obtain ⟨s0, H, pb, e⟩ := B.lines p.hp hG
  refine ⟨s0, fun tk' => ?_, ?_⟩
  · rw [hP]
    exact H tk'
  · rw [hP]
    exact ⟨pb, e⟩

/-- **The rotary tables' fit at every yes of a piece**, under `RefPub`. -/
theorem refP_rope (R : RefLetters M Xs) (hg : p.g < 12) (nT nI : ℕ) (B : RefPub X p.g)
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
  exact B.rope o.v vy vsc vg o.K.rs rt lam hlam

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.refPub_of_tests
#print axioms OnBytes.Road.K4.pub_ok
#print axioms OnBytes.Road.K4.refP_meets
#print axioms OnBytes.Road.K4.refP_valueIs
#print axioms OnBytes.Road.K4.refP_hk
#print axioms OnBytes.Road.K4.refP_lines_pub
#print axioms OnBytes.Road.K4.refP_rope
