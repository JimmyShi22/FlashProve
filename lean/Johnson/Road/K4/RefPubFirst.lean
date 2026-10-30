-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefPubFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/RefPub.lean's FIVE
STATEMENTS: THE PUBLIC PREMISES OF THE THEOREMS ON K4's BLOCK AT THE FIRST GROUP's VALUE AT THE
REFERENCE SIZES (`refLF`, Johnson/Road/K4/RefValueFirst.lean), FROM THE RECORD OF SENTENCES `RefPub
X g` IN THE PLACE OF THE BOOLEAN TESTS. Four statements: `refF_meets` (RefValueFirst.lean),
`refF_valueIs` (Johnson/Road/K4/MemberKFirst.lean), `refF_lines_pub` and `refF_rope`
(Johnson/Road/K4/MemberOwesFirst.lean), to the letter in their conclusions. `refP_hk` (RefPub.lean)
speaks of every group.

  `refPF_meets`, `refPF_valueIs`, `refPF_lines_pub`, `refPF_rope`.

Limits. THE PUBLIC SIDE ALONE. `RefPub` is a premise; so is hla (the shape's number la is 16) in the
first two: in the goals' scope both are theorems (`refPub_in_scope`, `scope_la`,
Johnson/Road/K4/RefInScope.lean). The proofs are those of the four statements named. No soundness is
concluded.
-/
import Johnson.Road.K4.RefPub
import Johnson.Road.K4.MemberKFirst
import Johnson.Road.K4.MemberOwesFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public publicOf layerShape weightShape)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef)
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)

variable [scl : Scl] {M Xs T Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`MeetsF` holds of the first group's value**, under `RefPub`, where the group is the first and
la is 16. -/
theorem refPF_meets (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) :
    (refLF R tok nT nI).planF.MeetsF p (layerShape X.P) X.P.polCalls := by
  obtain ⟨s0, H, _⟩ := B.lines p.hp hG
  obtain ⟨s1, s2⟩ := refF_sizes (H #[]).hy (H #[]).Z hla
  exact (refLF R tok nT nI).planF.meetsF_public h hP hG B.covers (H #[]).Z
    (wsLayOf_units (H #[]).hlw).1.symm hg0 s1.symm s2.symm

/-- **`ValueIs` holds of the first group's value at the record's own two numbers of end values**,
under `RefPub`, where the group is the first, la is 16 and the section's table of scales is
`sclX X p.g`. -/
theorem refPF_valueIs (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ)
    (h : publicOf pol KL lay = .ok X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) :
    Plan4L.ValueIs (refLF R tok (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))).toPlan4L
      p (layerShape X.P) := by
  have A := refPF_meets R tok (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))) h B hP hG hg0
    hla
  have eg : p.g = 0 := beq_iff_eq.mp hg0
  have eT := A.nEndT_eq
  rw [hP] at eT
  refine ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, Nat.le_of_eq eT.symm,
    (refF_room R tok _ _).1, rfl, rfl, by rw [hscl, hP], ?_⟩
  rw [eg, Nat.zero_mul]
  rfl

/-- **One s0 serves the public lines and the lookup's shape**, under `RefPub`. -/
theorem refPF_lines_pub (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp) :
    ∃ s0, (∀ tk', PubLines { p.P with tokv := tk' } p.g (layerShape X.P) X.P.polCalls
        (refLF R tok nT nI).planF.fullF.D (refLF R tok nT nI).planF.fullF.tb
        (weightShape X.P X.y) kRef s0 p.hp.tl) ∧
      ∃ pb, p.P.y.fo = { s0 with pub := pb } := by
  obtain ⟨s0, H, pb, e⟩ := B.lines p.hp hG
  refine ⟨s0, fun tk' => ?_, ?_⟩
  · rw [hP]
    exact H tk'
  · rw [hP]
    exact ⟨pb, e⟩

/-- **The rotary tables' fit at every yes of a piece**, under `RefPub`. -/
theorem refPF_rope (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) (B : RefPub X p.g)
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
  exact B.rope o.v vy vsc vg o.K.rs rt lam hlam

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.refPF_meets
#print axioms OnBytes.Road.K4.refPF_valueIs
#print axioms OnBytes.Road.K4.refPF_lines_pub
#print axioms OnBytes.Road.K4.refPF_rope
