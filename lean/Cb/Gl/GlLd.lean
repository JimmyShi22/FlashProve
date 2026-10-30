-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlLd.lean: two predicates on codes read under a transformation: "is a family of interleaved
Reed-Solomon codes with evaluation points in the prime field of p = 2^64 - 2^32 + 1 and symbols in
its cubic extension `E`, queried at common positions" (`IsGl`) and "is built from such families and
from families of copied codes" (`GlC`), and the five properties that each gives.

Definitions, statements (in `Cb.Gl.Spec`) and proofs.

Why: the blocks, and the records "within a third of the distances", ask of each code
(Cb/Ld/LdRel.lean: `LdCode E P`, any long positions P): laws, a distance as read, transparency, that
the transformation reads what it declares, zero knowledge of the encoding at t long positions.
Cb/Gl/GlCodesLd.lean has all that for the codes T.ld E R. Here it is put in a form that can be said
of a code that is a field in some record.

Main names (each statement under the hypotheses of its statement):
  `IsGl C d t`: C is, for some finite family of plain Reed-Solomon codes on subgroups of orders
    2^(a i) ≤ 2^32, of dimensions k i + 1 ≤ 2^(a i), message and randomness within the dimension,
    each with interleaved rows R i, read evenly at the long positions P (every position of
    component i is read mult i times): the code T.ld E R of Cb/Ld/LdRelRep.lean; d is at most
    mult i · (2^(a i) - k i) for all i; t is at most the number r i of uniform coordinates
    for all i.
  `Spec.gl_code`: `IsGl C d t` gives: laws, transparent, reads what it declares, distance d as read,
    zero knowledge of the encoding at t long positions.
    The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the
    encoder `C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from
    native words to long words, are linear over E; the encoder sends only the zero message with zero
    randomness to zero; and, for every long position x, any two native words that agree at the
    native positions `C.src x` have the same long symbol at x. Here they are a conclusion.
  `Spec.gl_code_mono`: smaller d, smaller t.
  `Spec.gl_code_atPos`: the same code read at other long positions, each old position m > 0 times:
    `IsGl` with m · d.
  `GlC C d t`, `Spec.glC_code`, `Spec.glC_mono`, `Spec.glC_atPos`: the closure of `IsGl` under
    interleaving (`C.il R`), putting two codes side by side (`C₁.pair C₂`), and complexes
    (`LdCode.fam C`: the code of a group; there t = 0), with the same five properties. A second kind
    of leaf of the closure (a constructor without a `GlC` premise: `base`, `copy`): families of
    copied plain Reed-Solomon codes (the constructor `copy`; `IsGlCp`, with the same five
    properties: Cb/Gl/GlCopy.lean, Cb/Gl/GlCopyProofs.lean): a short codeword written out c times as
    one long native word.
  `Spec.gl_code_list`: an oracle message with such a code (`GlC`) and twice its radius below d:
    lists of at most one message; "evades", whatever the sample map.
  `Spec.gl_code_one`: the predicate is not empty: one code read as it stands (d = 2^a - k, t = r).

Limits: this file says nothing on lengths above 2^32, and nothing on oracles with symbols in the
small field. It states no inequality between radii and distances but as a premise (`gl_code_list`:
2 e < d): they stay with the caller.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlCodesLd
import Cb.Gl.GlCopyProofs
import Cb.Ld.LdSwitch
import Cb.Ld.LdWfThird
import Cb.Ld.LdZkPair
import Cb.Ld.LdSumZkRows
import Cb.Ld.LdRelProofsCode
import Cb.Obj.LdObjectToyKit
import Cb.Gen.CodeProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

/-- C is a family of plain Reed-Solomon codes over the prime 2^64 - 2^32 + 1, with rows, read
evenly. -/
def IsGl {P : Type} [Fintype P] (C : LdCode E P) (d t : ℕ) : Prop :=
  ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (a k msg r : A → ℕ)
      (pos : ∀ i, P → Fin (2 ^ a i)) (mult : A → ℕ) (R : A → Type)
      (_ : ∀ i, Fintype (R i)) (_ : ∀ i, DecidableEq (R i)),
    C = (⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R ∧
    (∀ i, a i ≤ 32) ∧
    (∀ i, k i < 2 ^ a i) ∧
    (∀ i, msg i + r i ≤ k i + 1) ∧
    (⟨P, pos, mult⟩ : Reading (grp a k msg r)).Even ∧
    (∀ i, d ≤ mult i * (2 ^ a i - k i)) ∧
    ∀ i, t ≤ r i

/-- The codes built from such families, and from families of copied codes, by interleaving, by
putting two side by side, and as complexes: the codes of the joints of a tower (a fold's input and
output, a mask oracle, the new code of a switch) are of this kind, and are no families themselves.
-/
inductive GlC {P : Type} [Fintype P] : LdCode E P → ℕ → ℕ → Prop
  | base {C : LdCode E P} {d t : ℕ} : IsGl C d t → GlC C d t
  | copy {C : LdCode E P} {d t : ℕ} : IsGlCp C d t → GlC C d t
  | il {C : LdCode E P} {d t : ℕ} (R : Type) [Fintype R] [DecidableEq R] :
      GlC C d t → GlC (C.il R) d t
  | pair {C₁ C₂ : LdCode E P} {d t : ℕ} : GlC C₁ d t → GlC C₂ d t → GlC (C₁.pair C₂) d t
  | fam {A : Type} [Fintype A] [DecidableEq A] {C : A → LdCode E P} {d : ℕ} :
      (∀ a, GlC (C a) d 0) → GlC (LdCode.fam C) d 0

namespace Spec

/-- What the blocks ask of a code. -/
def gl_code : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t : ℕ),
    IsGl C d t → C.Laws ∧ C.Transparent ∧ C.Reads ∧ C.Dist d ∧ C.Zk t

def gl_code_mono : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t d' t' : ℕ),
    IsGl C d t → d' ≤ d → t' ≤ t → IsGl C d' t'

/-- Read at other long positions. -/
def gl_code_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t : ℕ) (pos' : P' → P) (m : ℕ),
    IsGl C d t → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) → IsGl (C.atPos pos') (m * d) t

/-- The same for the closure. -/
def glC_code : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t : ℕ),
    GlC C d t → C.Laws ∧ C.Transparent ∧ C.Reads ∧ C.Dist d ∧ C.Zk t

def glC_mono : Prop :=
  ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t d' t' : ℕ),
    GlC C d t → d' ≤ d → t' ≤ t → GlC C d' t'

def glC_atPos : Prop :=
  ∀ (P P' : Type) [Fintype P] [Fintype P'] (C : LdCode E P) (d t : ℕ) (pos' : P' → P) (m : ℕ),
    GlC C d t → 0 < m → (∀ y, cnt (fun x => pos' x = y) = m) → GlC (C.atPos pos') (m * d) t

def gl_code_list : Prop :=
  ∀ (o : OMsg E) (d t : ℕ), GlC o.C d t → 2 * o.e < d → o.ListLE 1 ∧ o.Evades

/-- One code, read as it stands. -/
def gl_code_one : Prop :=
  ∀ (a k msg r : ℕ) (R : Type) [Fintype R] [DecidableEq R], a ≤ 32 → k < 2 ^ a → msg + r ≤ k + 1 →
    IsGl ((Reading.one (rs a k msg r 0 0)).ld E fun _ => R) (2 ^ a - k) r

/-- Codes of lengths that divide 2^b, read by repetition. -/
def gl_code_rep : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (a k msg r : A → ℕ) (b : ℕ) (h : ∀ i, a i ≤ b)
      (R : A → Type) [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)] (d t : ℕ),
    (∀ i, a i ≤ 32) → (∀ i, k i < 2 ^ a i) → (∀ i, msg i + r i ≤ k i + 1) →
    (∀ i, d ≤ 2 ^ b / 2 ^ a i * (2 ^ a i - k i)) → (∀ i, t ≤ r i) →
    IsGl ((Reading.rep (grp a k msg r) (2 ^ b) fun i => pow_dvd_pow 2 (h i)).ld E R) d t

end Spec

theorem gl_code : Spec.gl_code := by
  rintro P _ C d t ⟨A, _, _, a, k, msg, r, pos, mult, R, _, _, rfl, ha, hk, hp, hE, hd, ht⟩
  have h := gl_ld A a k msg r ha hk hp (⟨P, pos, mult⟩ : Reading (grp a k msg r)) R
  exact ⟨h.1, h.2.1, h.1.loc, h.2.2.2 hE d hd, h.2.2.1 t ht⟩

theorem gl_code_mono : Spec.gl_code_mono := by
  rintro P _ C d t d' t'
    ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk, hp, hE, hd, ht⟩ h1 h2
  exact ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk, hp, hE,
    fun i => le_trans h1 (hd i), fun i => le_trans h2 (ht i)⟩

theorem gl_code_atPos : Spec.gl_code_atPos := by
  rintro P P' _ _ C d t pos' m
    ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk, hp, hE, hd, ht⟩ hm hpos
  refine ⟨A, iA, dA, a, k, msg, r, fun i x => pos i (pos' x), fun i => m * mult i, R, fR, dR, rfl,
    ha, hk, hp, fun i => ⟨Nat.mul_pos hm (hE i).1, fun y => ?_⟩, fun i => ?_, ht⟩
  · have e := CodeRep.cnt_comp_even pos' m hpos fun z => pos i z = y
    exact e.trans (congrArg (m * ·) ((hE i).2 y))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left m (hd i)

/-- read at no long position (t = 0), every encoding is zero knowledge: `C.Zk 0` for every code C -/
theorem zk_zero {P : Type} (C : LdCode E P) : C.Zk 0 :=
  (hides_iff_equiv _ C.Nn (C.budT 0)).2 fun S hS _ _ => ⟨Equiv.refl _, fun _ p hp => by
    obtain ⟨X, hX, hSX⟩ := hS
    have hX0 : X = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hX)
    have h := hSX hp
    rw [hX0] at h
    simp at h⟩

theorem glC_code : Spec.glC_code := by
  intro P _ C d t h
  induction h with
  | base h => exact gl_code P _ _ _ h
  | copy h => exact glCp_code P _ _ _ h
  | il R _ ih =>
      have hl := ld_laws_il E P _ R ih.1
      exact ⟨hl, ld_transp_il E P _ R ih.2.1, hl.loc,
        ld_dist_il E P _ R _ ih.2.2.2.1, ld_zk_il E P _ R _ ih.2.2.2.2⟩
  | pair _ _ ih₁ ih₂ =>
      have hl := ld_laws_pair E P _ _ ih₁.1 ih₂.1
      exact ⟨hl,
        ld_transp_pair E P _ _ ih₁.2.1 ih₂.2.1,
        hl.loc,
        ld_dist_pair E P _ _ _ ih₁.2.2.2.1 ih₂.2.2.2.1,
        ld_zk_pair E P _ _ _ ih₁.2.2.2.2 ih₂.2.2.2.2⟩
  | fam _ ih =>
      have hl := ld_laws_fam E P _ _ fun a => (ih a).1
      exact ⟨hl, ld_transp_fam _ fun a => (ih a).2.1, hl.loc,
        ld_dist_fam _ _ fun a => (ih a).2.2.2.1, zk_zero _⟩

theorem glC_mono : Spec.glC_mono := by
  intro P _ C d t d' t' h h1 h2
  induction h with
  | base h => exact .base (gl_code_mono P _ _ _ d' t' h h1 h2)
  | copy h => exact .copy (glCp_mono P _ _ _ d' t' h h1 h2)
  | il R _ ih => exact .il R (ih h1 h2)
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ h1 h2) (ih₂ h1 h2)
  | fam _ ih =>
      obtain rfl : t' = 0 := Nat.le_zero.1 h2
      exact .fam fun a => ih a h1 le_rfl

theorem glC_atPos : Spec.glC_atPos := by
  intro P P' _ _ C d t pos' m h hm hpos
  induction h with
  | base h => exact .base (gl_code_atPos P P' _ _ _ pos' m h hm hpos)
  | copy h => exact .copy (glCp_atPos P P' _ _ _ pos' m h hm hpos)
  | il R _ ih => exact GlC.il R ih
  | @pair C₁ C₂ _ _ _ _ ih₁ ih₂ =>
      have e : (C₁.pair C₂).atPos pos' = (C₁.atPos pos').pair (C₂.atPos pos') := by
        show LdCode.mk _ _ _ _ _ _ _ _ = LdCode.mk _ _ _ _ _ _ _ _
        congr 1
        all_goals
          funext f x α
          cases α <;> rfl
      rw [e]
      exact GlC.pair ih₁ ih₂
  | fam _ ih => exact GlC.fam ih

theorem gl_code_list : Spec.gl_code_list := fun o d t h h2 =>
  have g := glC_code o.P o.C d t h
  have hl := ldWfThird_list o d g.1 g.2.2.2.1 h2
  ⟨hl, ldWfThird_evades o hl⟩

theorem gl_code_one : Spec.gl_code_one := fun a k msg r R fR dR ha hk hp =>
  ⟨Unit, inferInstance, inferInstance, fun _ => a, fun _ => k, fun _ => msg, fun _ => r,
    fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => ha, fun _ => hk,
    fun _ => hp, one_even F (rs a k msg r 0 0), fun _ => by rw [Nat.one_mul], fun _ => le_rfl⟩

theorem gl_code_rep : Spec.gl_code_rep := fun A iA dA a k msg r b h R fR dR _ _ ha hk hp hd ht =>
  ⟨A, iA, dA, a, k, msg, r, (Reading.rep (grp a k msg r) (2 ^ b) fun i => pow_dvd_pow 2 (h i)).pos,
    fun i => 2 ^ b / 2 ^ a i, R, fR, dR, rfl, ha, hk, hp, gl_rep_even A a k msg r b h, hd, ht⟩

end Cb.Gl
