-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlCodes.lean: plain Reed-Solomon codes over the prime p = 2^64 - 2^32 + 1, evaluated on the
points of a multiplicative subgroup of order 2^a: their distance, list sizes and mutual correlated
agreement.

Definitions, statements (in `Cb.Gl.Spec`) and proofs. No length, no rate, no radius is fixed: a, k,
msg, r, e are parameters.

Main names:
  `rs a k msg r e mca`: a message of msg symbols, then r uniform coordinates, are coefficients of a
    polynomial of degree at most k. For a ≤ 32, k < 2^a, msg + r ≤ k + 1: distance at least 2^a - k;
    the encoder hides r positions. Words and tables are read over E = F[x] / (x^3 - 2), F the
    integers modulo p (Cb/Gl/GlField.lean).
  All statements are for a ≤ 32, the first four also for k < 2^a.
  `Spec.gl_rs_dist`, `Spec.gl_rs_core`: the distance; for msg + r ≤ k + 1 the record `Code.Enc.Core`
    (Cb/Gen/CodeList.lean): place, distance, positive distance, any r positions of an encoding are
    uniform.
  `Spec.gl_rs_third`: nothing assumed: at every radius e with 3 e below the distance: at most one
    codeword in the list, at most e + 1 exceptional values in mutual correlated agreement.
  `Spec.gl_rs_list`: nothing assumed: at every radius below the Johnson radius the list has at most
    `listMax` members (Cb/Gen/JohnsonList.lean).
  The last two are for 0 < k, the second of them also for msg + r ≤ k + 1:
  **Spec.gl_rs_prox, gl_rs_listProps** UNDER THE HYPOTHESIS BCHKS46, BY NAME
  (Cb/Gen/CodeListRS.lean: stated in its source with an outline of a proof; taken as a named
  hypothesis, not an axiom): agreement at every radius e > 0 with 2^a k < (2^a - e)^2, with that
  statement's count; the record Code.Enc.ListProps at such a radius
    (The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)

Notation: `e`, `mca` in `rs a k msg r e mca`: fields of `Code.Enc` (Code/Iface.lean): proximity
parameter in positions; count of bad θ.

Limits: this file says nothing on lengths above 2^32 (but for `rs_d`, which has no bound on a), on
which lengths, rates, radii an instance takes, or on families of codes read at common positions
(Cb/Gl/GlCodesLd.lean). It does not say whether BCHKS46 as stated there is what its source proves:
the head of Cb/Gen/CodeListRS.lean. Nothing is said between the Johnson radius and capacity.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlField
import Cb.Gen.CodeListRows

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

/-- The plain Reed-Solomon code of length 2^a and dimension k + 1 on the points `pts a`: for a ≤ 32
the subgroup of order 2^a. -/
@[reducible] def rs (a k msg r e mca : ℕ) : Code.Enc F := Code.RS.code (pts a) (k + 1) msg r e mca

namespace Spec

def gl_rs_dist : Prop :=
  ∀ a k msg r e mca : ℕ, a ≤ 32 → k < 2 ^ a → HasDist (rs a k msg r e mca).G (2 ^ a - k)

def gl_rs_core : Prop :=
  ∀ a k msg r e mca : ℕ, a ≤ 32 → k < 2 ^ a → msg + r ≤ k + 1 → (rs a k msg r e mca).Core

/-- Up to a third of the distance: nothing assumed beyond the hypotheses of the statement and
whatever the arguments hold as proofs. -/
def gl_rs_third : Prop :=
  ∀ a k msg r e mca : ℕ, a ≤ 32 → k < 2 ^ a →
    (rs a k msg r e mca).Prox E (fun e' => 3 * e' < 2 ^ a - k) (fun _ _ => 1) (fun e' _ => e' + 1)

/-- The list below the Johnson radius: nothing assumed beyond the hypotheses of the statement and
whatever the arguments hold as proofs. -/
def gl_rs_list : Prop :=
  ∀ a k msg r e mca : ℕ, a ≤ 32 → k < 2 ^ a →
    ∀ e', InJohnson (2 ^ a) (2 ^ a - k) e' →
      ∀ (R : Type) [Finite R], (rs a k msg r e mca).ListAt E R e' (listMax (2 ^ a) (2 ^ a - k) e')

/-- Agreement below the Johnson radius: under the statement on codes, by name.
(not all hypotheses are named here: see the statement below) -/
def gl_rs_prox : Prop :=
  Cb.BCHKS46 →
  ∀ a k msg r e mca : ℕ, a ≤ 32 → 0 < k →
    (rs a k msg r e mca).Prox E (fun e' => 0 < e' ∧ 2 ^ a * k < (2 ^ a - e') ^ 2)
      (fun e' _ => listMax (2 ^ a) (2 ^ a - k) e') (fun e' _ => ⌊Cb.bchksBound (2 ^ a) k e'⌋₊)

def gl_rs_listProps : Prop :=
  Cb.BCHKS46 →
  ∀ a k msg r e : ℕ, a ≤ 32 → msg + r ≤ k + 1 → 0 < k → 0 < e → 2 ^ a * k < (2 ^ a - e) ^ 2 →
    (rs a k msg r e ⌊Cb.bchksBound (2 ^ a) k e⌋₊).ListProps E (listMax (2 ^ a) (2 ^ a - k) e)

end Spec

/-- Under `hk`, the distance in the data of the code is 2^a - k. -/
theorem rs_d {a k : ℕ} (msg r e mca : ℕ) (hk : k < 2 ^ a) : (rs a k msg r e mca).d = 2 ^ a - k := by
  show 2 ^ a - (k + 1) + 1 = 2 ^ a - k
  omega

theorem gl_rs_dist : Spec.gl_rs_dist := by
  intro a k msg r e mca ha hk
  have h : HasDist (rs a k msg r e mca).G (2 ^ a - (k + 1) + 1) :=
    Code.RS.code_dist (gl_pts_inj a ha) hk
  have e1 : 2 ^ a - (k + 1) + 1 = 2 ^ a - k := by omega
  rwa [e1] at h

theorem rs_hasDist {a k : ℕ} (msg r e mca : ℕ) (ha : a ≤ 32) (hk : k < 2 ^ a) :
    HasDist (rs a k msg r e mca).G (rs a k msg r e mca).d :=
  Code.RS.code_dist (gl_pts_inj a ha) hk

theorem gl_rs_core : Spec.gl_rs_core := fun a k msg r e mca ha hk hp =>
  { place := hp
    dist := Code.RS.code_dist (gl_pts_inj a ha) hk
    pos := Nat.succ_pos _
    hides := ((rs a k msg r e mca).hides_iff_ontoUpTo r).2
      (Code.RS.code_ontoUpTo (gl_pts_inj a ha) (gl_pts_ne_zero a) hp) }

theorem gl_rs_third : Spec.gl_rs_third := by
  intro a k msg r e mca ha hk
  have h := prox_third F E (rs a k msg r e mca) (rs_hasDist msg r e mca ha hk)
  rwa [rs_d msg r e mca hk] at h

theorem gl_rs_list : Spec.gl_rs_list := by
  intro a k msg r e mca ha hk e' hJ R _ f
  have h := johnson_enc F E (rs a k msg r e mca) e' (rs_hasDist msg r e mca ha hk)
    (by rw [rs_d msg r e mca hk]; exact hJ) R f
  rwa [rs_d msg r e mca hk] at h

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem gl_rs_prox : Spec.gl_rs_prox := fun H a k msg r e mca ha hk =>
  rs_prox H F E (2 ^ a) k msg r e mca (pts a) (gl_pts_inj a ha) hk

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem gl_rs_listProps : Spec.gl_rs_listProps := fun H a k msg r e ha hp hk he hJ =>
  rs_listProps H F E (2 ^ a) k msg r e (pts a) (gl_pts_inj a ha) (gl_pts_ne_zero a) hp hk he hJ

end Cb.Gl
