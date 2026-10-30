-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle.lean: circle codes at the interface of layers 2 and 3.

The interface is Code/Iface.lean. Its `Enc` is a code with encoder: a generator matrix with the
numbers that go with it. Its `Enc.Props` is the record of properties that layer 2 assumes of such a
code; (P1), (P2) and (P3) are three of its fields. This file defines the circle code as an `Enc` and
proves `Enc.Props` of it, under the conditions that each theorem names.

A write-up of ours that is not in this repository (lean/CREDITS.md): Definition I.12, Corollary I.15
((P1)), Theorem I.18 ((P2)) and Theorem I.19 ((P3)), stated for the structure Code.Enc of
Code/Iface.lean.

The circle code `Circle.code z k msg r e mca` is defined at any points z of the circle over any
field F with 2 ≠ 0. Under hypotheses (see `props`) its distance is at least n - 2⌊k/2⌋ and it hides
`hidden r` positions (r for odd, r - 1 for even r). `props` has the count for mutual correlated
agreement as a hypothesis; `props_third` (3e < d, at most e + 1 bad values) and `props_half`
(2e < d, at most n bad values) have no hypothesis on the code but the conditions on the field, the
points and the numbers that the docstring of `props` lists.

How the encoder of Definition I.1 is expressed. The interface puts the r uniform coordinates right
after the message. That write-up's encoder has ℓ ≤ i0 and zeros at the indices ℓ, ..., i0 - 1. Here
msg stands for i0: a message of ℓ symbols is used with zeros up to i0. All statements hold for every
vector of msg symbols, so also for these. (Alignment) reads: a power of two 2^s ≥ r divides msg.

The mathematics is in Code/Circle/Poly.lean, Code/Circle/Basis.lean, Code/Circle/GRS.lean,
Code/Circle/MCA.lean and Code/Circle/Domain.lean, and in Code/Third.lean and Code/Facts.lean.

Terms: lean/GLOSSARY.md.
-/
import Code.Iface
import Code.Facts
import Code.Third
import Code.Circle.GRS
import Code.Circle.MCA
import Code.Circle.Domain

set_option autoImplicit false

namespace Code.Circle

open Prob Function

/-! ## Any field, any points -/

section Interface

variable {F : Type} [Field F] {n : ℕ}

/-- The circle code as a code with encoder. The points are z, the dimension is k; the message has
msg symbols and is followed by r uniform coordinates. The proximity parameter e and the count mca
for mutual correlated agreement are parameters. -/
def code (z : Fin n → Circ F) (k msg r e mca : ℕ) : Enc F where
  n := n
  k := k
  msg := msg
  r := r
  G := Matrix.of fun I i => bas (i : ℕ) (z I)
  d := n - 2 * (k / 2)
  e := e
  b := hidden r
  mca := mca

variable (z : Fin n → Circ F) (k msg r e mca : ℕ)

/-- The matrix of the interface acts as the generator of Code/Circle/GRS.lean (`gen`). -/
theorem code_mulVec (v : Fin k → F) (I : Fin n) :
    (code z k msg r e mca).G.mulVec v I = gen z k v I := by
  simp only [code, Matrix.mulVec, dotProduct, Matrix.of_apply, gen_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The code over E is the circle code over E at the same points. So Theorem I.14
(`gen_eq_scaled_rs`), under that theorem's hypotheses, applies to it. -/
theorem code_GE (E : Type) [Field E] [Algebra F E] :
    (code z k msg r e mca).GE E =
      (code (fun I => Circ.map (algebraMap F E) (z I)) k msg r e mca).G := by
  ext I i
  simp [Enc.GE, code, bas_map]

theorem code_GE_mulVec (E : Type) [Field E] [Algebra F E] (v : Fin k → E) (I : Fin n) :
    ((code z k msg r e mca).GE E).mulVec v I =
      gen (fun I => Circ.map (algebraMap F E) (z I)) k v I := by
  rw [code_GE]
  exact code_mulVec (fun I => Circ.map (algebraMap F E) (z I)) k msg r e mca v I

/-- If msg + r ≤ k, the share of the randomness is that of Theorem I.19, with i0 = msg (`genShift`,
Code/Circle/GRS.lean). -/
theorem code_share (hp : msg + r ≤ k) (ρ : Fin r → F) (I : Fin n) :
    (code z k msg r e mca).share ρ I = genShift z msg r ρ I := by
  rw [Enc.share_apply]
  have h := (code z k msg r e mca).sum_mul_fm_rand hp (fun i => (code z k msg r e mca).G I i) ρ
  refine Eq.trans h ?_
  rw [genShift_apply]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

variable {z k msg r e mca}

/-- (P1) for the code of the interface (Corollary I.15). If 2 ≠ 0 in F, the n points are distinct
points of the circle other than (-1, 0), and 2⌊k/2⌋ < n, then the image of a non-zero vector has at
least n - 2⌊k/2⌋ symbols that are not 0. -/
theorem code_dist (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) (hkn : 2 * (k / 2) < n)
    (v : Fin k → F) (hv : v ≠ 0) :
    n - 2 * (k / 2) ≤ cnt (fun I => (code z k msg r e mca).G.mulVec v I ≠ 0) := by
  have h := le_weight h2 hz (k := k) (by rw [Nat.card_fin]; exact hkn) hv
  rw [Nat.card_fin] at h
  refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)))
  rw [code_mulVec]

/-- The linear algebra behind (P3) for the code of the interface (Theorem I.19). -/
theorem code_ontoUpTo (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) (hp : msg + r ≤ k) {s : ℕ}
    (hd : 2 ^ s ∣ msg) (hr : r ≤ 2 ^ s) (h0 : ∀ I, bas msg (z I) ≠ 0) :
    OntoUpTo (code z k msg r e mca).share (hidden r) := by
  have e1 : (code z k msg r e mca).share = genShift z msg r :=
    LinearMap.ext fun ρ => funext fun I => code_share z k msg r e mca hp ρ I
  rw [e1]
  exact ontoUpTo_genShift h2 hz hd hr h0

variable [Fintype F] {E : Type} [Field E] [Finite E] [Algebra F E]

/-- Circle codes at the interface, with (P2) as a hypothesis. Let F be finite with 2 ≠ 0, and let E
be a finite field that is an algebra over F; let the n points be distinct points of the circle other
than (-1, 0); let msg + r ≤ k and 2⌊k/2⌋ < n; let a power of two 2^s ≥ r divide msg, and let bas_msg
have no zero at the points; let 2e < n - 2⌊k/2⌋. If at most mca values of θ are bad for mutual
correlated agreement at e positions, the code has all the properties that layer 2 asks for
(`Enc.Props`). -/
theorem props (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) (hp : msg + r ≤ k) (hkn : 2 * (k / 2) < n)
    {s : ℕ} (hd : 2 ^ s ∣ msg) (hr : r ≤ 2 ^ s) (h0 : ∀ I, bas msg (z I) ≠ 0)
    (he : 2 * e < n - 2 * (k / 2)) (hmca : (code z k msg r e mca).MCA E e mca) :
    (code z k msg r e mca).Props E where
  place := hp
  dist := code_dist h2 hz hkn
  unique := he
  mca := hmca
  hides :=
    ((code z k msg r e mca).hides_iff_ontoUpTo (hidden r)).2 (code_ontoUpTo h2 hz hp hd hr h0)

/-- Circle codes at the interface, without hypotheses on the code but the conditions on the field,
the points and the numbers that the docstring of `props` lists, in the range 3e < n - 2⌊k/2⌋, where
at most e + 1 values of θ are bad. -/
theorem props_third (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) (hp : msg + r ≤ k)
    (hkn : 2 * (k / 2) < n) {s : ℕ} (hd : 2 ^ s ∣ msg) (hr : r ≤ 2 ^ s)
    (h0 : ∀ I, bas msg (z I) ≠ 0) (he : 3 * e < n - 2 * (k / 2)) :
    (code z k msg r e (e + 1)).Props E :=
  props h2 hz hp hkn hd hr h0 (by omega)
    ((code z k msg r e (e + 1)).mca_third (code_dist h2 hz hkn) he)

omit [Fintype F] in
/-- Theorem I.18 at the interface. If 2 ≠ 0 in F, the n points are distinct points of the circle
other than (-1, 0), and 2e' < n - 2⌊k/2⌋, at most n values of θ are bad at the radius e', for any
number of interleaved rows over E. -/
theorem mca_half (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) {e' : ℕ} (he : 2 * e' < n - 2 * (k / 2)) :
    (code z k msg r e mca).MCA E e' n := by
  have h2E : (2 : E) ≠ 0 := by
    intro h
    refine h2 ((algebraMap F E).injective ?_)
    rw [map_ofNat, map_zero, h]
  have h := mca_range_gen h2E (hz.map (algebraMap F E)) (k := k)
    (e := e') (by rw [Fintype.card_fin]; exact he)
  rw [Fintype.card_fin] at h
  have hc : (code z k msg r e mca).codeE E =
      LinearMap.range (gen (fun I => Circ.map (algebraMap F E) (z I)) k) := by
    unfold Enc.codeE
    congr 1
    exact LinearMap.ext fun v => funext fun I => code_GE_mulVec z k msg r e mca E v I
  rw [Enc.mca_iff, hc]
  exact h

/-- Circle codes at the interface, without hypotheses on the code but the conditions on the field,
the points and the numbers that the docstring of `props` lists, in the whole range
2e < n - 2⌊k/2⌋, with at most n bad values of θ. -/
theorem props_half (h2 : (2 : F) ≠ 0) (hz : CirclePoints z) (hp : msg + r ≤ k)
    (hkn : 2 * (k / 2) < n) {s : ℕ} (hd : 2 ^ s ∣ msg) (hr : r ≤ 2 ^ s)
    (h0 : ∀ I, bas msg (z I) ≠ 0) (he : 2 * e < n - 2 * (k / 2)) : (code z k msg r e n).Props E :=
  props h2 hz hp hkn hd hr h0 he (mca_half h2 hz he)

end Interface

end Code.Circle
