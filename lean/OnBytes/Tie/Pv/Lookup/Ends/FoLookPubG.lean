-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubG.lean.
The one lookup of a layer sub-proof: its share of the link's public record, as a value made of the
byte-level verifier's own layout and plan.

It follows OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean (attention), whose box of entries (JA, cellJ,
maskJ) it uses.

Main names:
  `layout_lm`, `polLayout_lm`, `public_lm`: 5 ≤ y.h.lmb ≤ y.fo.kT + 5 for the layout y that
    Layer.layout, Verify.polLayout return, and for X.layers.y where Verify.publicOf returns X.
  `IxG`: what a layer sub-proof's committed messages hold, by plain names: the cells of the
    smallness test's matrices (matrix, row, column), and the mask row's slots.
  `lookPubG rdG K y hp nM nR nC St`: the record, over any base reading M₀ that is read at the names
    IxG by rdG: h := y.fo; the mask entries are the slots from hp.Fp.next on; the bits of the counts
    lie in the matrix number (Layer.matIx y).iB, of 2^lmb rows. THE KEYS K ARE AN ARGUMENT.
  `lookPubG_of`: ShapeOf and the bounds on lmb give Fo.Pub2.LookPubOK of it.
  `lookPubG_ok`: where Verify.publicOf returns X: LookPubOK at y := X.layers.y and every plan hp, at
    the calls, numbers of padding keys and cap y.cl, y.fo.pub, y.h.lidb.
Limits: K, the keys as a function of the entries, is an argument: nothing is said of it. nM, nR, nC,
the box's bounds, are free: no clause here asks that different places are different entries, and
beyond the bounds they are not. That a layer's check calls Forest.pad at y.cl, y.fo.pub, y.h.lidb is
Fo.g_look_exact (OnBytes/Tie/Pv/Lookup/Ends/FoTiedLook.lean); that the lookup's first slot in a run
is hp.Fp.next is not said here; nor that the byte-level verifier reads the bits of the counts in the
matrix (Layer.matIx y).iB: the value lays them there. No clause reads hp but through hp.Fp.next and
hp.ns, so lookPubG_ok holds of every hp, a member of X.G or not.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicShape

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model
open Fo.BatRows (bindE_ok)

/-! ### the bounds on the number of the planes' rows -/

theorem layout_lm {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : 5 ≤ y.h.lmb ∧ y.h.lmb ≤ y.fo.kT + 5 := by
  unfold Layer.layout at e
  obtain ⟨y0, _, e⟩ := bindE_ok e
  rw [layoutLook_h e]
  exact Fo.Pay.layoutLook_lm e

theorem polLayout_lm {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (e : Verify.polLayout pol = .ok (P, y)) : 5 ≤ y.h.lmb ∧ y.h.lmb ≤ y.fo.kT + 5 := by
  unfold Verify.polLayout at e
  obtain ⟨P0, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y0, hy, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact layout_lm hy

theorem public_lm {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    5 ≤ X.layers.y.h.lmb ∧ X.layers.y.h.lmb ≤ X.layers.y.fo.kT + 5 :=
  polLayout_lm (Fo.Pub.publicOf_cut pol KL layout X h).1

/-! ### the value -/

/-- The names at a layer: the cells (matrix, row, column), and the mask row's slots. -/
abbrev IxG : Type := (ℕ × ℕ × ℕ) ⊕ ℕ

/-- The lookup's share of the public record of a layer sub-proof. The keys are an argument. -/
def lookPubG {M₀ : Type} (rdG : M₀ → IxG → Cb.Gl.E) {St : Type} (y : Layer.Lay)
    (hp : Layer.HPlan2) (nM nR nC : ℕ)
    (K : St → (JA nM nR nC hp.ns → Cb.Gl.E) → ℕ → ℕ → Cb.Gl.E) : LookPub M₀ St where
  h := y.fo
  J₀ := JA nM nR nC hp.ns
  L :=
    { K := K
      bc := fun t c j => cellJ (Layer.matIx y).iB (FoNums.cellRC y.fo y.h.lmb (t, c, j)).1
        (FoNums.cellRC y.fo y.h.lmb (t, c, j)).2
      mkS := fun s => maskJ (hp.Fp.next + s) }
  rd₀ := fun b => Sum.elim (fun n => rdG b (.inl (n.1.val, n.2.1.val, n.2.2.val)))
    fun s => rdG b (.inr s.val)

theorem lookPubG_of {M₀ : Type} (rdG : M₀ → IxG → Cb.Gl.E) {St : Type} (y : Layer.Lay)
    (hp : Layer.HPlan2) (nM nR nC : ℕ)
    (K : St → (JA nM nR nC hp.ns → Cb.Gl.E) → ℕ → ℕ → Cb.Gl.E)
    (hs : ShapeOf y.cl y.fo.pub y.h.lidb y.fo) (hl : 5 ≤ y.h.lmb ∧ y.h.lmb ≤ y.fo.kT + 5) :
    LookPubOK (lookPubG rdG y hp nM nR nC K) y.cl y.fo.pub y.h.lidb y.h.lmb hp.Fp.next maskJ
      (cellJ (Layer.matIx y).iB) :=
  ⟨hs, hl.1, hl.2, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-- **At the public record's layout, for every plan.** -/
theorem lookPubG_ok {M₀ : Type} (rdG : M₀ → IxG → Cb.Gl.E) {St : Type} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (hp : Layer.HPlan2) (nM nR nC : ℕ)
    (K : St → (JA nM nR nC hp.ns → Cb.Gl.E) → ℕ → ℕ → Cb.Gl.E) :
    LookPubOK (lookPubG rdG X.layers.y hp nM nR nC K) X.layers.y.cl X.layers.y.fo.pub
      X.layers.y.h.lidb X.layers.y.h.lmb hp.Fp.next maskJ (cellJ (Layer.matIx X.layers.y).iB) :=
  lookPubG_of rdG X.layers.y hp nM nR nC K (public_shape h) (public_lm h)

end Fo.Pub2
