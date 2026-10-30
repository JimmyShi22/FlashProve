-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupRider.lean: a layer of a lookup argument's key side with a rider.

A rider (Blocks/StageBoth.lean) uses coordinates of the layer's next point as the point of a second
zero test. The layer l of the key side (`Lk.stK` l; the last one is `Lk.stLast`) ends with the point
x.pt = (ζ | ϱ̂): coordinate 0 is ζ, coordinate t + 1 is the challenge of the round that binds the
variable t. σ k says which coordinate is substituted for the variable k of the polynomial G x y of
the second test. The rider exists only in the analysis: the verifier sends and checks nothing more.
G must not depend on the running form, the point and the list of deferred claims, which the layer
changes. (The σ of `degLE_ext_comp`, `vanishes_ext` in Blocks/StageBoth.lean goes the other way,
from coordinates to variables.)

`Lk.props_stK_rider`: under its hypotheses and 2 ≠ 0 in E the layer has `Stage.Props` between the
conjunctions (`Cut.and`) of its own relations cK l, cK (l + 1) with the rider's: before it G x y is
the zero function, after it G x y is 0 at the point (x.pt (σ k))_k. Protocol, honest prover, masked
form and withheld sets are those of the layer. The error of a round whose challenge is substituted
for the variable k is the larger of the layer's error and d k; for d = 1 no error changes
(`Lk.stK_both_one`).

Notation:
 * ϱ̂, ζ: of a product layer: the end point ϱ̂ of its sumcheck, the verifier's challenge ζ (the head
   of Blocks/ProductBlock.lean).
 * σ, `d`: `Fin n → ℕ`; `G`: `LkX N E → Y → (Fin n → E) → E`: binders of `props_stK_rider`; `d`
   enters through hG : ∀ x y, `DegLE` d (G x y) (Alg/Poly.lean).
 * the running form, the point, the list of deferred claims: the fields `C`, `pt`, `led` of `LkX`
   (Blocks/LookupBlock.lean).
 * `Stage.Props` S ca cb: all properties of a stage, between the relations before and after it
   (Blocks/Stage.lean).
 * `LkPar.OrdOK`: the order of the last layer of the key side names each of its variables once
   (Blocks/LookupRel.lean); `Lk.PadsOK`: see its definition, Blocks/LookupHon.lean.
 * `Binds` κ E s: for each round of a list of rounds: nothing, or a variable, with the map that
   computes an element of E from the verifier message of the round; `selOf` σ t: the variable that
   the coordinate t is used for (Blocks/StageBoth.lean).
-/
import Blocks.LookupSplit
import Blocks.StageBoth
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks.Lk
open Iop Prob Alg

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The rounds of the layer l of the key side whose challenges the rider uses. -/
def bindsK (l : ℕ) {n : ℕ} (σ : Fin n → ℕ) : Binds (Fin n) E (L.stK l).B.shape :=
  (L.plK l).binds (selOf σ)

/-- Under the hypotheses below and 2 ≠ 0 in E, a layer with a rider has `Stage.Props`. -/
theorem props_stK_rider (ho : L.par.OrdOK) (hok : L.PadsOK) {l : ℕ} (hl : l < L.par.D) {n : ℕ}
    {σ : Fin n → ℕ} (hσ : Function.Injective σ) (hle : ∀ k, σ k ≤ l + L.par.σ) {d : Fin n → ℕ}
    {G : LkX N E → Y → (Fin n → E) → E} (hG : ∀ x y, DegLE d (G x y))
    (hinv : ∀ (x : LkX N E) C pt led, G { x with C := C, pt := pt, led := led } = G x) :
    ((L.stK l).both ((L.bindsK l σ).err d)).Props
      ((L.cK T l).and (fun x y => ∀ z, G x y z = 0) fun _ _ x y => ∀ z, G x y z = 0)
      ((L.cK T (l + 1)).and (fun x y => G x y (fun k => x.pt (σ k)) = 0) fun _ _ x y =>
        G x y (fun k => x.pt (σ k)) = 0) :=
  (L.props_stK T ho hok hl).rider_all (L.bindsK l σ) ((L.plK l).inj_binds _)
    (fun k => ((L.plK l).mem_vars_binds (ho.kOrd l) _).2 ⟨σ k, hle k, selOf_apply hσ k⟩) hG
    fun x y τ xo hxo => by
      obtain ⟨xo', hxo', rfl⟩ := Option.map_eq_some_iff.1
        (show ((L.plK l).pl.pub (gxPL x) τ.rho τ.plains).map (pxPL x) = some xo from hxo)
      have h1 : (L.bK l).imp y τ = y := (L.plK l).imp_pl y τ
      have h2 : (fun k => (pxPL x xo').pt (σ k)) =
          (L.bindsK l σ).pt τ.rho fun _ => 0 := funext fun k =>
        ((L.plK l).pt_binds (ho.kOrd l) (selOf σ) (fun _ _ _ _ _ e e' => selOf_inj e e') _ hxo'
          (hle k) (selOf_apply hσ k)).symm
      show G (pxPL x xo') ((L.bK l).imp y τ) (fun k => (pxPL x xo').pt (σ k)) = 0 ↔ _
      rw [h1, h2, show G (pxPL x xo') = G x from hinv x _ _ _]

/-- `props_stK_rider` at l = D - 1, under hD: the coordinates are those of the end point z of the
key side. -/
theorem props_stLast_rider (ho : L.par.OrdOK) (hok : L.PadsOK) (hD : 0 < L.par.D) {n : ℕ}
    {σ : Fin n → ℕ} (hσ : Function.Injective σ) (hle : ∀ k, σ k ≤ L.par.D - 1 + L.par.σ)
    {d : Fin n → ℕ} {G : LkX N E → Y → (Fin n → E) → E} (hG : ∀ x y, DegLE d (G x y))
    (hinv : ∀ (x : LkX N E) C pt led, G { x with C := C, pt := pt, led := led } = G x) :
    (L.stLast.both ((L.bindsK (L.par.D - 1) σ).err d)).Props
      ((L.cK T (L.par.D - 1)).and (fun x y => ∀ z, G x y z = 0) fun _ _ x y => ∀ z, G x y z = 0)
      ((L.cK T L.par.D).and (fun x y => G x y (fun k => x.pt (σ k)) = 0) fun _ _ x y =>
        G x y (fun k => x.pt (σ k)) = 0) := by
  have h := L.props_stK_rider T ho hok (l := L.par.D - 1) (by omega) hσ hle hG hinv
  rwa [show L.par.D - 1 + 1 = L.par.D by omega] at h

omit [NeZero (2 : E)] [Fintype Pd] [DecidableEq Pd] in
/-- For a second test of degree 1 in each variable the layer with the rider is the layer: the same
stage, the same errors. So all lemmas on the numbers of the layer apply after one rewriting. -/
theorem stK_both_one (l : ℕ) {n : ℕ} (σ : Fin n → ℕ) :
    (L.stK l).both ((L.bindsK l σ).err fun _ => 1) = L.stK l :=
  Stage.both_eq_self _
    ((L.plK l).err_binds_le _ _ 1 (fun _ _ _ => Nat.le_add_left _ _) fun _ _ => le_rfl)

end Blocks.Lk

