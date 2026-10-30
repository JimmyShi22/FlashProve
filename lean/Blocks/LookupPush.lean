-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupPush.lean: a lookup argument between steps 5 and 6, carried to a larger implicit part.

If a vector is sent during a lookup argument (Blocks/LookupBlock.lean), the implicit part of the
statement grows, and with it the set of entries that forms read. The explicit part `LkX` of the
argument's statement holds forms; each is carried along the map σ of entries (Blocks/Form.lean:
`Form.push`) and, under `Lk.Up`, has the value that it had (`Lk.Up.V`).
 * `LkX.push` σ x: all its forms carried along σ.
 * `Lk.up` L σ proj': the same lookup argument over the larger implicit part: same parameters and
   pads; the entries are read by proj', a pad is at σ of its old entry.
 * `Lk.grp_up`, ..: it uses the same pads as L.
 * `Lk.Up`: what links the two: proj' reads the old entries as before (through a map gy of implicit
   parts), and the true vectors (keys, bits) are the old ones.
 * Under `Lk.Up`: `Lk.r8_of_up`: the relation for soundness after step 5 for the carried explicit
   part implies that for the old one; `Lk.h8_up`: that for the honest run carries over.
Only this point of the argument is treated: there the range reduction by calls
(Blocks/RngCalls.lean) sends its vector RA.

Notation: E, Y, Pd, N: types, the arguments of `Lk`: E the field; Y the implicit part; Pd the set of
places of pads; N the set of entries (Blocks/LookupBlock.lean); `T`, `T'`: `Lk.Vecs E Y`,
`Lk.Vecs E Y'`: the true vectors of a lookup argument: the keys and the multiplicity bits, as
functions of the implicit part (Blocks/LookupBlock.lean); Y', N': the implicit part and the set of
entries of the carried argument `Lk.up` L σ proj'.
-/
import Blocks.LookupStage
import Blocks.HLed

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop

/-- The explicit part of a lookup argument's statement with all its forms carried along a map of
entries. -/
def LkX.push {N N' E : Type} [Fintype N] [DecidableEq N'] [CommRing E] (σ : N → N') (x : LkX N E) :
    LkX N' E where
  led := x.led.push σ
  al := x.al
  Zf := fun θ => Form.push σ (x.Zf θ)
  Yf := fun θ π => Form.push σ (x.Yf θ π)
  C := Form.push σ x.C
  pt := x.pt
  Cend := Form.push σ x.Cend
  z := x.z
  v4 := Form.push σ x.v4
  p4 := x.p4
  v5 := Form.push σ x.v5
  p5 := x.p5
  p6 := x.p6
  Uf := fun π θ => Form.push σ (x.Uf π θ)
  Vf := fun π θ => Form.push σ (x.Vf π θ)
  pr := x.pr
  cx := x.cx

namespace Lk

variable {E Y Pd N Y' N' : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]
  [Fintype N'] [DecidableEq N'] (L : Lk E Y Pd N) (T : Lk.Vecs E Y)

/-- The same lookup argument over a larger implicit part. -/
@[reducible] def up (σ : N → N') (proj' : Y' → N' → E) : Lk E Y' Pd N' :=
  { L with proj := proj', place := fun p => σ (L.place p) }

/-- The pads of the rounds of a sumcheck depend only on its map `idx` to pads. -/
theorem _root_.Blocks.SC.padsOf_congr {Y₁ Y₂ P Ξ₁ Ξ₂ ι : Type} {S : SC E Y₁ P Ξ₁ ι}
    {S' : SC E Y₂ P Ξ₂ ι} (h : ∀ i, Set.range (S.idx i) = Set.range (S'.idx i)) :
    ∀ l : List ι, S.padsOf l = S'.padsOf l
  | [] => rfl
  | i :: l => by
      show Set.range (S.idx i) ∪ S.padsOf l = Set.range (S'.idx i) ∪ S'.padsOf l
      rw [h i, SC.padsOf_congr h l]

/-- `Lk.up` uses the same pads as L. -/
theorem grp_up (σ : N → N') (proj' : Y' → N' → E) : ∀ g, (L.up σ proj').grp g = L.grp g
  | .zy =>
    congrArg Set.range
      (funext fun k => by rcases k with _ | ⟨_, _⟩ <;> rfl : (L.up σ proj').idxZY = L.idxZY)
  | .k l =>
    congrArg (· ∪ Set.range (L.plK l).pv)
      (SC.padsOf_congr (S := ((L.up σ proj').plK l).sc) (S' := (L.plK l).sc) (fun _ => rfl) _)
  | .t l =>
    congrArg (· ∪ Set.range (L.plT l).pv)
      (SC.padsOf_congr (S := ((L.up σ proj').plT l).sc) (S' := (L.plT l).sc) (fun _ => rfl) _)
  | .lf =>
    congrArg (· ∪ Set.range L.plL.pv)
      (SC.padsOf_congr (S := (L.up σ proj').plL.sc) (S' := L.plL.sc) (fun _ => rfl) _)
  | .bt =>
    congrArg (· ∪ Set.range L.plB.pv)
      (SC.padsOf_congr (S := (L.up σ proj').plB.sc) (S' := L.plB.sc) (fun _ => rfl) _)
  | .uv =>
    congrArg Set.range
      (funext fun k => by rcases k with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl : (L.up σ proj').idxUV = L.idxUV)
  | .rt => SC.padsOf_congr (S := (L.up σ proj').scR) (S' := L.scR) (fun _ => rfl) _

theorem allPads_up (σ : N → N') (proj' : Y' → N' → E) : (L.up σ proj').allPads = L.allPads :=
  Set.ext fun p =>
    ⟨fun ⟨g, hg, hp⟩ => ⟨g, hg, by rwa [L.grp_up] at hp⟩,
      fun ⟨g, hg, hp⟩ => ⟨g, hg, by rwa [L.grp_up]⟩⟩

theorem UG_up (σ : N → N') (proj' : Y' → N' → E) (Q : ℕ → Prop) : (L.up σ proj').UG Q = L.UG Q :=
  Set.ext fun p =>
    ⟨fun ⟨g, hQ, hg, hp⟩ => ⟨g, hQ, hg, by rwa [L.grp_up] at hp⟩,
      fun ⟨g, hQ, hg, hp⟩ => ⟨g, hQ, hg, by rwa [L.grp_up]⟩⟩

theorem rt_up (σ : N → N') (proj' : Y' → N' → E) (h : L.scR.PlacesOnceOn (lkVars L.par.σ)) :
    (L.up σ proj').scR.PlacesOnceOn (lkVars L.par.σ) := h

variable {L T} {σ : N → N'} {proj' : Y' → N' → E} {T' : Lk.Vecs E Y'} {gy : Y' → Y}

/-- The conditions that link the two arguments. -/
structure Up (L : Lk E Y Pd N) (T : Lk.Vecs E Y) (σ : N → N') (proj' : Y' → N' → E)
    (T' : Lk.Vecs E Y') (gy : Y' → Y) : Prop where
  proj : ∀ y' n, proj' y' (σ n) = L.proj (gy y') n
  key : ∀ y', T'.key y' = T.key (gy y')
  B : ∀ y', T'.B y' = T.B (gy y')

theorem Up.projF (h : Up L T σ proj' T' gy) (y' : Y') :
    (fun n => proj' y' (σ n)) = L.proj (gy y') :=
  funext (h.proj y')

/-- Under `Up`, a carried form has the value that the form had. -/
theorem Up.V (h : Up L T σ proj' T' gy) (y' : Y') (f : Form N E) :
    (L.up σ proj').V y' (Form.push σ f) = L.V (gy y') f := by
  show Form.val (proj' y') (Form.push σ f) = Form.val (L.proj (gy y')) f
  rw [Form.val_push, h.projF]

theorem Up.led (h : Up L T σ proj' T' gy) (y' : Y') (led : Ledger N E) :
    (led.push σ).True (proj' y') ↔ led.True (L.proj (gy y')) := by
  rw [Ledger.true_push, h.projF]

/-- Soundness, under `Up`: the relation after step 5 for the carried explicit part implies that for
the old one. -/
theorem r8_of_up (h : Up L T σ proj' T' gy) {x : LkX N E} {y' : Y'}
    (hR : (L.up σ proj').R8 T' (x.push σ) y') : L.R8 T x (gy y') := by
  obtain ⟨hled, hids, hend, h4, h5, h6⟩ := hR
  refine ⟨(h.led y' x.led).1 hled, ?_, fun hz => ?_, ?_, ?_, ?_⟩
  · have e : L.par.Ident x.al (fun θ => (L.up σ proj').V y' (Form.push σ (x.Zf θ)))
        (fun θ π => (L.up σ proj').V y' (Form.push σ (x.Yf θ π))) := hids
    simp only [h.V] at e
    exact e
  · have e : (L.up σ proj').V y' (Form.push σ x.Cend) =
        ext (L.par.D + L.par.σ) (L.par.leafK (T'.key y') x.al) x.z := hend hz
    rw [h.V, h.key] at e
    exact e
  · have e : (L.up σ proj').V y' (Form.push σ x.v4) = ext L.par.gT (L.par.vB (T'.B y')) x.p4 := h4
    rw [h.V, h.B] at e
    exact e
  · have e : (L.up σ proj').V y' (Form.push σ x.v5) = ext L.par.gT (L.par.vB (T'.B y')) x.p5 := h5
    rw [h.V, h.B] at e
    exact e
  · have e : ext L.par.σ (L.par.dDeg (T'.B y')) x.p6 = 0 := h6
    rw [h.B] at e
    exact e

/-- Honest run, under `Up`: the relation after step 5 carries over. -/
theorem h8_up (h : Up L T σ proj' T' gy) {U : Set Pd} {a : LkA E} {π : Pd → E} {x : LkX N E}
    {y' : Y'} (hH : L.H8 T U a π x (gy y')) :
    (L.up σ proj').H8 T' U a π (x.push σ) y' := by
  obtain ⟨⟨⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hp⟩, ⟨tz1, tz2⟩, ⟨e1, e2⟩, h4, h5⟩, h6⟩ := hH
  refine ⟨⟨⟨⟨k1.trans (h.key y').symm, k2.trans (h.B y').symm,
          fun p hp' => (h.proj y' _).trans (k3 p hp'), (Ledger.wf_push σ x.led).trans k4,
          (h.led y' x.led).2 k5, ?_, ?_⟩,
        hp⟩,
      ⟨fun θ hθ => ?_, fun θ hθ π' hπ' => ?_⟩,
      ⟨e1, ?_⟩, ?_, ?_⟩,
    ?_⟩
  · refine HLed.Of.push σ ?_
    rw [h.projF]
    exact k6
  · show L.par.Bits (T'.B y') ∧
      L.par.DegE (T'.B y') ∧
      ∀ al, L.par.Ident al (L.par.Zt (T'.key y') al) (L.par.Yt (T'.B y') al)
    rw [h.B, h.key]
    exact k7
  · show (L.up σ proj').V y' (Form.push σ (x.Zf θ)) = L.par.Zt (T'.key y') x.al θ
    rw [h.V, h.key]
    exact tz1 θ hθ
  · show (L.up σ proj').V y' (Form.push σ (x.Yf θ π')) = L.par.Yt (T'.B y') x.al θ π'
    rw [h.V, h.B]
    exact tz2 θ hθ π' hπ'
  · show (L.up σ proj').V y' (Form.push σ x.Cend) =
      ext (L.par.D + L.par.σ) (L.par.leafK (T'.key y') x.al) x.z
    rw [h.V, h.key]
    exact e2
  · show (L.up σ proj').V y' (Form.push σ x.v4) = ext L.par.gT (L.par.vB (T'.B y')) x.p4
    rw [h.V, h.B]
    exact h4
  · show (L.up σ proj').V y' (Form.push σ x.v5) = ext L.par.gT (L.par.vB (T'.B y')) x.p5
    rw [h.V, h.B]
    exact h5
  · show ext L.par.σ (L.par.dDeg (T'.B y')) x.p6 = 0
    rw [h.B]
    exact h6

end Lk

end Blocks
