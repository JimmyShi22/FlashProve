-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Rows/LayerGatedPort.lean: each claim of the verifier on an end value of the two product
layers of the gated products of a layers' sub-proof is worth what the library-side claim is worth,
in every world and at all entries that four plain conditions tie to each other.

Johnson/Road/Rows/GatedClaims.lean writes these claims as lists of forms (endsL, inside gatedL).
Cb/Pv/Lay/End/GatedCl.lean lists them in the library's names: four forms cEnd (gatedCl). This file
holds one claim of the one against one form of the other, on values, after the pattern of
Johnson/Road/Rows/LayerTermsPort.lean.

Main names:
  `sumForms_value_lt`: the value of a sum of forms, from what its terms BELOW n are worth.
  `longA_read`: a block of a tensor, read from a long table: its limbs under the powers of 256.
  `end_val`: Aff.slot s + (the sum of claimsEnds) and cEnd have one value, if: the hidden value
    under the slot is what was shown less the factor times the mask entry (hslot); the verifier's
    table of weights reads as the equality weights of the library's point (hw); the tensor has two
    limbs (hnl); the entries of the reads that the form names are worth the library-side entries of
    the same names (hread).
  `endsL_port`: so, if both forms of endsL are worth 0, so are the two forms cEnd.
Limits. The four conditions are premises. The two layers' OWN claims (hd.row, hd2.row; the library's
prodU) are not spoken of here. Nothing on whether the reads are true, on soundness or on hiding.


-/
import Johnson.Road.Rows.LayerHotPort
import Johnson.Road.Rows.GatedClaims
import Cb.Pv.Lay.End.GatedCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Level tenCell)
open OnBytes.Model.Layer (Env Ten)
open Cb.Pv.Lay.End.Gated (cEnd hid)
open Blocks (Form eqN)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]
variable {ρ : Reading K} {W : World K} {v : Env}

/-- The value of a sum of forms under coefficients, from what the terms below n are worth. -/
theorem sumForms_value_lt (n : ℕ) (f : ℕ → Option (Aff × E)) (g : ℕ → K)
    (H : ∀ x, x < n → ∀ b k, f x = some (b, k) → ρ.val k * b.value ρ W = g x)
    {a : Aff} (h : Model.Layer.sumForms n f = some a) : a.value ρ W = ∑ x ∈ range n, g x := by
  have hall := foldForms_there f (List.range n) _ _ h
  rw [sumForms_value ρ W n f (fun x => ((f x).map fun t => ρ.val t.2 * t.1.value ρ W).getD 0)
    (fun x b k hb => by dsimp only; rw [hb]; rfl) h]
  refine sum_congr rfl fun x hx => ?_
  have hx' : x < n := mem_range.mp hx
  obtain ⟨t, ht⟩ := hall x (List.mem_range.mpr hx')
  rw [ht]
  exact H x hx' t.1 t.2 ht

/-- A block of a tensor with nl limbs, read from a long table. -/
theorem longA_read (hρ : Numerals ρ) {t : ℕ} {X : Ten} {i jh : ℕ} {a : Aff}
    (h : v.longA t X i jh = some a) :
    a.value ρ W =
      ∑ k ∈ range X.nl, (256 : K) ^ k * readAtW W v t (tenCell X.place k i 0 / v.y.S2 + jh) :=
  limbs_value hρ (readAtW W v t) (fun _ _ hb => U3at_read hb) h

/-- **One claim on an end value.** -/
theorem end_val (hρ : Numerals ρ) {sX t : ℕ} {X : Ten} {e : Array E}
    {rows blocks stride first : ℕ} {lamOf : ℕ → ℕ} {sh β : K} {m : J} {u : ℕ → ℕ → ℕ → J}
    {r : ℕ → K} {g : ℕ} {y : J → K}
    (hslot : W.slot sX = sh - β * y m)
    (hw : ∀ x, x < rows * blocks →
      ρ.val (e.getD (x / blocks * stride + x % blocks) zeroE) = eqN g 0 r x)
    (hnl : X.nl = 2)
    (hread : ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W v t (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        y (u l (lamOf (x / blocks)) (first + x % blocks)))
    {a : Aff} (h : endForm v t X e rows blocks stride lamOf first = some a) :
    (Aff.slot sX + a).value ρ W =
      Form.val y (cEnd sh β m u r g rows blocks lamOf first) := by
  have hv : a.value ρ W = ∑ x ∈ range (rows * blocks), eqN g 0 r x *
      ∑ l ∈ range 2, (256 : K) ^ l * y (u l (lamOf (x / blocks)) (first + x % blocks)) := by
    unfold endForm at h
    refine sumForms_value_lt _ _ _ (fun x hx b k hb => ?_) h
    obtain ⟨c, hc, ec⟩ := map_some hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ec
    rw [hw x hx, longA_read hρ hc, hnl]
    congr 1
    exact sum_congr rfl fun l hl => by rw [hread x hx l (mem_range.mp hl)]
  unfold cEnd hid
  rw [Aff.value_add, Aff.value_slot, hslot, hv, map_add, map_sub, Form.val_const, map_smul,
    Form.val_ent, smul_eq_mul, map_sum]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, map_sum]
  congr 1
  exact sum_congr rfl fun l _ => by rw [map_smul, Form.val_ent, smul_eq_mul]

/-- **The two claims of one product layer.** -/
theorem endsL_port (hρ : Numerals ρ) {o : Level} {t : ℕ} {e : Array E}
    {rows blocks stride first : ℕ} {lamOf : ℕ → ℕ} {shL shR β : K} {mL mR : J}
    {uS uU : ℕ → ℕ → ℕ → J} {r : ℕ → K} {g : ℕ} {y : J → K}
    (hL : W.slot o.sL = shL - β * y mL) (hR : W.slot o.sR = shR - β * y mR)
    (hw : ∀ x, x < rows * blocks →
      ρ.val (e.getD (x / blocks * stride + x % blocks) zeroE) = eqN g 0 r x)
    (hS : ∀ X, v.y.T_ "s" = some X → X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W v t (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        y (uS l (lamOf (x / blocks)) (first + x % blocks)))
    (hU : ∀ X, v.y.T_ "u" = some X → X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W v t (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        y (uU l (lamOf (x / blocks)) (first + x % blocks)))
    {l : List Aff} (h : endsL v o e t rows blocks stride lamOf first = some l)
    (hz : ∀ q ∈ l, q.value ρ W = 0) :
    Form.val y (cEnd shL β mL uS r g rows blocks lamOf first) = 0 ∧
      Form.val y (cEnd shR β mR uU r g rows blocks lamOf first) = 0 := by
  unfold endsL at h
  obtain ⟨ts, hts, h⟩ := bind_some h
  obtain ⟨tu, htu, h⟩ := bind_some h
  obtain ⟨aS, haS, h⟩ := bind_some h
  obtain ⟨la, lb, ea, hb, rfl⟩ := appL_some h
  obtain rfl : [Aff.slot o.sL + aS] = la := Option.some.inj ea
  obtain ⟨aU, haU, hb⟩ := bind_some hb
  obtain rfl : [Aff.slot o.sR + aU] = lb := Option.some.inj hb
  obtain ⟨nS, rS⟩ := hS ts hts
  obtain ⟨nU, rU⟩ := hU tu htu
  refine ⟨?_, ?_⟩
  · rw [← end_val hρ hL hw nS rS haS]
    exact hz _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
  · rw [← end_val hρ hR hw nU rU haU]
    exact hz _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.end_val
#print axioms OnBytes.Road.Rows.endsL_port
