-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Rows/LayerHotPort.lean: each claim of the verifier "the selector's entries of a routed
layer sum to 1" is worth what the library-side claim is worth, in every world and at all entries
that the dictionary HotDict ties to each other.

Johnson/Road/FormsKeysClaims.lean writes these claims of a layers' sub-proof as a list of forms,
oneHotL. Cb/Pv/Lay/End/NormsCl.lean lists the claims in the library's names, clHot (the part "hot"
of the ledger LayCl, Cb/Pv/Lay/End/LayEnd.lean). This file holds the two against each other, claim
by claim, on values, after the pattern of Johnson/Road/Rows/LayerTermsPort.lean, whose helpers it
calls.

Main names:
  `HotDict`: the dictionary: how numerals are read; two sizes and one switch; the selector at the
    lookup's token point has one limb, and the entries of the array of reads that the verifier's
    forms name are worth the library-side entries of the same names.
  `foldForms_there`: where a sum of forms returns, each of its terms is there.
  `hot_val`: the verifier's claim and the library-side claim have one value.
  `oneHotL_port`: if all forms of oneHotL are worth 0, all forms of clHot are worth 0.
Limits. The dictionary is a premise: no world and no entries are shown at which it holds. Nothing is
said on whether the reads are true, on soundness or on hiding.


-/
import Johnson.Road.Rows.LayerTermsPort
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff tenCell)
open OnBytes.Model.Layer (Env Ten)
open Inst.Model.FFSeg (Dim)
open Cb.Pv.Lay.End (NormsNames cHot clHot)
open Blocks (Form)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- The dictionary between the verifier's letters and the library-side names of the claims on the
selectors' sums. -/
structure HotDict (ρ : Reading K) (W : World K) (v : Env) (D : Dim) (N : NormsNames J)
    (y : J → K) : Prop where
  /-- how numerals are read -/
  num : Numerals ρ
  /-- the sizes and the switch -/
  ne : v.y.LamM = D.ne
  nx : v.y.h.NE = D.nx
  p3 : v.y.h.p3 = true
  /-- the selectors at the lookup's token point: one limb -/
  sel : ∀ X tb, v.tensorAt "sel" "zt" = some (X, tb) → X.nl = 1 ∧
    ∀ l x, l < D.ne → x < D.nx → readAtW W v tb (tenCell X.place 0 l x) = y (N.uSel l x)

variable {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {N : NormsNames J} {y : J → K}

/-- Where the fold that sumForms runs returns, each of its terms is there. -/
theorem foldForms_there (f : ℕ → Option (Aff × E)) :
    ∀ (l : List ℕ) (s a : Aff),
      l.foldlM (fun a x => (f x).map fun t => a.addMul t.1 t.2) s = some a →
      ∀ x ∈ l, ∃ t, f x = some t
  | [], _, _, _, x, hx => absurd hx (List.not_mem_nil)
  | z :: l, s, a, h, x, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨s', hs', h'⟩ := bind_some h
    obtain ⟨t, ht, _⟩ := map_some hs'
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨t, ht⟩
    · exact foldForms_there f l s' a h' x hx'

variable (Dc : HotDict ρ W v D N y)
include Dc

/-- The claim of one routed layer. -/
theorem hot_val {l : ℕ} (hl : l < D.ne) {s : Aff} (hs : hotSum v l = some s) :
    (Aff.ofConst (negE oneE) + s).value ρ W = Form.val y (cHot (E := K) N D.nx l) := by
  have hv : s.value ρ W = ∑ x ∈ range D.nx, y (N.uSel l x) := by
    unfold hotSum at hs
    rw [Dc.nx] at hs
    have hall := foldForms_there _ (List.range D.nx) _ _ hs
    rw [sumForms_value ρ W D.nx _
      (fun x => (((v.shA "sel" "zt" l x).map fun a => (a, oneE)).map fun t =>
        ρ.val t.2 * t.1.value ρ W).getD 0) (fun x b k hb => by dsimp only; rw [hb]; rfl) hs]
    refine sum_congr rfl fun x hx => ?_
    have hx' : x < D.nx := mem_range.mp hx
    obtain ⟨t, ht⟩ := hall x (List.mem_range.mpr hx')
    obtain ⟨a, ha, e⟩ := map_some ht
    subst e
    rw [ht]
    show ρ.val oneE * a.value ρ W = _
    have hX : ∃ X tb, v.tensorAt "sel" "zt" = some (X, tb) := by
      unfold Env.shA Env.shIn at ha
      obtain ⟨z, hz, _⟩ := bind_some ha
      exact ⟨z.1, z.2, hz⟩
    obtain ⟨X, tb, hX⟩ := hX
    obtain ⟨hn, hr⟩ := Dc.sel X tb hX
    rw [ρ.one, one_mul, shA_read Dc.num hX ha, hn, sum_range_one, pow_zero, one_mul,
      hr l x hl hx']
  unfold cHot
  rw [Aff.value_add, Aff.value_ofConst, Dc.num.neg, ρ.one, hv, map_sub, map_sum, Form.val_const]
  simp only [Form.val_ent]
  ring

/-- If all the verifier's claims on the selectors' sums are worth 0, so are all library-side
claims. -/
theorem oneHotL_port {l : List Aff} (h : oneHotL v = some l) (hz : ∀ q ∈ l, q.value ρ W = 0) :
    ∀ f ∈ clHot (E := K) N D, Form.val y f = 0 := by
  unfold oneHotL at h
  rw [if_pos Dc.p3] at h
  intro f hf
  simp only [clHot, List.mem_map, List.mem_range] at hf
  obtain ⟨l', hl', rfl⟩ := hf
  obtain ⟨x, hx, hin⟩ := mem_flat h (List.mem_range.mpr (by rw [Dc.ne]; exact hl'))
  obtain ⟨s, hs, hx⟩ := bind_some hx
  cases hx
  rw [← hot_val Dc hl' hs]
  exact hz _ (hin _ (List.mem_singleton.mpr rfl))

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.hot_val
#print axioms OnBytes.Road.Rows.oneHotL_port
