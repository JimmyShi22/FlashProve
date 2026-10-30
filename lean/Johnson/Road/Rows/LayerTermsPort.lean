-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerTermsPort.lean: each claim of the verifier on an end value of the second
token sumcheck of a layers' sub-proof is worth what the library-side claim is worth, in every world
and at all entries that the dictionary TermsDict ties to each other.

Johnson/Road/Rows/LayerEnds3S.lean writes the verifier's claims on these end values as a list of
forms, termsL. Cb/Pv/Lay/End/TermsCl.lean lists claims on the same end values in the library's
names, termsCl. This file holds the two against each other, claim by claim, on values. It asks one
dictionary, TermsDict: the sizes agree; the hidden value under the slot of an end value is what was
shown less the challenge times the mask entry; and the entries of the array of reads that the
verifier's forms name are worth the library-side entries of the same names.

Main names:
  `TermsDict`: the dictionary.
  `rec_val`, `sc_val`, `sel_val`: the verifier's claim and the library-side claim have one value.
  `termsL_port`: if all forms of termsL are worth 0, all forms of termsCl are worth 0.
Limits. The dictionary is a premise: no world and no entries are shown at which it holds. Nothing is
said on whether the reads are true, on soundness or on hiding. Rows with five limbs alone.


-/
import Johnson.Road.Rows.LayerEnds3S
import Cb.Pv.Lay.End.TermsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff tenCell)
open OnBytes.Model.Layer (Env Ten aff0)
open Inst.Model.FFSeg (Dim Arr)
open Cb.Pv.Lay.End (TermsNames TermsE hT val_hT valF cRec cSc cSel termsCl)
open Blocks (Form)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- What entry φ of the family of tables that begins at entry tb of the reads is worth. -/
def readAtW (W : World K) (v : Env) (tb φ : ℕ) : K :=
  W.entry v.iU3 ((tb + φ) / v.K3) ((tb + φ) % v.K3)

/-- The dictionary between the verifier's letters and the library-side letters of the claims on the
end values of the second token sumcheck. -/
structure TermsDict (ρ : Reading K) (W : World K) (v : Env) (sEnd : ℕ) (D : Dim)
    (N : TermsNames J) (e : TermsE K) (y : J → K) : Prop where
  /-- how numerals are read -/
  num : Numerals ρ
  /-- the sizes and the two switches -/
  nNu : v.y.NN * v.y.Lam = D.nNu
  ne : v.y.LamM = D.ne
  nx : v.y.h.NE = D.nx
  p3 : v.y.h.p3 = true
  xl : v.y.h.xl = 5
  /-- the hidden value under the slot of end value number x -/
  slot : ∀ x, x < D.nNu + D.ne + D.ne * D.nx →
    W.slot (sEnd + x) = e.sh x - e.β * y (N.mT x)
  /-- the cells of the norms' ledgers -/
  row : ∀ t tr, v.tabAt ("ar@" ++ "rt") = some t → v.y.T_ "row" = some tr →
    ∀ ν n, ν < D.nNu → n < 99 → readAtW W v t (tr.OFF + ν * 99 + n) = y (N.uRow ν n)
  /-- the scores: three limbs -/
  sc : ∀ X tb, v.tensorAt "sc" "rt" = some (X, tb) → X.nl = 3 ∧
    ∀ l k, l < D.ne → k < 3 → readAtW W v tb (tenCell X.place k l 0) = y (N.uSc l k)
  /-- the selectors: one limb -/
  sel : ∀ X tb, v.tensorAt "sel" "rt" = some (X, tb) → X.nl = 1 ∧
    ∀ l x k, l < D.ne → x < D.nx → k < 1 →
      readAtW W v tb (tenCell X.place k l x) = y (N.uSel l x k)

variable {ρ : Reading K} {W : World K} {v : Env} {sEnd : ℕ} {D : Dim} {N : TermsNames J}
  {e : TermsE K} {y : J → K}

/-- A form that U3at hands out is worth the entry of the reads. -/
theorem U3at_read {tb φ : ℕ} {a : Aff} (h : v.U3at tb φ = some a) :
    a.value ρ W = readAtW W v tb φ := by
  obtain ⟨_, _, _, hv⟩ := U3at_entry ρ W h
  exact hv

/-- The read-out formula, written out. -/
theorem val_valF_sum (X : Arr) (u : ℕ → J) :
    Form.val y (valF (E := K) X u) =
      ∑ k ∈ range X.nCell, (256 : K) ^ k * y (u k) + ((X.off : ℤ) : K) := by
  unfold valF
  rw [map_add, map_sum, Form.val_const]
  congr 1
  exact sum_congr rfl fun k _ => by rw [map_smul, Form.val_ent, smul_eq_mul]

/-- An entry of a tensor with nl limbs, read from a short table. -/
theorem shA_read (hρ : Numerals ρ) {Xn P : String} {i j : ℕ} {a : Aff} {X : Ten} {tb : ℕ}
    (hX : v.tensorAt Xn P = some (X, tb)) (h : v.shA Xn P i j = some a) :
    a.value ρ W = ∑ k ∈ range X.nl, (256 : K) ^ k * readAtW W v tb (tenCell X.place k i j) := by
  unfold Env.shA at h
  rw [hX] at h
  have h3 : v.limbs tb X.nl (fun l => tenCell X.place l i j) = some a := h
  exact limbs_value hρ (readAtW W v tb) (fun _ _ hb => U3at_read hb) h3

variable (Dc : TermsDict ρ W v sEnd D N e y)
include Dc

/-- The reciprocal of a norm. -/
theorem rec_val {ν : ℕ} (hν : ν < D.nNu) {f : Aff} (hf : v.rowR "rt" ν = some f) :
    (Aff.slot (sEnd + ν) - f).value ρ W = Form.val y (cRec N e ν) := by
  unfold cRec
  rw [Aff.value_sub, Aff.value_slot, Dc.slot ν (by omega), map_sub, val_hT,
    Inst.Model.Ledger.val_RF]
  congr 1
  unfold Env.rowR at hf
  have h5 : (v.y.h.xl == 5) = true := by rw [Dc.xl]; rfl
  rw [if_pos h5] at hf
  obtain ⟨row, hr, er⟩ := map_some hf
  subst er
  unfold Env.row5At at hr
  obtain ⟨cells, hc, er⟩ := bind_some hr
  obtain rfl : Model.row5 (fun j => cells.getD j aff0) = row := Option.some.inj er
  refine Hd.row5_R Dc.num fun n hn => ?_
  unfold Env.rowCells at hc
  obtain ⟨t, ht, hc⟩ := bind_some hc
  obtain ⟨tr, htr, hc⟩ := bind_some hc
  have h1 := range_mapM_get aff0 hc hn
  rw [U3at_read h1, Dc.row t tr ht htr ν n hν hn, val_valF_sum]
  simp [Arr.nCell, Arr.off]

/-- The score of a layer with routed experts. -/
theorem sc_val {l : ℕ} (hl : l < D.ne) {f : Aff} (hf : v.shA "sc" "rt" l 0 = some f) :
    (Aff.slot (sEnd + v.y.NN * v.y.Lam + l) - f).value ρ W =
      Form.val y (cSc N e D.nNu l) := by
  have hX : ∃ X tb, v.tensorAt "sc" "rt" = some (X, tb) := by
    unfold Env.shA Env.shIn at hf
    obtain ⟨x, hx, _⟩ := bind_some hf
    exact ⟨x.1, x.2, hx⟩
  obtain ⟨X, tb, hX⟩ := hX
  obtain ⟨hn, hr⟩ := Dc.sc X tb hX
  unfold cSc
  rw [Aff.value_sub, Aff.value_slot, Dc.nNu, Nat.add_assoc,
    Dc.slot (D.nNu + l) (by have := Nat.zero_le (D.ne * D.nx); omega), map_sub, val_hT,
    shA_read Dc.num hX hf, val_valF_sum, hn]
  congr 1
  have e0 : ((Arr.sc.off : ℤ) : K) = 0 := by simp [Arr.off]
  rw [e0, add_zero]
  exact sum_congr rfl fun k hk => by rw [hr l k hl (mem_range.mp hk)]

/-- An entry of the selector of a layer with routed experts. -/
theorem sel_val {l x : ℕ} (hl : l < D.ne) (hx : x < D.nx) {f : Aff}
    (hf : v.shA "sel" "rt" l x = some f) :
    (Aff.slot (sEnd + v.y.NN * v.y.Lam + v.y.LamM + (l * v.y.h.NE + x)) - f).value ρ W =
      Form.val y (cSel N e D.nNu D.ne D.nx l x) := by
  have hX : ∃ X tb, v.tensorAt "sel" "rt" = some (X, tb) := by
    unfold Env.shA Env.shIn at hf
    obtain ⟨z, hz, _⟩ := bind_some hf
    exact ⟨z.1, z.2, hz⟩
  obtain ⟨X, tb, hX⟩ := hX
  obtain ⟨hn, hr⟩ := Dc.sel X tb hX
  have hlt : l * D.nx + x < D.ne * D.nx := by
    calc l * D.nx + x < l * D.nx + D.nx := by omega
      _ = (l + 1) * D.nx := by ring
      _ ≤ D.ne * D.nx := Nat.mul_le_mul_right _ hl
  have es : sEnd + D.nNu + D.ne + (l * D.nx + x) = sEnd + (D.nNu + D.ne + l * D.nx + x) := by
    omega
  unfold cSel
  rw [Aff.value_sub, Aff.value_slot, Dc.nNu, Dc.ne, Dc.nx, es,
    Dc.slot (D.nNu + D.ne + l * D.nx + x) (by omega), map_sub, val_hT,
    shA_read Dc.num hX hf, val_valF_sum, hn]
  congr 1
  have e0 : ((Arr.sel.off : ℤ) : K) = 0 := by simp [Arr.off]
  rw [e0, add_zero]
  exact sum_congr rfl fun k hk => by rw [hr l x k hl hx (mem_range.mp hk)]

/-- If all the verifier's claims on the end values are worth 0, so are all library-side claims. -/
theorem termsL_port {l : List Aff} (h : termsL v sEnd = some l)
    (hz : ∀ q ∈ l, q.value ρ W = 0) : ∀ f ∈ termsCl N e D, Form.val y f = 0 := by
  unfold termsL at h
  obtain ⟨la, lb, ha, hb, rfl⟩ := appL_some h
  rw [if_pos Dc.p3] at hb
  obtain ⟨lc, ld, hc, hd, rfl⟩ := appL_some hb
  intro f hf
  simp only [termsCl, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with (⟨ν, hν, rfl⟩ | ⟨l', hl', rfl⟩) | ⟨i, hi, rfl⟩
  · obtain ⟨x, hx, hin⟩ := mem_flat ha (List.mem_range.mpr (by rw [Dc.nNu]; exact hν))
    obtain ⟨g, hg, hx⟩ := bind_some hx
    cases hx
    rw [← rec_val Dc hν hg]
    exact hz _ (List.mem_append_left _ (hin _ (List.mem_singleton.mpr rfl)))
  · obtain ⟨x, hx, hin⟩ := mem_flat hc (List.mem_range.mpr (by rw [Dc.ne]; exact hl'))
    obtain ⟨g, hg, hx⟩ := bind_some hx
    cases hx
    rw [← sc_val Dc hl' hg]
    exact hz _ (List.mem_append_right _ (List.mem_append_left _
      (hin _ (List.mem_singleton.mpr rfl))))
  · have hx0 : 0 < D.nx := by
      rcases Nat.eq_zero_or_pos D.nx with h0 | h0
      · rw [h0, Nat.mul_zero] at hi
        exact absurd hi (Nat.not_lt_zero _)
      · exact h0
    have hl2 : i / D.nx < D.ne := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
    have hx2 : i % D.nx < D.nx := Nat.mod_lt _ hx0
    obtain ⟨x, hx, hin⟩ := mem_flat hd (List.mem_range.mpr (by rw [Dc.ne, Dc.nx]; exact hi))
    obtain ⟨g, hg, hx⟩ := bind_some hx
    cases hx
    rw [Dc.nx] at hg
    have ei : i / D.nx * v.y.h.NE + i % D.nx = i := by
      rw [Dc.nx, Nat.mul_comm]
      exact Nat.div_add_mod i D.nx
    have hv := sel_val Dc hl2 hx2 hg
    rw [ei] at hv
    rw [← hv]
    exact hz _ (List.mem_append_right _ (List.mem_append_right _
      (hin _ (List.mem_singleton.mpr rfl))))

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.rec_val
#print axioms OnBytes.Road.Rows.sc_val
#print axioms OnBytes.Road.Rows.sel_val
#print axioms OnBytes.Road.Rows.termsL_port
