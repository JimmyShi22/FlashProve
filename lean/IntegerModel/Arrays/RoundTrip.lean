-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Arrays/RoundTrip.lean: from the library's weight tensors (`Weights`,
Inst/Model/Program.lean) to arrays and back.
`weightsTo_weightsArraysOf`: the tensors of the arrays of well-formed tensors are these tensors.
With `weights_back` (IntegerModel/Arrays/ToTensors.lean) the two maps are inverse to each other: the
arrays that pass `weightsAreValid` at valid settings and the library's well-formed tensors are the
same things in two forms.
Well-formed tensors are 0 outside their sizes; that is what the proof uses.
-/
import IntegerModel.Arrays.ToTensors

set_option autoImplicit false

namespace VerifiableInference

open Inst.Model IntegerModel.Readable IntegerModel.Runnable

namespace Back

theorem zero_of_two {W : Mat} (h : Two 0 0 W) (j x : ℕ) : W j x = 0 := by
  have a := h j x
  rw [if_neg (by omega)] at a
  exact a

/-- A matrix that is 0 outside its size is read back from its array. -/
theorem entries_mat {r c : ℕ} {low high : ℤ} {W : Mat} (h : Box r c low high W) :
    (fun j x => ((mat r c W).entry j).entry x) = W := by
  funext j x
  by_cases hi : j < r ∧ x < c
  · exact mat_get W hi.1 hi.2
  · have a := h j x
    rw [if_neg hi] at a
    rw [a]
    exact entries_out (hasSize_mat r c W) hi

theorem layerW_ext {a b : LayerW} (h1 : a.Wq = b.Wq) (h2 : a.Wk = b.Wk) (h3 : a.Wv = b.Wv)
    (h4 : a.Wo = b.Wo) (h5 : a.Wg = b.Wg) (h6 : a.Wu = b.Wu) (h7 : a.Wd = b.Wd) (h8 : a.Wr = b.Wr)
    (h9 : a.Eg = b.Eg) (h10 : a.Eu = b.Eu) (h11 : a.Ed = b.Ed) : a = b := by
  cases a
  cases b
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rfl

theorem weights_ext {a b : Weights} (h1 : a.layer = b.layer) (h2 : a.Emb = b.Emb)
    (h3 : a.H = b.H) : a = b := by
  cases a
  cases b
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- Under the hypothesis `he` below, the three matrices of expert `e` are read back from the array
of experts. -/
theorem routed_entry {n d h : ℕ} {G U D : ℕ → Mat}
    (he : ∀ e, if e < n then Two d h (G e) ∧ Two d h (U e) ∧ Two h d (D e)
      else Two 0 0 (G e) ∧ Two 0 0 (U e) ∧ Two 0 0 (D e)) (e : ℕ) :
    (fun j c => (((tabl n fun e => gatedOf d h (G e) (U e) (D e)).entry e).gate.entry j).entry c)
        = G e ∧
    (fun j c => (((tabl n fun e => gatedOf d h (G e) (U e) (D e)).entry e).up.entry j).entry c)
        = U e ∧
    (fun j c => (((tabl n fun e => gatedOf d h (G e) (U e) (D e)).entry e).down.entry j).entry c)
        = D e := by
  have a := he e
  by_cases hlt : e < n
  · rw [if_pos hlt] at a
    rw [tabl_entry _ hlt]
    exact ⟨entries_mat a.1, entries_mat a.2.1, entries_mat a.2.2⟩
  · rw [if_neg hlt] at a
    have o := gated_out (v := tabl n fun e => gatedOf d h (G e) (U e) (D e)) (e := e)
      (by rw [tabl_size]; omega)
    exact ⟨funext fun j => funext fun c => (zero_of_two o.1 j c).trans (zero_of_two a.1 j c).symm,
      funext fun j => funext fun c => (zero_of_two o.2.1 j c).trans (zero_of_two a.2.1 j c).symm,
      funext fun j => funext fun c => (zero_of_two o.2.2 j c).trans (zero_of_two a.2.2 j c).symm⟩

/-- What is read from an empty array of experts equals any three families of matrices that are 0
everywhere. -/
theorem routed_none {G U D : ℕ → Mat}
    (he : ∀ e, Two 0 0 (G e) ∧ Two 0 0 (U e) ∧ Two 0 0 (D e))
    {v : Array IntegerTransformer.GatedWeights} (hv : v.size = 0) :
    (fun e j c => ((v.entry e).gate.entry j).entry c) = G ∧
    (fun e j c => ((v.entry e).up.entry j).entry c) = U ∧
    (fun e j c => ((v.entry e).down.entry j).entry c) = D := by
  have o : ∀ e, _ := fun e => gated_out (v := v) (e := e) (by omega)
  exact ⟨funext fun e => funext fun j => funext fun c =>
      (zero_of_two (o e).1 j c).trans (zero_of_two (he e).1 j c).symm,
    funext fun e => funext fun j => funext fun c =>
      (zero_of_two (o e).2.1 j c).trans (zero_of_two (he e).2.1 j c).symm,
    funext fun e => funext fun j => funext fun c =>
      (zero_of_two (o e).2.2 j c).trans (zero_of_two (he e).2.2 j c).symm⟩

/-- A matrix that is 0 everywhere is what is read from an empty array. -/
theorem entries_none {W : Mat} (h : Two 0 0 W) {M : Array (Array ℤ)} (hM : M.size = 0) :
    (fun j x => (M.entry j).entry x) = W :=
  funext fun j => funext fun x => (entries_empty hM j x).trans (zero_of_two h j x).symm

/-- The tensors of one layer, to arrays and back. -/
theorem layerTo_layerArrays {P : Params} {L : ℕ} {w : LayerW} (h : w.WF P L) :
    layerTo (layerArrays P w L) = w := by
  obtain ⟨hq, hk, hv, ho, hr⟩ := h
  unfold layerArrays
  by_cases hE : hasExperts L
  · rw [if_pos hE] at hr ⊢
    obtain ⟨hg, hu, hd, hw, he⟩ := hr
    have hg' : Two P.d (if hasExperts L then P.fe else P.f) w.Wg := by rw [if_pos hE]; exact hg
    have hu' : Two P.d (if hasExperts L then P.fe else P.f) w.Wu := by rw [if_pos hE]; exact hu
    have hd' : Two (if hasExperts L then P.fe else P.f) P.d w.Wd := by rw [if_pos hE]; exact hd
    exact layerW_ext (entries_mat hq) (entries_mat hk) (entries_mat hv) (entries_mat ho)
      (entries_mat hg') (entries_mat hu') (entries_mat hd') (entries_mat hw)
      (funext fun e => (routed_entry he e).1) (funext fun e => (routed_entry he e).2.1)
      (funext fun e => (routed_entry he e).2.2)
  · rw [if_neg hE] at hr ⊢
    obtain ⟨hg, hu, hd, hw, he⟩ := hr
    have hg' : Two P.d (if hasExperts L then P.fe else P.f) w.Wg := by rw [if_neg hE]; exact hg
    have hu' : Two P.d (if hasExperts L then P.fe else P.f) w.Wu := by rw [if_neg hE]; exact hu
    have hd' : Two (if hasExperts L then P.fe else P.f) P.d w.Wd := by rw [if_neg hE]; exact hd
    have o := routed_none he (v := (#[] : Array IntegerTransformer.GatedWeights)) rfl
    exact layerW_ext (entries_mat hq) (entries_mat hk) (entries_mat hv) (entries_mat ho)
      (entries_mat hg') (entries_mat hu') (entries_mat hd')
      (entries_none hw (M := (#[] : Array (Array ℤ))) rfl) o.1 o.2.1 o.2.2

/-- The tensors read from the default (empty) arrays of a layer equal any all-zero layer
(`LayerW.IsZero`); used beyond the last layer, where well-formed tensors are 0. -/
theorem layerTo_default {w : LayerW} (h : w.IsZero) :
    layerTo (default : IntegerTransformer.LayerWeights) = w := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, ze⟩ := h
  have o := routed_none ze (v := (default : IntegerTransformer.LayerWeights).routed) rfl
  exact layerW_ext
    (entries_none z1 (M := (default : IntegerTransformer.LayerWeights).query) rfl)
    (entries_none z2 (M := (default : IntegerTransformer.LayerWeights).key) rfl)
    (entries_none z3 (M := (default : IntegerTransformer.LayerWeights).value) rfl)
    (entries_none z4 (M := (default : IntegerTransformer.LayerWeights).output) rfl)
    (entries_none z5 (M := (default : IntegerTransformer.LayerWeights).shared.gate) rfl)
    (entries_none z6 (M := (default : IntegerTransformer.LayerWeights).shared.up) rfl)
    (entries_none z7 (M := (default : IntegerTransformer.LayerWeights).shared.down) rfl)
    (entries_none z8 (M := (default : IntegerTransformer.LayerWeights).router) rfl)
    o.1 o.2.1 o.2.2

/-- Well-formed tensors, to arrays and back: the same tensors. -/
theorem weightsTo_weightsArraysOf {P : Params} {w : Weights} (h : w.WF P) :
    weightsTo (weightsArraysOf P w) = w := by
  obtain ⟨hl, he, hh⟩ := h
  refine weights_ext (funext fun L => ?_) (entries_mat he) (entries_mat hh)
  show layerTo ((tabl P.layers fun L => layerArrays P (w.layer L) L).entry L) = w.layer L
  have b := hl L
  by_cases hL : L < P.layers
  · rw [if_pos hL] at b
    rw [tabl_entry _ hL]
    exact layerTo_layerArrays b
  · rw [if_neg hL] at b
    rw [entry_out (tabl P.layers fun L => layerArrays P (w.layer L) L) (k := L)
      (by rw [tabl_size]; omega)]
    exact layerTo_default b

end Back

end VerifiableInference
