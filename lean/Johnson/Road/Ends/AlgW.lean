-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgW.lean: the library's weights of a layer, beside G.lean's.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (wt_entryR) G.lean's weight of the unit of kind X of layer l at given indices, read in a
reading whose cells of W are Wc, IS THE LIBRARY's entryR of that unit at these indices.
(agreeW_layerR) **THE LIBRARY's WEIGHTS OF A LAYER, READ FROM W BY THE LIBRARY's OWN LAYOUT
(layerR), ARE G.lean's (wOfG), INSIDE THE MATRICES' RANGES**: AgreeW (AlgCongr.lean), the premise of
keyVec_kvG and callKey_of_inTable.
How: layout_eq and unitOf_eq (Johnson/Road/FormsKeysWLay.lean: the verifier's layout of the
committed weights is the library's: unit by unit, and cellOf is the library's place);
AlgWcell.lean's wcell_eq_cellOf.
Under: the verifier's wsLayOf has returned P's layout of W, for a model with mixtures of experts, at
a shape that agrees with the library's parameters in nine numbers (SizedW); the group's first layer
L0 = g * Lam is even and its layers lie below the model's; the odd layers have routed experts; two
sizes of the layers' shape.
Does not say: anything on the verifier's own reading of W (its settling of a claim stands in no
statement here: the verifier's layout RECORD is read by the cell rule wcell = cellOf); that the
reading's cells cell (.w r c) are the entries of the committed matrix: the premise hcell defines Wc
by them, and nothing here ties them to a commitment.
-/
import Johnson.Road.FormsKeysWLay
import Johnson.Road.Ends.AlgWcell
import Johnson.Road.Ends.AlgGam
import Johnson.Road.Ends.AlgCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Ends
open OnBytes.Model (WsShape WsLay wsLayOf)
open Inst.Model (Params hasExperts)
open Inst.Model.Layout (UnitS uQK uV uO uGU uD uGUr uDr uR)
open Inst.Model.FFSeg (Dim LW layerR entryR matR isExpL)

/-- Unit number i of layer l has, in the library's whole list, the number i on top of the units of
the layers before. -/
theorem lib_at (Pp : Params) {l i : ℕ} {U : UnitS} (hl : l < Pp.layers)
    (h : (Inst.Model.Layout.layerUnits Pp l)[i]? = some U) :
    (Inst.Model.Layout.units Pp)[Inst.Model.Layout.first Pp l + i]? = some U := by
  obtain ⟨t, ht⟩ := flat_split (Inst.Model.Layout.layerUnits Pp) Pp.layers l hl
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp h
  unfold Inst.Model.Layout.units Inst.Model.Layout.first
  rw [ht, List.append_assoc, List.getElem?_append_right
    (by rw [List.length_flatMap]; exact Nat.le_add_right _ _), List.length_flatMap,
    Nat.add_sub_cancel_left, List.append_assoc, List.getElem?_append_left hi]
  exact h

/-- An entry of a matrix inside its rows and columns. -/
theorem matR_in {R : Type} [CommRing R] {r c j x : ℕ} (f : ℕ → ℕ → R) (hj : j < r) (hx : x < c) :
    matR r c f j x = f j x := by
  unfold matR
  rw [if_pos ⟨hj, hx⟩]

section W

variable {K : Type} [Field K] {s : WsShape} {Pp : Params} {lk : ℕ} {P : Model.Layer.Pub}
  {cell : G.NameG → K} {Wc : ℕ → ℕ → K}

/-- **G.lean's weight is the library's entry.** -/
theorem wt_entryR (Z : SizedW s Pp) (h : wsLayOf s true lk = .ok P.wsLay)
    (hcell : ∀ r c, cell (.w r c) = Wc r c) {l i X : ℕ} {U : UnitS} (hl : l < Pp.layers)
    (hX : (kindsOf l)[i]? = some X) (hU : (Inst.Model.Layout.layerUnits Pp l)[i]? = some U)
    (idx : List ℕ) :
    G.wt P cell X l idx = entryR Pp lk Wc (Inst.Model.Layout.first Pp l + i) U idx := by
  obtain ⟨u, hu, UOK, hnl, -, -, -, -, -, hc⟩ := (layout_eq Z h).2.2.2 _ U (lib_at Pp hl hU)
  unfold G.wt entryR
  rw [(unitOf_eq Z h).1 l hl i X hX]
  show (match P.wsLay.U[Inst.Model.Layout.first Pp l + i]? with
    | some u => G.sumN u.nlw fun δ =>
      (256 : K) ^ δ * cell (.w (H.wcell u δ idx).1 (H.wcell u δ idx).2)
    | none => 0) = _
  rw [hu]
  show G.sumN u.nlw (fun δ =>
    (256 : K) ^ δ * cell (.w (H.wcell u δ idx).1 (H.wcell u δ idx).2)) = _
  rw [sumN_eq, hnl]
  refine sum_congr rfl fun δ _ => ?_
  rw [hcell, wcell_eq_cellOf UOK.grp, hc]

/-- **The library's weights of a group's layers are G.lean's, inside the ranges.** -/
theorem agreeW_layerR (Z : SizedW s Pp) (h : wsLayOf s true lk = .ok P.wsLay)
    (hcell : ∀ r c, cell (.w r c) = Wc r c) {D : Dim} (hD : D.P = Pp) (g : ℕ)
    (hev : g * P.y.Lam % 2 = 0) (hL : ∀ l < D.nl, g * P.y.Lam + l < Pp.layers)
    (hp3 : P.y.h.p3 = true) (hdh : P.y.h.dh = Pp.ch) (hdq : P.y.dq = Pp.nq * Pp.ch)
    (hch : 0 < Pp.ch) :
    AgreeW D (fun l => layerR Pp lk Wc (g * P.y.Lam + l)) (wOfG P g cell) := by
  subst hD
  have odd : ∀ l, isExpL l = true → hasExperts (g * P.y.Lam + l) := fun l he => by
    unfold isExpL at he
    unfold hasExperts
    have : l % 2 = 1 := by simpa using he
    omega
  have even : ∀ l, ¬ isExpL l = true → ¬ hasExperts (g * P.y.Lam + l) := fun l he => by
    unfold isExpL at he
    unfold hasExperts
    have : ¬ l % 2 = 1 := by simpa using he
    omega
  have kOdd : ∀ l, isExpL l = true →
      kindsOf (g * P.y.Lam + l) = [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] := fun l he => by
    unfold kindsOf
    exact if_pos (odd l he)
  have kEven : ∀ l, ¬ isExpL l = true → kindsOf (g * P.y.Lam + l) = [0, 1, 2, 3, 4, 9] :=
    fun l he => by
      unfold kindsOf
      exact if_neg (even l he)
  have uOdd : ∀ l, isExpL l = true → Inst.Model.Layout.layerUnits D.P (g * P.y.Lam + l) =
      [uQK D.P, uV D.P, uO D.P, uGU D.P D.P.fe, uGU D.P D.P.fe, uGUr D.P, uGUr D.P,
        uD D.P D.P.fe, uDr D.P, uR D.P] := fun l he => by
    unfold Inst.Model.Layout.layerUnits
    rw [if_pos (odd l he)]
    rfl
  have uEven : ∀ l, ¬ isExpL l = true → Inst.Model.Layout.layerUnits D.P (g * P.y.Lam + l) =
      [uQK D.P, uV D.P, uO D.P, uGU D.P D.P.f, uGU D.P D.P.f, uD D.P D.P.f] := fun l he => by
    unfold Inst.Model.Layout.layerUnits
    rw [if_neg (even l he)]
    rfl
  have k3 : ∀ l (i X : ℕ), ([0, 1, 2] : List ℕ)[i]? = some X →
      (kindsOf (g * P.y.Lam + l))[i]? = some X := fun l i X hi => by
    have hi3 : i < 3 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simpa using hc)] at hi
      cases hi
    by_cases he : isExpL l = true
    · rw [kOdd l he]
      interval_cases i <;> exact hi
    · rw [kEven l he]
      interval_cases i <;> exact hi
  have u3 : ∀ l (i : ℕ) (U : UnitS), ([uQK D.P, uV D.P, uO D.P] : List UnitS)[i]? = some U →
      (Inst.Model.Layout.layerUnits D.P (g * P.y.Lam + l))[i]? = some U := fun l i U hi => by
    have hi3 : i < 3 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simpa using hc)] at hi
      cases hi
    by_cases he : isExpL l = true
    · rw [uOdd l he]
      interval_cases i <;> exact hi
    · rw [uEven l he]
      interval_cases i <;> exact hi
  have moeT : ∀ l, isExpL l = true → G.moe P l = true := fun l he => by
    unfold G.moe
    rw [hp3, Bool.true_and]
    exact he
  have moeF : ∀ l, ¬ isExpL l = true → ¬ G.moe P l = true := fun l he => by
    unfold G.moe
    rw [hp3, Bool.true_and]
    exact he
  refine ⟨fun l hl j hj x hx => ?_, fun l hl j hj x hx => ?_, fun l hl j hj x hx => ?_,
    fun l hl j hj x hx => ?_, fun l hl j hj x hx => ?_, fun l hl j hj x hx => ?_,
    fun l hl j hj x hx => ?_, fun l hl he j hj x hx => ?_, fun l hl he e hE j hj x hx => ?_,
    fun l hl he e hE j hj x hx => ?_, fun l hl he e hE j hj x hx => ?_⟩
  · have e : (layerR D.P lk Wc (g * P.y.Lam + l)).Wq = matR D.P.d (D.P.nq * D.P.ch) fun j c =>
        entryR D.P lk Wc (Inst.Model.Layout.first D.P (g * P.y.Lam + l)) (uQK D.P)
          [c / D.P.ch, c % D.P.ch, j] := rfl
    show (layerR D.P lk Wc (g * P.y.Lam + l)).Wq j x =
      G.wt P cell 0 (g * P.y.Lam + l) [x / P.y.h.dh, x % P.y.h.dh, j]
    rw [e, matR_in (r := D.P.d) (c := D.P.nq * D.P.ch) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (k3 l 0 0 rfl) (u3 l 0 _ rfl), hdh]
    rfl
  · have e : (layerR D.P lk Wc (g * P.y.Lam + l)).Wk = matR D.P.d (D.P.nkv * D.P.ch) fun j c =>
        entryR D.P lk Wc (Inst.Model.Layout.first D.P (g * P.y.Lam + l)) (uQK D.P)
          [D.P.nq + c / D.P.ch, c % D.P.ch, j] := rfl
    show (layerR D.P lk Wc (g * P.y.Lam + l)).Wk j x =
      G.wt P cell 0 (g * P.y.Lam + l) [(P.y.dq + x) / P.y.h.dh, (P.y.dq + x) % P.y.h.dh, j]
    rw [e, matR_in (r := D.P.d) (c := D.P.nkv * D.P.ch) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (k3 l 0 0 rfl) (u3 l 0 _ rfl), hdh, hdq,
      Nat.mul_comm D.P.nq, Nat.mul_add_div hch, Nat.mul_add_mod]
    rfl
  · have e : (layerR D.P lk Wc (g * P.y.Lam + l)).Wv = matR D.P.d (D.P.nkv * D.P.ch) fun j x =>
        entryR D.P lk Wc (Inst.Model.Layout.first D.P (g * P.y.Lam + l) + 1) (uV D.P) [j, x] := rfl
    show (layerR D.P lk Wc (g * P.y.Lam + l)).Wv j x = G.wt P cell 1 (g * P.y.Lam + l) [j, x]
    rw [e, matR_in (r := D.P.d) (c := D.P.nkv * D.P.ch) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (k3 l 1 1 rfl) (u3 l 1 _ rfl)]
  · have e : (layerR D.P lk Wc (g * P.y.Lam + l)).Wo = matR (D.P.nq * D.P.ch) D.P.d fun j x =>
        entryR D.P lk Wc (Inst.Model.Layout.first D.P (g * P.y.Lam + l) + 2) (uO D.P) [j, x] := rfl
    show (layerR D.P lk Wc (g * P.y.Lam + l)).Wo j x = G.wt P cell 2 (g * P.y.Lam + l) [j, x]
    rw [e, matR_in (r := D.P.nq * D.P.ch) (c := D.P.d) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (k3 l 2 2 rfl) (u3 l 2 _ rfl)]
  · by_cases he : isExpL l = true
    · rw [if_pos he] at hx
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.d D.P.fe _ else matR D.P.d D.P.f _) j x =
        G.wt P cell (if G.moe P l then 5 else 3) (g * P.y.Lam + l) _
      rw [if_pos (odd l he), if_pos (moeT l he), matR_in (r := D.P.d) (c := D.P.fe) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 3) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
    · rw [if_neg he] at hx
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.d D.P.fe _ else matR D.P.d D.P.f _) j x =
        G.wt P cell (if G.moe P l then 5 else 3) (g * P.y.Lam + l) _
      rw [if_neg (even l he), if_neg (moeF l he), matR_in (r := D.P.d) (c := D.P.f) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 3) (by rw [kEven l he]; rfl) (by rw [uEven l he]; rfl)]
  · by_cases he : isExpL l = true
    · rw [if_pos he] at hx
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.d D.P.fe _ else matR D.P.d D.P.f _) j x =
        G.wt P cell (if G.moe P l then 6 else 4) (g * P.y.Lam + l) _
      rw [if_pos (odd l he), if_pos (moeT l he), matR_in (r := D.P.d) (c := D.P.fe) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 4) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
    · rw [if_neg he] at hx
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.d D.P.fe _ else matR D.P.d D.P.f _) j x =
        G.wt P cell (if G.moe P l then 6 else 4) (g * P.y.Lam + l) _
      rw [if_neg (even l he), if_neg (moeF l he), matR_in (r := D.P.d) (c := D.P.f) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 4) (by rw [kEven l he]; rfl) (by rw [uEven l he]; rfl)]
  · by_cases he : isExpL l = true
    · rw [if_pos he] at hj
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.fe D.P.d _ else matR D.P.f D.P.d _) j x =
        G.wt P cell 9 (g * P.y.Lam + l) _
      rw [if_pos (odd l he), matR_in (r := D.P.fe) (c := D.P.d) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 7) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
    · rw [if_neg he] at hj
      show (if hasExperts (g * P.y.Lam + l) then matR D.P.fe D.P.d _ else matR D.P.f D.P.d _) j x =
        G.wt P cell 9 (g * P.y.Lam + l) _
      rw [if_neg (even l he), matR_in (r := D.P.f) (c := D.P.d) _ hj hx,
        wt_entryR Z h hcell (hL l hl) (i := 5) (by rw [kEven l he]; rfl) (by rw [uEven l he]; rfl)]
  · show (if hasExperts (g * P.y.Lam + l) then matR D.P.d D.P.nexp _ else fun _ _ => 0) j x =
      G.wt P cell 11 (g * P.y.Lam + l) _
    rw [if_pos (odd l he), matR_in (r := D.P.d) (c := D.P.nexp) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (i := 9) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
  · show (if hasExperts (g * P.y.Lam + l) ∧ e < D.P.nexp then matR D.P.d D.P.fe _
      else fun _ _ => 0) j x = G.wt P cell 7 (g * P.y.Lam + l) _
    rw [if_pos ⟨odd l he, hE⟩, matR_in (r := D.P.d) (c := D.P.fe) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (i := 5) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
  · show (if hasExperts (g * P.y.Lam + l) ∧ e < D.P.nexp then matR D.P.d D.P.fe _
      else fun _ _ => 0) j x = G.wt P cell 8 (g * P.y.Lam + l) _
    rw [if_pos ⟨odd l he, hE⟩, matR_in (r := D.P.d) (c := D.P.fe) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (i := 6) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]
  · show (if hasExperts (g * P.y.Lam + l) ∧ e < D.P.nexp then matR D.P.fe D.P.d _
      else fun _ _ => 0) j x = G.wt P cell 10 (g * P.y.Lam + l) _
    rw [if_pos ⟨odd l he, hE⟩, matR_in (r := D.P.fe) (c := D.P.d) _ hj hx,
      wt_entryR Z h hcell (hL l hl) (i := 8) (by rw [kOdd l he]; rfl) (by rw [uOdd l he]; rfl)]

end W

#print axioms wt_entryR
#print axioms agreeW_layerR

end OnBytes.Road.Alg
