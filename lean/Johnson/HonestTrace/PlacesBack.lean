-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlacesBack.lean

The laws on the places of Johnson/HonestTrace/Places.lean: in range, there and back, the laying,
padding, and attention's borrowed names. At any sizes and any number of groups.

"Under OK" below means: for every structure of numbers S with "Sz.OK" (there is a group; a column of
each matrix of features holds a feature; af, ad, as, hf have a part; 5 ≤ lm ≤ kT + 5 for the planes
of each segment of the proof; lB + 1 ≤ lt). "Under Fit": with "Sz.Fit" (nkv = 2^lg, ch = 2^ln, nkv
divides nq). A segment of the proof is the head or a segment of a group below nGr.

Main theorems:
* "place_inShape": under OK the place of a valid name lies inside the shape of its matrix.
* "nameAt_place": under OK "nameAt" at the place of a valid name returns that name. "place_inj":
  so two valid names with one place are one name.
* "nameAt_back": under OK a name that "nameAt" returns is valid and stands at the place asked for.
* "nameAt_none_iff", "nameAt_as_none_iff", "nameAt_plane": inside the shape of a matrix that its
  segment owns, "nameAt" is "none" exactly at a feature (under OK), or a cell of as, that is not in
  use, and never in the planes.
* "lay_place", "lay_off", "lay_small": under OK the laid matrices hold each valid name's cell at its
  place, and are as small as these cells; outside the shapes they are 0.
* "shape_owner", "lay_owner": under OK a borrowed matrix in the list of a segment of the proof has
  its owner's shape and its owner's entries.
* "place_qry", "place_out", "place_key", "place_val": under Fit a borrowed name of attention is laid
  where the feed-forward segment lays its own cell.

How. Each decoder is shown right in one direction by arithmetic (decode, then encode: "ffName_back",
"asName_spec", "ahName_spec", "aoName_spec", "bitName_back"). For the layers' and attention's names
the other direction comes from theorems of the library that the numbers of features and cells are
different for different valid names ("phi_inj", "adr_inj" of Inst/Model/Att/AddrFacts.lean;
"offL_disj" of Inst/Model/FF/IndexFacts.lean). For the bits and the head's features it is arithmetic
of this file too ("bitName_atBit", "featOf_atFeat").

Limits. These are laws on the functions of Johnson/HonestTrace/Places.lean, whose limits hold here
too: the rules were typed by a reading of the format's pages, at fixed digit forms. That "OK" and
"Fit" hold somewhere is shown in Johnson/HonestTrace/Places.lean, at the numbers of the two example
sets. "nameAt_none_iff" does not speak of xbI from group 1 on, of qa in attention or of xbL: there
"nameAt" is "none" everywhere, and "lay" reads the owner's matrix.

Not claimed: that any program lays its cells so, or that a verifier reads them so; anything on the
values of the cells.

-/
import Johnson.HonestTrace.Places

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open Inst.Model.AttSeg.AddrFacts (adr phi pos mat SM SD S1 S2 S3 Phi fK fI fL IsC)

/-! ## Matrices of features -/

/-- μ is the name of a matrix of features of σ's sort that σ owns, or xbI in a feed-forward segment.
Nothing is asked of the part's number. -/
def isFeat : Seg → MatName → Bool
  | .ff _, .af _ | .ff _, .ad _ | .ff _, .ar | .ff _, .qa | .ff _, .xbO | .ff _, .xbI => true
  | .att _, .ah | .att _, .ao => true
  | .head, .hf _ | .head, .hd | .head, .hr => true
  | _, _ => false

namespace Sz
variable (S : Sz)

/-- The features in a column do not depend on the part. -/
theorem wc_setPart (μ : MatName) (p : ℕ) : S.wc (μ.setPart p) = S.wc μ := by cases μ <;> rfl
/-- The columns of a part do not depend on the part. -/
theorem kF_setPart (μ : MatName) (p : ℕ) : S.kF (μ.setPart p) = S.kF μ := by cases μ <;> rfl
/-- What a matrix holds does not depend on the part. -/
theorem n_setPart (μ : MatName) (p : ℕ) : S.n (μ.setPart p) = S.n μ := by cases μ <;> rfl

/-- For p below the number of parts, the name of part p has the part's number p. -/
theorem part_setPart {μ : MatName} {p : ℕ} (h : p < S.np μ) : (μ.setPart p).part = p := by
  cases μ <;> first | rfl | (have h1 : p < 1 := h; show 0 = p; omega)

/-- A name is the name of its own part. -/
theorem setPart_part (μ : MatName) : μ.setPart μ.part = μ := by cases μ <;> rfl

/-- "nameOfFeat" does not depend on the part in the matrix's name. -/
theorem nameOfFeat_setPart (σ : Seg) (μ : MatName) (p φ i : ℕ) :
    S.nameOfFeat σ (μ.setPart p) φ i = S.nameOfFeat σ μ φ i := by
  cases σ <;> cases μ <;> rfl

variable {S}

/-- Under "OK" a column of a matrix of features holds a feature. -/
theorem wc_pos (h : S.OK) {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) : 0 < S.wc μ := by
  cases σ <;> cases μ <;>
    first
      | exact Bool.noConfusion hf
      | exact h.wcaf | exact h.wcad | exact h.wcar | exact h.wcq | exact h.wcx | exact h.wch
      | exact h.wco | exact h.wchf | exact h.wchd | exact h.wchr

/-- Under "OK" a matrix of features has a part. -/
theorem np_pos (h : S.OK) {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) : 0 < S.np μ := by
  cases σ <;> cases μ <;>
    first
      | exact Bool.noConfusion hf
      | exact h.NAf | exact h.NAd | exact h.NHf | exact Nat.one_pos

/-- The columns of a part of a matrix of features: the features in use, by the parts times the
features in a column, rounded up. -/
theorem kF_eq {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) :
    S.kF μ = ceilDiv (S.n μ) (S.np μ * S.wc μ) := by
  cases σ <;> cases μ <;> first | exact Bool.noConfusion hf | rfl

/-- In a segment of the proof, part p of a matrix of features has a number in the list, for p below
the number of parts. -/
theorem mu_feat {σ : Seg} {μ : MatName} (hσ : σ.Below S.nGr) (hf : isFeat σ μ = true) {p : ℕ}
    (hp : p < S.np μ) : (S.mu σ (μ.setPart p)).isSome = true := by
  unfold Sz.mu
  rw [if_pos hσ]
  cases σ <;> cases μ <;>
    first
      | exact Bool.noConfusion hf
      | rfl
      | (simp only [MatName.setPart, MatName.no?, Sz.np] at hp ⊢; simp [hp])

/-- In a segment of the proof, part p of a matrix of features, for p below the number of parts, has
wc 2^lt rows and "kF" columns. -/
theorem shape_feat {σ : Seg} {μ : MatName} (hσ : σ.Below S.nGr) (hf : isFeat σ μ = true) {p : ℕ}
    (hp : p < S.np μ) : S.shape σ (μ.setPart p) = (S.wc μ * 2 ^ S.lt, S.kF μ) := by
  unfold Sz.shape
  rw [if_pos (mu_feat hσ hf hp)]
  cases σ <;> cases μ <;> first | exact Bool.noConfusion hf | rfl

/-- Under "OK", a feature in use of a matrix of features lies in a part below the number of parts
and in a column below the columns of a part. -/
theorem part_lt (h : S.OK) {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) {φ : ℕ}
    (hφ : φ < S.n μ) : φ / S.wc μ / S.kF μ < S.np μ ∧ φ / S.wc μ % S.kF μ < S.kF μ := by
  have hpc := part_col_lt (np_pos h hf) (wc_pos h hf) hφ
  rw [← kF_eq hf] at hpc
  exact hpc

/-- Under "OK", in a segment of the proof: the cell of a feature in use at a position below 2^lt
lies inside the shape of its part. -/
theorem atFeat_inShape (h : S.OK) {σ : Seg} {μ : MatName} (hσ : σ.Below S.nGr)
    (hf : isFeat σ μ = true) {φ i : ℕ} (hφ : φ < S.n μ) (hi : i < 2 ^ S.lt) :
    (S.atFeat σ μ φ i).2.2.1 < (S.shape (S.atFeat σ μ φ i).1 (S.atFeat σ μ φ i).2.1).1 ∧
      (S.atFeat σ μ φ i).2.2.2 < (S.shape (S.atFeat σ μ φ i).1 (S.atFeat σ μ φ i).2.1).2 := by
  have hw := wc_pos h hf
  have hpc := part_col_lt (np_pos h hf) hw hφ
  rw [← kF_eq hf] at hpc
  show φ % S.wc μ * 2 ^ S.lt + i < (S.shape σ (μ.setPart (φ / S.wc μ / S.kF μ))).1 ∧
    φ / S.wc μ % S.kF μ < (S.shape σ (μ.setPart (φ / S.wc μ / S.kF μ))).2
  rw [shape_feat hσ hf hpc.1]
  exact ⟨row_lt hw hi, hpc.2⟩

/-- Under "OK": at the place of a feature in use at a position below 2^lt, "featOf" returns the
feature and the position. -/
theorem featOf_atFeat (h : S.OK) {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) {φ i : ℕ}
    (hφ : φ < S.n μ) (hi : i < 2 ^ S.lt) :
    S.featOf (S.atFeat σ μ φ i).2.1 (S.atFeat σ μ φ i).2.2.1 (S.atFeat σ μ φ i).2.2.2 =
      (φ, i) := by
  have hpc := part_col_lt (np_pos h hf) (wc_pos h hf) hφ
  rw [← kF_eq hf] at hpc
  show (((μ.setPart (φ / S.wc μ / S.kF μ)).part * S.kF (μ.setPart (φ / S.wc μ / S.kF μ)) +
      φ / S.wc μ % S.kF μ) * S.wc (μ.setPart (φ / S.wc μ / S.kF μ)) +
      (φ % S.wc μ * 2 ^ S.lt + i) / 2 ^ S.lt, (φ % S.wc μ * 2 ^ S.lt + i) % 2 ^ S.lt) = (φ, i)
  rw [S.part_setPart hpc.1, S.kF_setPart, S.wc_setPart, mulAdd_div hi, mulAdd_mod hi,
    Nat.div_add_mod', Nat.div_add_mod']

/-- At a row below wc 2^lt and a column below the columns of a part, the feature and position that
"featOf" returns have that very place. -/
theorem atFeat_featOf (σ : Seg) (μ : MatName) {r c : ℕ} (hr : r < S.wc μ * 2 ^ S.lt)
    (hc : c < S.kF μ) :
    S.atFeat σ μ (S.featOf μ r c).1 (S.featOf μ r c).2 = (σ, μ, r, c) := by
  have hT : 0 < 2 ^ S.lt := Nat.two_pow_pos _
  have h1 : r / 2 ^ S.lt < S.wc μ := (Nat.div_lt_iff_lt_mul hT).2 hr
  show (σ, μ.setPart (((μ.part * S.kF μ + c) * S.wc μ + r / 2 ^ S.lt) / S.wc μ / S.kF μ),
    ((μ.part * S.kF μ + c) * S.wc μ + r / 2 ^ S.lt) % S.wc μ * 2 ^ S.lt + r % 2 ^ S.lt,
    ((μ.part * S.kF μ + c) * S.wc μ + r / 2 ^ S.lt) / S.wc μ % S.kF μ) = (σ, μ, r, c)
  rw [mulAdd_div h1, mulAdd_mod h1, mulAdd_div hc, mulAdd_mod hc, setPart_part,
    Nat.div_add_mod']

end Sz

/-! ## The decoders -/

section Decoders
open Inst.Model.FFSeg.IndexFacts (feat_in mem_arrs mx_of_mem offL_disj OFF_eq)
open Inst.Model.AttSeg.AddrFacts (mr_dec mr_lt)

/-- "ffName" finds a valid cell of a feed-forward segment by its matrix, its feature and its
position. -/
theorem ffName_feat (D : FFSeg.Dim) (c : FFSeg.Cell) (hc : c.Valid D) :
    ffName D c.X.mx (FFSeg.feat D c.X c.k c.inst c.j) c.i = some c := by
  obtain ⟨X, k, inst, j, i⟩ := c
  obtain ⟨hk, hin, hj, -⟩ := hc
  simp only at hk hin hj ⊢
  have hr := feat_in D hk hin hj
  have hfind : (FFSeg.arrs X.mx).find? (fun Y =>
      decide (FFSeg.OFF D Y ≤ FFSeg.feat D X k inst j ∧
        FFSeg.feat D X k inst j < FFSeg.OFF D Y + Y.nFeat D)) = some X := by
    cases hX : (FFSeg.arrs X.mx).find? (fun Y =>
      decide (FFSeg.OFF D Y ≤ FFSeg.feat D X k inst j ∧
        FFSeg.feat D X k inst j < FFSeg.OFF D Y + Y.nFeat D)) with
    | none =>
      have h1 := List.find?_eq_none.1 hX X (mem_arrs X)
      exact absurd (decide_eq_true hr) h1
    | some Y =>
      have h1 := List.find?_some hX
      simp only [decide_eq_true_eq] at h1
      have h2 : Y ∈ FFSeg.arrs X.mx := List.mem_of_find?_eq_some hX
      by_cases hne : X = Y
      · rw [hne]
      · exfalso
        have e2 : FFSeg.OFF D Y =
            FFSeg.IndexFacts.offL (FFSeg.Arr.nFeat D) (FFSeg.arrs X.mx) Y := by
          rw [OFF_eq, mx_of_mem _ _ h2]
        rcases offL_disj (FFSeg.Arr.nFeat D) (mem_arrs X) h2 hne with h3 | h3
        · rw [← OFF_eq, ← e2] at h3
          omega
        · rw [← OFF_eq, ← e2] at h3
          omega
  unfold ffName
  rw [hfind]
  have e : FFSeg.feat D X k inst j - FFSeg.OFF D X = (k * X.cnt D + inst) * X.width D + j := by
    unfold FFSeg.feat
    omega
  simp only [Option.map_some, e, mulAdd_div hj, mulAdd_mod hj, mulAdd_div hin, mulAdd_mod hin]

/-- What "ffName" returns at a position below the number of positions is a valid cell of that
matrix, with that feature and that position. -/
theorem ffName_back (D : FFSeg.Dim) {μ : FFSeg.Mx} {φ i : ℕ} {c : FFSeg.Cell}
    (e : ffName D μ φ i = some c) (hi : i < D.T) :
    c.Valid D ∧ c.X.mx = μ ∧ FFSeg.feat D c.X c.k c.inst c.j = φ ∧ c.i = i := by
  unfold ffName at e
  obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 e
  have h0 := List.find?_some hX
  simp only [decide_eq_true_eq] at h0
  obtain ⟨h1, h2⟩ := h0
  have hm := mx_of_mem _ _ (List.mem_of_find?_eq_some hX)
  obtain ⟨ψ, rfl⟩ : ∃ ψ, φ = FFSeg.OFF D X + ψ := ⟨φ - FFSeg.OFF D X, by omega⟩
  have hψ : ψ < X.nCell * X.cnt D * X.width D := by
    unfold FFSeg.Arr.nFeat at h2
    omega
  have ew : FFSeg.OFF D X + ψ - FFSeg.OFF D X = ψ := by omega
  simp only [ew]
  have hw : 0 < X.width D := by
    rcases Nat.eq_zero_or_pos (X.width D) with h | h
    · rw [h, Nat.mul_zero] at hψ
      exact absurd hψ (Nat.not_lt_zero _)
    · exact h
  have h3 : ψ / X.width D < X.nCell * X.cnt D := (Nat.div_lt_iff_lt_mul hw).2 hψ
  have hc : 0 < X.cnt D := by
    rcases Nat.eq_zero_or_pos (X.cnt D) with h | h
    · rw [h, Nat.mul_zero] at h3
      exact absurd h3 (Nat.not_lt_zero _)
    · exact h
  refine ⟨⟨(Nat.div_lt_iff_lt_mul hc).2 h3, Nat.mod_lt _ hc, Nat.mod_lt _ hw, hi⟩, hm, ?_, trivial⟩
  show FFSeg.OFF D X + (ψ / X.width D / X.cnt D * X.cnt D + ψ / X.width D % X.cnt D) * X.width D +
    ψ % X.width D = FFSeg.OFF D X + ψ
  rw [Nat.div_add_mod', Nat.add_assoc, Nat.div_add_mod']

variable (D : AttSeg.Dim)

/-- For a layer lam and a query head h in range, "bOf" and "gOf" are in range and give lam and h
back. -/
theorem bg_formula {lam h : ℕ} (hl : lam < D.nl) (hh : h < D.nH) :
    bOf D lam h < D.nb ∧ gOf D h < D.nG ∧ D.lamOf (bOf D lam h) = lam ∧
      D.head (gOf D h) (bOf D lam h) = h := by
  unfold AttSeg.Dim.nH at hh
  rw [Nat.mul_comm] at hh
  obtain ⟨h1, h2, h3⟩ := mr_dec hh
  have hna : 0 < D.na := Nat.lt_of_le_of_lt (Nat.zero_le _) h2
  unfold bOf gOf
  refine ⟨?_, h1, ?_, ?_⟩
  · unfold AttSeg.Dim.nb
    rw [Nat.mul_comm D.nl]
    exact mr_lt hl h2
  · unfold AttSeg.Dim.lamOf
    rw [Nat.mul_add_div hna, Nat.div_eq_of_lt h2, Nat.add_zero]
  · unfold AttSeg.Dim.head AttSeg.Dim.aOf
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2, h3]

/-- Below nH nl m, the library's number "fK" of (limb, pair, head of keys and values) is undone by
division: the three are in range and have the number x. -/
theorem fK_formula {m x : ℕ} (hx : x < D.nH * (D.nl * m)) :
    x / D.nH / D.nl < m ∧ bOf D (x / D.nH % D.nl) (x % D.nH) < D.nb ∧ gOf D (x % D.nH) < D.nG ∧
      fK D (x / D.nH / D.nl) (bOf D (x / D.nH % D.nl) (x % D.nH)) (gOf D (x % D.nH)) = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  obtain ⟨b1, b2, b3, b4⟩ := bg_formula D h5 h2
  refine ⟨h4, b1, b2, ?_⟩
  unfold fK
  rw [b3, b4, h6, h3]

/-- Below nH lT nl, the library's number "fI" of (bit, pair, head of keys and values) is undone by
division: the three are in range and have the number x. -/
theorem fI_formula {x : ℕ} (hx : x < D.nH * (D.lT * D.nl)) :
    x / D.nH % D.lT < D.lT ∧ bOf D (x / D.nH / D.lT) (x % D.nH) < D.nb ∧
      gOf D (x % D.nH) < D.nG ∧
      fI D (x / D.nH % D.lT) (bOf D (x / D.nH / D.lT) (x % D.nH)) (gOf D (x % D.nH)) = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  obtain ⟨b1, b2, b3, b4⟩ := bg_formula D h4 h2
  refine ⟨h5, b1, b2, ?_⟩
  unfold fI
  rw [b3, b4, h6, h3]

/-- Below nH nl, the library's number "fL" of (pair, head of keys and values) is undone by division:
the two are in range and have the number x. -/
theorem fL_formula {x : ℕ} (hx : x < D.nH * D.nl) :
    bOf D (x / D.nH) (x % D.nH) < D.nb ∧ gOf D (x % D.nH) < D.nG ∧
      fL D (bOf D (x / D.nH) (x % D.nH)) (gOf D (x % D.nH)) = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨b1, b2, b3, b4⟩ := bg_formula D h1 h2
  refine ⟨b1, b2, ?_⟩
  unfold fL
  rw [b3, b4, h3]

/-- What a decoder of attention's features owes: a valid own name, no cell of an entry, of the
matrix μ, with the feature φ and the position i. -/
def GoodAt (μ : AttSeg.Mx) (φ i : ℕ) (c : AttSeg.Raw) : Prop :=
  c.Valid D ∧ ¬ IsC c ∧ c.Own = true ∧ mat c = μ ∧ phi D c = φ ∧ pos c = i

/-- At a position in range: below the number of features in use "ahName" returns a name that is
"GoodAt"; from that number on it returns "none". -/
theorem ahName_spec {φ i : ℕ} (hi : i < D.T) :
    (φ < Phi D .ah → ∃ c, ahName D φ i = some c ∧ GoodAt D .ah φ i c) ∧
      (¬ φ < Phi D .ah → ahName D φ i = none) := by
  have e4 : D.nH * (D.nl * 4) = 4 * S1 D := by unfold S1; ring
  unfold ahName
  constructor
  · intro hφ
    have hφ' : φ < 8 * S1 D + S2 D := hφ
    by_cases h1 : φ < 4 * S1 D
    · rw [if_pos h1]
      obtain ⟨a1, a2, a3, a4⟩ := fK_formula D (m := 4) (x := φ) (by rw [e4]; exact h1)
      exact ⟨_, rfl, ⟨a1, a2, a3, hi⟩, fun h => h, rfl, rfl, a4, rfl⟩
    · rw [if_neg h1]
      by_cases h2 : φ < 8 * S1 D
      · rw [if_pos h2]
        obtain ⟨a1, a2, a3, a4⟩ := fK_formula D (m := 4) (x := φ - 4 * S1 D) (by rw [e4]; omega)
        refine ⟨_, rfl, ⟨a1, a2, a3, hi⟩, fun h => h, rfl, rfl, ?_, rfl⟩
        show 4 * S1 D + fK D _ _ _ = φ
        rw [a4]
        omega
      · rw [if_neg h2, if_pos hφ']
        obtain ⟨a1, a2, a3, a4⟩ := fI_formula D (x := φ - 8 * S1 D)
          (by show φ - 8 * S1 D < S2 D; omega)
        refine ⟨_, rfl, ⟨a1, a2, a3, hi⟩, fun h => h, rfl, rfl, ?_, rfl⟩
        show 8 * S1 D + fI D _ _ _ = φ
        rw [a4]
        omega
  · intro hφ
    have hφ' : ¬ φ < 8 * S1 D + S2 D := hφ
    rw [if_neg (by omega), if_neg (by omega), if_neg hφ']

/-- At a position in range: below the number of features in use "aoName" returns a name that is
"GoodAt"; from that number on it returns "none". -/
theorem aoName_spec {φ i : ℕ} (hi : i < D.T) :
    (φ < Phi D .ao → ∃ c, aoName D φ i = some c ∧ GoodAt D .ao φ i c) ∧
      (¬ φ < Phi D .ao → aoName D φ i = none) := by
  unfold aoName
  constructor
  · intro hφ
    have hφ' : φ < 2 * S3 D := hφ
    by_cases h1 : φ < S3 D
    · rw [if_pos h1]
      obtain ⟨c1, c2, c3⟩ := mr_dec (show φ < D.ch * (D.nH * D.nl) from h1)
      obtain ⟨a1, a2, a3⟩ := fL_formula D c1
      refine ⟨_, rfl, ⟨a1, a2, hi, c2⟩, fun h => h, rfl, rfl, ?_, rfl⟩
      show D.ch * fL D _ _ + φ % D.ch = φ
      rw [a3, c3]
    · rw [if_neg h1, if_pos hφ']
      obtain ⟨c1, c2, c3⟩ := mr_dec (show φ - S3 D < D.ch * (D.nH * D.nl) by
        show φ - S3 D < S3 D; omega)
      obtain ⟨a1, a2, a3⟩ := fL_formula D c1
      refine ⟨_, rfl, ⟨a1, a2, hi, c2⟩, fun h => h, rfl, rfl, ?_, rfl⟩
      show S3 D + (D.ch * fL D _ _ + (φ - S3 D) % D.ch) = φ
      rw [a3, c3]
      omega
  · intro hφ
    have hφ' : ¬ φ < 2 * S3 D := hφ
    rw [if_neg (by omega), if_neg hφ']

/-- Below the number of cells in use "asName" returns a valid name whose number is A; from that
number on it returns "none". -/
theorem asName_spec {A : ℕ} :
    (A < SM D + SD D → ∃ ρ jj b x, asName D A = some (.c ρ jj b x) ∧
        (AttSeg.Raw.c ρ jj b x).Valid D ∧ adr D ρ jj b x = A) ∧
      (¬ A < SM D + SD D → asName D A = none) := by
  unfold asName
  constructor
  · intro hA
    by_cases h1 : A < SM D
    · rw [if_pos h1]
      obtain ⟨c1, c2, c3⟩ := mr_dec (show A < 2 ^ D.lM * (D.nb * 5) from h1)
      obtain ⟨d1, d2, d3⟩ := mr_dec c1
      refine ⟨.M, _, _, _, rfl, ⟨d1, d2, c2⟩, ?_⟩
      show 2 ^ D.lM * (D.nb * (A / 2 ^ D.lM / D.nb) + A / 2 ^ D.lM % D.nb) + A % 2 ^ D.lM = A
      rw [d3, c3]
    · rw [if_neg h1, if_pos hA]
      obtain ⟨c1, c2, c3⟩ := mr_dec (show A - SM D < 2 ^ D.lD * (D.nb * 5) by
        show A - SM D < SD D; omega)
      obtain ⟨d1, d2, d3⟩ := mr_dec c1
      refine ⟨.D, _, _, _, rfl, ⟨d1, d2, c2⟩, ?_⟩
      show SM D + (2 ^ D.lD * (D.nb * ((A - SM D) / 2 ^ D.lD / D.nb) +
        (A - SM D) / 2 ^ D.lD % D.nb) + (A - SM D) % 2 ^ D.lD) = A
      rw [d3, c3]
      omega
  · intro hA
    rw [if_neg (by omega), if_neg hA]

end Decoders

/-! ## The three sorts of place -/

section Core
open Inst.Model.FFSeg.IndexFacts (feat_lt mx_ne_b)
open Inst.Model.AttSeg.AddrFacts (phi_lt phi_inj adr_lt adr_inj)

namespace Sz
variable {S : Sz}

/-- Under "OK" attention's positions are 2^lt. -/
theorem DA_T (h : S.OK) : S.DA.T = 2 ^ S.lt := by
  rw [AttSeg.Dim.T_eq]
  have e : S.DA.lT = S.lt := by
    show S.lt - 1 - S.lB + 1 + S.lB = S.lt
    have := h.lB
    omega
  rw [e]

/-- What a matrix of a feed-forward segment holds is the library's number of its features. -/
theorem n_famOf (μ : FFSeg.Mx) : S.n (famOf μ) = FFSeg.nFeatMx S.DF μ := by cases μ <;> rfl

/-- The library's matrices of a feed-forward segment, but b, are matrices of features. -/
theorem isFeat_famOf (g : ℕ) {μ : FFSeg.Mx} (hμ : μ ≠ .b) : isFeat (.ff g) (famOf μ) = true := by
  cases μ <;> first | rfl | exact absurd rfl hμ

/-- "isFeat" does not depend on the part. -/
theorem isFeat_setPart (σ : Seg) (μ : MatName) (p : ℕ) :
    isFeat σ (μ.setPart p) = isFeat σ μ := by
  cases σ <;> cases μ <;> rfl

/-- "atFeat" does not depend on the part in the matrix's name. -/
theorem atFeat_setPart (σ : Seg) (μ : MatName) (p φ i : ℕ) :
    S.atFeat σ (μ.setPart p) φ i = S.atFeat σ μ φ i := by
  cases μ <;> rfl

/-- Inside the shape of a matrix of features, "nameAt" is "nameOfFeat" at the feature and position
of "featOf". -/
theorem nameAt_of_isFeat {σ : Seg} {μ : MatName} (hf : isFeat σ μ = true) {r c : ℕ}
    (hin : r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2) :
    S.nameAt σ μ r c = S.nameOfFeat σ μ (S.featOf μ r c).1 (S.featOf μ r c).2 := by
  unfold Sz.nameAt
  rw [if_pos hin]
  cases σ <;> cases μ <;> first | exact Bool.noConfusion hf | rfl

/-- Under "OK", in a segment of the proof: at the place of a feature in use at a position below
2^lt, "nameAt" is "nameOfFeat" of that feature and position. -/
theorem nameAt_atFeat (h : S.OK) {σ : Seg} {μ : MatName} (hσ : σ.Below S.nGr)
    (hf : isFeat σ μ = true) {φ i : ℕ} (hφ : φ < S.n μ) (hi : i < 2 ^ S.lt) :
    S.nameAt (S.atFeat σ μ φ i).1 (S.atFeat σ μ φ i).2.1 (S.atFeat σ μ φ i).2.2.1
      (S.atFeat σ μ φ i).2.2.2 = S.nameOfFeat σ μ φ i := by
  rw [nameAt_of_isFeat (by
    show isFeat σ (μ.setPart _) = true
    rw [isFeat_setPart]
    exact hf) (atFeat_inShape h hσ hf hφ hi), featOf_atFeat h hf hφ hi]
  exact S.nameOfFeat_setPart σ μ _ φ i

/-! ### the matrix as -/

/-- In a group below nGr, part p of as, for p < NAs, has 2^lmS rows and "kF" columns. -/
theorem shape_as {g p : ℕ} (hg : g < S.nGr) (hp : p < S.NAs) :
    S.shape (.att g) (.as p) = (2 ^ S.lmS, S.kF (.as 0)) := by
  have hm : (S.mu (.att g) (.as p)).isSome = true := by
    unfold Sz.mu
    rw [if_pos (show (Seg.att g).Below S.nGr from hg)]
    simp [MatName.no?, hp]
  unfold Sz.shape
  rw [if_pos hm]
  rfl

/-- Under "OK" a cell of as in use lies in a part below NAs and a column below the columns of a
part. -/
theorem atCell_lt (h : S.OK) {N : ℕ} (hN : N < SM S.DA + SD S.DA) :
    N / 2 ^ S.lmS / S.kF (.as 0) < S.NAs ∧ N / 2 ^ S.lmS % S.kF (.as 0) < S.kF (.as 0) :=
  part_col_lt h.NAs (Nat.two_pow_pos _) hN

/-- Under "OK", in a group below nGr, a cell of as in use lies inside the shape of its part. -/
theorem atCell_inShape (h : S.OK) {g N : ℕ} (hg : g < S.nGr) (hN : N < SM S.DA + SD S.DA) :
    (S.atCell g N).2.2.1 < (S.shape (S.atCell g N).1 (S.atCell g N).2.1).1 ∧
      (S.atCell g N).2.2.2 < (S.shape (S.atCell g N).1 (S.atCell g N).2.1).2 := by
  have hpc := atCell_lt h hN
  show N % 2 ^ S.lmS < (S.shape (.att g) (.as (N / 2 ^ S.lmS / S.kF (.as 0)))).1 ∧
    N / 2 ^ S.lmS % S.kF (.as 0) < (S.shape (.att g) (.as (N / 2 ^ S.lmS / S.kF (.as 0)))).2
  rw [shape_as hg hpc.1]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), hpc.2⟩

/-- At the place of cell number N of as, "cellOf" returns N. -/
theorem cellOf_atCell (g N : ℕ) :
    S.cellOf (S.atCell g N).2.1 (S.atCell g N).2.2.1 (S.atCell g N).2.2.2 = N := by
  show (N / 2 ^ S.lmS / S.kF (.as 0) * S.kF (.as 0) + N / 2 ^ S.lmS % S.kF (.as 0)) * 2 ^ S.lmS +
    N % 2 ^ S.lmS = N
  rw [Nat.div_add_mod', Nat.div_add_mod']

/-- At a row below 2^lmS and a column below the columns of a part, the cell whose number "cellOf"
returns has that very place. -/
theorem atCell_cellOf (g p : ℕ) {r c : ℕ} (hr : r < 2 ^ S.lmS) (hc : c < S.kF (.as 0)) :
    S.atCell g (S.cellOf (.as p) r c) = (.att g, .as p, r, c) := by
  show (Seg.att g, MatName.as (((p * S.kF (.as 0) + c) * 2 ^ S.lmS + r) / 2 ^ S.lmS /
      S.kF (.as 0)), ((p * S.kF (.as 0) + c) * 2 ^ S.lmS + r) % 2 ^ S.lmS,
    ((p * S.kF (.as 0) + c) * 2 ^ S.lmS + r) / 2 ^ S.lmS % S.kF (.as 0)) = _
  rw [mulAdd_div hr, mulAdd_mod hr, mulAdd_div hc, mulAdd_mod hc]

/-! ### the planes -/

/-- In a segment of the proof the matrix of planes has 2^lm rows and "kP" columns. -/
theorem shape_plane {σ : Seg} (hσ : σ.Below S.nGr) :
    S.shape σ (planeOf σ) = (2 ^ S.lmP σ, S.kP σ) := by
  have hm : (S.mu σ (planeOf σ)).isSome = true := by
    unfold Sz.mu
    rw [if_pos hσ]
    cases σ <;> rfl
  unfold Sz.shape
  rw [if_pos hm]
  cases σ <;> rfl

/-- Under "OK", in a segment of the proof, the matrix of planes has NC 2^kT 32 entries. -/
theorem kP_mul (h : S.OK) {σ : Seg} (hσ : σ.Below S.nGr) :
    S.kP σ * 2 ^ S.lmP σ = S.NC σ * 2 ^ S.kT σ * 32 := by
  unfold Sz.kP
  rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (h.planes σ hσ).2, pow_add, Nat.mul_assoc]
  norm_num

/-- For c < NC, t < K and j < 32 the number (c K + t) 32 + j is below NC K 32. -/
theorem bitNo_lt {NC K c t j : ℕ} (hc : c < NC) (ht : t < K) (hj : j < 32) :
    (c * K + t) * 32 + j < NC * K * 32 := by
  have h1 : (c + 1) * K ≤ NC * K := Nat.mul_le_mul_right _ hc
  have e : (c + 1) * K = c * K + K := by ring
  omega

/-- Under "OK", in a segment of the proof, the bit (t, c, j) with t < 2^kT, c < NC, j < 32 lies
inside the shape of the planes. -/
theorem atBit_inShape (h : S.OK) {σ : Seg} (hσ : σ.Below S.nGr) {t c j : ℕ}
    (ht : t < 2 ^ S.kT σ) (hc : c < S.NC σ) (hj : j < 32) :
    (S.atBit σ t c j).2.2.1 < (S.shape (S.atBit σ t c j).1 (S.atBit σ t c j).2.1).1 ∧
      (S.atBit σ t c j).2.2.2 < (S.shape (S.atBit σ t c j).1 (S.atBit σ t c j).2.1).2 := by
  show ((c * 2 ^ S.kT σ + t) * 32 + j) % 2 ^ S.lmP σ < (S.shape σ (planeOf σ)).1 ∧
    ((c * 2 ^ S.kT σ + t) * 32 + j) / 2 ^ S.lmP σ < (S.shape σ (planeOf σ)).2
  rw [shape_plane hσ]
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
  show _ / _ < S.kP σ
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), kP_mul h hσ]
  exact bitNo_lt hc ht hj

/-- For t < 2^kT and j < 32: at the row and column of the bit (t, c, j), "bitName" returns that bit.
-/
theorem bitName_atBit (σ : Seg) {t c j : ℕ} (ht : t < 2 ^ S.kT σ) (hj : j < 32) :
    S.bitName σ (S.atBit σ t c j).2.2.1 (S.atBit σ t c j).2.2.2 = .bit σ t c j := by
  have e : (S.atBit σ t c j).2.2.2 * 2 ^ S.lmP σ + (S.atBit σ t c j).2.2.1 =
      (c * 2 ^ S.kT σ + t) * 32 + j := Nat.div_add_mod' _ _
  unfold Sz.bitName
  rw [e, mulAdd_div hj, mulAdd_mod hj, mulAdd_div ht, mulAdd_mod ht]

/-- Under "OK", in a segment of the proof, at a row and column inside the planes' shape: the bit
that "bitName" returns is valid and has that very place. -/
theorem bitName_back (h : S.OK) {σ : Seg} (hσ : σ.Below S.nGr) {r c : ℕ}
    (hr : r < 2 ^ S.lmP σ) (hc : c < S.kP σ) :
    (S.bitName σ r c).Valid S ∧ (S.bitName σ r c).place S = (σ, planeOf σ, r, c) := by
  have hN : c * 2 ^ S.lmP σ + r < S.NC σ * 2 ^ S.kT σ * 32 := by
    rw [← kP_mul h hσ]
    have h1 : (c + 1) * 2 ^ S.lmP σ ≤ S.kP σ * 2 ^ S.lmP σ := Nat.mul_le_mul_right _ hc
    have e : (c + 1) * 2 ^ S.lmP σ = c * 2 ^ S.lmP σ + 2 ^ S.lmP σ := by ring
    omega
  generalize hNe : c * 2 ^ S.lmP σ + r = N at hN
  have h32 : N / 32 < S.NC σ * 2 ^ S.kT σ := (Nat.div_lt_iff_lt_mul (by norm_num)).2 hN
  have hK : 0 < 2 ^ S.kT σ := Nat.two_pow_pos _
  have eb : S.bitName σ r c = .bit σ (N / 32 % 2 ^ S.kT σ) (N / 32 / 2 ^ S.kT σ) (N % 32) := by
    unfold Sz.bitName
    rw [hNe]
  rw [eb]
  refine ⟨⟨hσ, Nat.mod_lt _ hK, (Nat.div_lt_iff_lt_mul hK).2 h32, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  show (σ, planeOf σ,
    ((N / 32 / 2 ^ S.kT σ * 2 ^ S.kT σ + N / 32 % 2 ^ S.kT σ) * 32 + N % 32) % 2 ^ S.lmP σ,
    ((N / 32 / 2 ^ S.kT σ * 2 ^ S.kT σ + N / 32 % 2 ^ S.kT σ) * 32 + N % 32) / 2 ^ S.lmP σ) = _
  rw [Nat.div_add_mod', Nat.div_add_mod', ← hNe, mulAdd_div hr, mulAdd_mod hr]

end Sz

end Core

/-! ## Names of features, there and back -/

section Back
open Inst.Model.FFSeg.IndexFacts (feat_lt mx_ne_b)
open Inst.Model.AttSeg.AddrFacts (phi_lt phi_inj adr_lt adr_inj)

variable {S : Sz}

/-- The one array of the library's matrix xin is x0. -/
theorem x0_of_xin {X : FFSeg.Arr} (h : X.mx = .xin) : X = .x0 := by
  cases X <;> first | rfl | exact FFSeg.Mx.noConfusion h

/-- In a feed-forward segment "nameOfFeat" is "ffName", for the library's matrices but b, and for
xin in group 0. -/
theorem nameOfFeat_famOf (g : ℕ) {μ : FFSeg.Mx} (hμ : μ ≠ .b) (hx : μ = .xin → g = 0) (φ i : ℕ) :
    S.nameOfFeat (.ff g) (famOf μ) φ i = (ffName S.DF μ φ i).map (.ff g) := by
  cases μ with
  | b => exact absurd rfl hμ
  | xin => exact if_pos (hx rfl)
  | af => rfl
  | ad => rfl
  | ar => rfl
  | qa => rfl
  | xout => rfl

/-- In a group below nGr, at a position below 2^lt, and for xin in group 0 alone: a cell that
"ffName" returns gives a valid name, whose place is that of the feature and position asked for. -/
theorem back_ff {g : ℕ} (hg : g < S.nGr) {μ : FFSeg.Mx} (hx : μ = .xin → g = 0) {φ i : ℕ}
    (hi : i < 2 ^ S.lt) {c : FFSeg.Cell} (e : ffName S.DF μ φ i = some c) :
    (Name.ff g c).Valid S ∧ (Name.ff g c).place S = S.atFeat (.ff g) (famOf μ) φ i := by
  obtain ⟨hv, hm, hf, hci⟩ := ffName_back S.DF e hi
  refine ⟨⟨hg, hv, fun h0 => hx (by rw [← hm, h0]; rfl)⟩, ?_⟩
  show S.atFeat (.ff g) (famOf c.X.mx) (FFSeg.feat S.DF c.X c.k c.inst c.j) c.i = _
  rw [hm, hf, hci]

/-- The position of a valid name of attention that is no cell of an entry is in range. -/
theorem pos_lt {D : AttSeg.Dim} {c : AttSeg.Raw} (hv : c.Valid D) (hc : ¬ IsC c) :
    pos c < D.T := by
  cases c with
  | c ρ jj b x => exact absurd trivial hc
  | mx k b g i => exact hv.2.2.2
  | den k b g i => exact hv.2.2.2
  | ib k b g i => exact hv.2.2.2
  | qh b g i n => exact hv.2.2.1
  | qh' b g i n => exact hv.2.2.1
  | qry k b g i n => exact hv.2.2.2.1
  | out k b g i n => exact hv.2.2.2.1
  | key k lam g j n => exact hv.2.2.2.1
  | val k lam g j n => exact hv.2.2.2.1

/-- An own name of attention that is no cell of an entry is laid in ah or in ao, by its matrix, at
the library's feature and position. -/
theorem place_att_feat (g : ℕ) {c : AttSeg.Raw} (hc : ¬ IsC c) (ho : c.Own = true) :
    (mat c = .ah ∧ (Name.att g c).place S = S.atFeat (.att g) .ah (phi S.DA c) (pos c)) ∨
      (mat c = .ao ∧ (Name.att g c).place S = S.atFeat (.att g) .ao (phi S.DA c) (pos c)) := by
  cases c <;>
    first
      | exact absurd trivial hc
      | exact Bool.noConfusion ho
      | exact Or.inl ⟨rfl, rfl⟩
      | exact Or.inr ⟨rfl, rfl⟩

/-- Under "OK", in a segment of the proof, at a position below 2^lt: a name that "nameOfFeat"
returns is valid, and its place is that of the feature and position asked for. -/
theorem nameOfFeat_back (h : S.OK) {σ : Seg} {μ : MatName} (hσ : σ.Below S.nGr)
    (hf : isFeat σ μ = true) {φ i : ℕ} (hi : i < 2 ^ S.lt) {n : Name}
    (e : S.nameOfFeat σ μ φ i = some n) : n.Valid S ∧ n.place S = S.atFeat σ μ φ i := by
  have hiA : i < S.DA.T := by rw [Sz.DA_T h]; exact hi
  have ff : ∀ (g : ℕ) (ν : FFSeg.Mx), g < S.nGr → (ν = .xin → g = 0) →
      (ffName S.DF ν φ i).map (Name.ff g) = some n →
      n.Valid S ∧ n.place S = S.atFeat (.ff g) (famOf ν) φ i := by
    intro g ν hg hx e
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 e
    exact back_ff hg hx hi hc
  have nx : ∀ {ν : FFSeg.Mx} {g : ℕ}, ν ≠ .xin → ν = .xin → g = 0 := fun h1 h2 => absurd h2 h1
  cases σ with
  | ff g =>
    cases μ with
    | af p => exact ff g .af hσ (nx (by decide)) e
    | ad p => exact ff g .ad hσ (nx (by decide)) e
    | ar => exact ff g .ar hσ (nx (by decide)) e
    | qa => exact ff g .qa hσ (nx (by decide)) e
    | xbO => exact ff g .xout hσ (nx (by decide)) e
    | xbI =>
      by_cases h0 : g = 0
      · exact ff g .xin hσ (fun _ => h0) (by rw [← e]; exact (if_pos h0).symm)
      · exact absurd ((if_neg h0).symm.trans e) (by simp)
    | _ => exact Bool.noConfusion hf
  | att g =>
    cases μ with
    | ah =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 e
      by_cases hφ : φ < Phi S.DA .ah
      · obtain ⟨c', hc', hv, hC, ho, hm, hp, hq⟩ := (ahName_spec S.DA hiA).1 hφ
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
        refine ⟨⟨hσ, hv, ho⟩, ?_⟩
        rcases place_att_feat (S := S) g hC ho with ⟨-, h2⟩ | ⟨h1, -⟩
        · rw [h2, hp, hq]
        · rw [hm] at h1
          exact AttSeg.Mx.noConfusion h1
      · rw [(ahName_spec S.DA hiA).2 hφ] at hc
        exact absurd hc (by simp)
    | ao =>
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 e
      by_cases hφ : φ < Phi S.DA .ao
      · obtain ⟨c', hc', hv, hC, ho, hm, hp, hq⟩ := (aoName_spec S.DA hiA).1 hφ
        obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
        refine ⟨⟨hσ, hv, ho⟩, ?_⟩
        rcases place_att_feat (S := S) g hC ho with ⟨h1, -⟩ | ⟨-, h2⟩
        · rw [hm] at h1
          exact AttSeg.Mx.noConfusion h1
        · rw [h2, hp, hq]
      · rw [(aoName_spec S.DA hiA).2 hφ] at hc
        exact absurd hc (by simp)
    | _ => exact Bool.noConfusion hf
  | head =>
    cases μ with
    | hf p =>
      by_cases hφ : φ < S.n (.hf p)
      · obtain rfl := Option.some.inj ((if_pos hφ).symm.trans e)
        exact ⟨⟨hφ, hi⟩, rfl⟩
      · exact absurd ((if_neg hφ).symm.trans e) (by simp)
    | hd =>
      by_cases hφ : φ < S.n .hd
      · obtain rfl := Option.some.inj ((if_pos hφ).symm.trans e)
        exact ⟨⟨hφ, hi⟩, rfl⟩
      · exact absurd ((if_neg hφ).symm.trans e) (by simp)
    | hr =>
      by_cases hφ : φ < S.n .hr
      · obtain rfl := Option.some.inj ((if_pos hφ).symm.trans e)
        exact ⟨⟨hφ, hi⟩, rfl⟩
      · exact absurd ((if_neg hφ).symm.trans e) (by simp)
    | _ => exact Bool.noConfusion hf

end Back

/-! ## The laws -/

section Final
open Inst.Model.FFSeg.IndexFacts (feat_lt mx_ne_b)
open Inst.Model.AttSeg.AddrFacts (phi_lt phi_inj adr_lt adr_inj)

/-- **In range.** Under "OK" the place of a valid name lies inside the shape of its matrix. So that
matrix is in the list of its segment, and the part exists. -/
theorem place_inShape (S : Sz) (h : S.OK) (n : Name) (hn : n.Valid S) :
    (n.place S).2.2.1 < (S.shape (n.place S).1 (n.place S).2.1).1 ∧
      (n.place S).2.2.2 < (S.shape (n.place S).1 (n.place S).2.1).2 := by
  cases n with
  | ff g c =>
    obtain ⟨hg, hv, -⟩ := hn
    exact Sz.atFeat_inShape h (σ := .ff g) hg (Sz.isFeat_famOf g (mx_ne_b c.X))
      (by rw [Sz.n_famOf]; exact feat_lt S.DF hv.1 hv.2.1 hv.2.2.1) hv.2.2.2
  | att g c =>
    obtain ⟨hg, hv, ho⟩ := hn
    by_cases hC : IsC c
    · cases c with
      | c ρ jj b x => exact Sz.atCell_inShape h hg (adr_lt S.DA hv)
      | _ => exact False.elim hC
    · have hp : pos c < 2 ^ S.lt := by rw [← Sz.DA_T h]; exact pos_lt hv hC
      have hφ := (phi_lt S.DA c hv hC).1
      rcases place_att_feat (S := S) g hC ho with ⟨hm, e⟩ | ⟨hm, e⟩
      · rw [e]
        exact Sz.atFeat_inShape h (σ := .att g) hg rfl (by rw [hm] at hφ; exact hφ) hp
      · rw [e]
        exact Sz.atFeat_inShape h (σ := .att g) hg rfl (by rw [hm] at hφ; exact hφ) hp
  | hf φ i => exact Sz.atFeat_inShape h (σ := .head) trivial rfl hn.1 hn.2
  | hd φ i => exact Sz.atFeat_inShape h (σ := .head) trivial rfl hn.1 hn.2
  | hr φ i => exact Sz.atFeat_inShape h (σ := .head) trivial rfl hn.1 hn.2
  | bit σ t c j => exact Sz.atBit_inShape h hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

/-- Inside the shape of a segment's planes "nameAt" is "bitName". -/
theorem nameAt_planeEq (S : Sz) {σ : Seg} {r c : ℕ}
    (hin : r < (S.shape σ (planeOf σ)).1 ∧ c < (S.shape σ (planeOf σ)).2) :
    S.nameAt σ (planeOf σ) r c = some (S.bitName σ r c) := by
  unfold Sz.nameAt
  rw [if_pos hin]
  cases σ <;> rfl

/-- **There and back.** Under "OK", asked at the place of a valid name, "nameAt" returns that name.
-/
theorem nameAt_place (S : Sz) (h : S.OK) (n : Name) (hn : n.Valid S) :
    S.nameAt (n.place S).1 (n.place S).2.1 (n.place S).2.2.1 (n.place S).2.2.2 = some n := by
  cases n with
  | ff g c =>
    obtain ⟨hg, hv, hx⟩ := hn
    refine (Sz.nameAt_atFeat h (σ := .ff g) hg (Sz.isFeat_famOf g (mx_ne_b c.X))
      (by rw [Sz.n_famOf]; exact feat_lt S.DF hv.1 hv.2.1 hv.2.2.1) hv.2.2.2).trans ?_
    rw [nameOfFeat_famOf g (mx_ne_b c.X) (fun hm => hx (x0_of_xin hm)), ffName_feat S.DF c hv]
    rfl
  | att g c =>
    obtain ⟨hg, hv, ho⟩ := hn
    by_cases hC : IsC c
    · cases c with
      | c ρ jj b x =>
        have hin := Sz.atCell_inShape h hg (adr_lt S.DA hv)
        show S.nameAt (S.atCell g (adr S.DA ρ jj b x)).1 (S.atCell g (adr S.DA ρ jj b x)).2.1
          (S.atCell g (adr S.DA ρ jj b x)).2.2.1 (S.atCell g (adr S.DA ρ jj b x)).2.2.2 = _
        unfold Sz.nameAt
        rw [if_pos hin]
        show (asName S.DA (S.cellOf (S.atCell g (adr S.DA ρ jj b x)).2.1
          (S.atCell g (adr S.DA ρ jj b x)).2.2.1 (S.atCell g (adr S.DA ρ jj b x)).2.2.2)).map
            (Name.att g) = _
        rw [Sz.cellOf_atCell]
        obtain ⟨ρ', jj', b', x', e, hv', ha⟩ := (asName_spec S.DA).1 (adr_lt S.DA hv)
        rw [e, adr_inj S.DA hv' hv ha]
        rfl
      | _ => exact False.elim hC
    · have hpT := pos_lt hv hC
      have hp : pos c < 2 ^ S.lt := by rw [← Sz.DA_T h]; exact hpT
      have hφ := (phi_lt S.DA c hv hC).1
      rcases place_att_feat (S := S) g hC ho with ⟨hm, e⟩ | ⟨hm, e⟩
      · rw [hm] at hφ
        rw [e, Sz.nameAt_atFeat h (σ := .att g) hg rfl hφ hp]
        obtain ⟨c', hc', hv', hC', -, hm', hp', hq'⟩ := (ahName_spec S.DA hpT).1 hφ
        show (ahName S.DA (phi S.DA c) (pos c)).map (Name.att g) = _
        rw [hc', phi_inj S.DA c' c hv' hv hC' hC (hm'.trans hm.symm) hp' hq']
        rfl
      · rw [hm] at hφ
        rw [e, Sz.nameAt_atFeat h (σ := .att g) hg rfl hφ hp]
        obtain ⟨c', hc', hv', hC', -, hm', hp', hq'⟩ := (aoName_spec S.DA hpT).1 hφ
        show (aoName S.DA (phi S.DA c) (pos c)).map (Name.att g) = _
        rw [hc', phi_inj S.DA c' c hv' hv hC' hC (hm'.trans hm.symm) hp' hq']
        rfl
  | hf φ i =>
    exact (Sz.nameAt_atFeat h (σ := .head) trivial rfl hn.1 hn.2).trans (if_pos hn.1)
  | hd φ i =>
    exact (Sz.nameAt_atFeat h (σ := .head) trivial rfl hn.1 hn.2).trans (if_pos hn.1)
  | hr φ i =>
    exact (Sz.nameAt_atFeat h (σ := .head) trivial rfl hn.1 hn.2).trans (if_pos hn.1)
  | bit σ t c j =>
    refine (nameAt_planeEq S (Sz.atBit_inShape h hn.1 hn.2.1 hn.2.2.1 hn.2.2.2)).trans ?_
    exact congrArg some (Sz.bitName_atBit σ hn.2.1 hn.2.2.2)

/-- Under "OK" two valid names with one place are one name. -/
theorem place_inj (S : Sz) (h : S.OK) (n n' : Name) (hn : n.Valid S) (hn' : n'.Valid S)
    (e : n.place S = n'.place S) : n = n' :=
  Option.some.inj (by rw [← nameAt_place S h n hn, e, nameAt_place S h n' hn'])

/-- In a group below nGr, at a row below 2^lmS and a column below the columns of a part: a name that
"asName" returns at the cell's number is valid and has that very place. -/
theorem back_as {S : Sz} {g p r c : ℕ} (hg : g < S.nGr) (hr : r < 2 ^ S.lmS)
    (hc : c < S.kF (.as 0)) {n : Name}
    (e : (asName S.DA (S.cellOf (.as p) r c)).map (Name.att g) = some n) :
    n.Valid S ∧ n.place S = (.att g, .as p, r, c) := by
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 e
  by_cases hA : S.cellOf (.as p) r c < SM S.DA + SD S.DA
  · obtain ⟨ρ, jj, b, x, e1, hv, ha⟩ := (asName_spec S.DA).1 hA
    obtain rfl : AttSeg.Raw.c ρ jj b x = c0 := Option.some.inj (e1.symm.trans hc0)
    refine ⟨⟨hg, hv, rfl⟩, ?_⟩
    show S.atCell g (adr S.DA ρ jj b x) = _
    rw [ha]
    exact Sz.atCell_cellOf g p hr hc
  · rw [(asName_spec S.DA).2 hA] at hc0
    exact absurd hc0 (by simp)

/-- **Back and there.** Under "OK", a name that "nameAt" returns at a segment, matrix, row and
column is valid, and its place is that very quadruple. -/
theorem nameAt_back (S : Sz) (h : S.OK) (σ : Seg) (μ : MatName) (r c : ℕ) (n : Name)
    (e : S.nameAt σ μ r c = some n) : n.Valid S ∧ n.place S = (σ, μ, r, c) := by
  by_cases hin : r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2
  swap
  · unfold Sz.nameAt at e
    rw [if_neg hin] at e
    exact absurd e (by simp)
  have hm : (S.mu σ μ).isSome = true := by
    by_contra hm
    have e0 : S.shape σ μ = (0, 0) := if_neg hm
    rw [e0] at hin
    exact absurd hin.1 (Nat.not_lt_zero _)
  have hσ : σ.Below S.nGr := by
    by_contra hb
    unfold Sz.mu at hm
    rw [if_neg hb] at hm
    exact absurd hm (by simp)
  have hs : S.shape σ μ = (S.rows μ, S.k σ μ) := if_pos hm
  by_cases hf : isFeat σ μ = true
  · have e' := (Sz.nameAt_of_isFeat hf hin).symm.trans e
    have hrw : S.rows μ = S.wc μ * 2 ^ S.lt ∧ S.k σ μ = S.kF μ := by
      cases σ <;> cases μ <;> first | exact Bool.noConfusion hf | exact ⟨rfl, rfl⟩
    rw [hs] at hin
    obtain ⟨hv, hp⟩ := nameOfFeat_back h hσ hf (Nat.mod_lt _ (Nat.two_pow_pos _)) e'
    exact ⟨hv, hp.trans (Sz.atFeat_featOf σ μ (hrw.1 ▸ hin.1) (hrw.2 ▸ hin.2))⟩
  · unfold Sz.nameAt at e
    rw [if_pos hin] at e
    rw [hs] at hin
    cases σ with
    | ff g =>
      cases μ with
      | b =>
        obtain rfl := Option.some.inj e
        exact Sz.bitName_back h hσ hin.1 hin.2
      | af p => exact absurd rfl hf
      | ad p => exact absurd rfl hf
      | ar => exact absurd rfl hf
      | qa => exact absurd rfl hf
      | xbO => exact absurd rfl hf
      | xbI => exact absurd rfl hf
      | _ => exact absurd hm (by simp [Sz.mu, MatName.no?])
    | att g =>
      cases μ with
      | as p => exact back_as hσ hin.1 hin.2 e
      | bA =>
        obtain rfl := Option.some.inj e
        exact Sz.bitName_back h hσ hin.1 hin.2
      | qa =>
        have e' : (none : Option Name) = some n := e
        exact absurd e' (by simp)
      | ah => exact absurd rfl hf
      | ao => exact absurd rfl hf
      | _ => exact absurd hm (by simp [Sz.mu, MatName.no?])
    | head =>
      cases μ with
      | bH =>
        obtain rfl := Option.some.inj e
        exact Sz.bitName_back h hσ hin.1 hin.2
      | xbL =>
        have e' : (none : Option Name) = some n := e
        exact absurd e' (by simp)
      | hf p => exact absurd rfl hf
      | hd => exact absurd rfl hf
      | hr => exact absurd rfl hf
      | _ => exact absurd hm (by simp [Sz.mu, MatName.no?])

/-- The planes have no padding: at every row and column inside the shape of a segment's matrix of
planes "nameAt" returns a bit's name. No premise on the numbers. -/
theorem nameAt_plane (S : Sz) (σ : Seg) (r c : ℕ)
    (hr : r < (S.shape σ (planeOf σ)).1) (hc : c < (S.shape σ (planeOf σ)).2) :
    ∃ t cc j, S.nameAt σ (planeOf σ) r c = some (.bit σ t cc j) :=
  ⟨_, _, _, nameAt_planeEq S ⟨hr, hc⟩⟩

/-- A matrix of a feed-forward segment is its own owner; xbI in group 0. -/
theorem owner_famOf (S : Sz) (g : ℕ) (μ : FFSeg.Mx) (p : ℕ) (hx : μ = .xin → g = 0) :
    S.owner (.ff g) ((famOf μ).setPart p) = (.ff g, (famOf μ).setPart p) := by
  cases μ with
  | xin => exact if_pos (hx rfl)
  | _ => rfl

/-- The matrix in which a valid name is laid is its own owner. -/
theorem owner_place (S : Sz) (n : Name) (hn : n.Valid S) :
    S.owner (n.place S).1 (n.place S).2.1 = ((n.place S).1, (n.place S).2.1) := by
  cases n with
  | ff g c => exact owner_famOf S g c.X.mx _ (fun hm => hn.2.2 (x0_of_xin hm))
  | att g c =>
    by_cases hC : IsC c
    · cases c with
      | c ρ jj b x => rfl
      | _ => exact False.elim hC
    · rcases place_att_feat (S := S) g hC hn.2.2 with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> rfl
  | hf φ i => rfl
  | hd φ i => rfl
  | hr φ i => rfl
  | bit σ t c j => cases σ <;> rfl

/-- Under "OK" the laid matrices hold at the place of a valid name the cell of that name. -/
theorem lay_place (S : Sz) (h : S.OK) (X : Src) (n : Name) (hn : n.Valid S) :
    lay S X (n.place S).1 (n.place S).2.1 (n.place S).2.2.1 (n.place S).2.2.2 = X.get n := by
  unfold lay
  rw [if_pos (place_inShape S h n hn), owner_place S n hn]
  show (match S.nameAt (n.place S).1 (n.place S).2.1 (n.place S).2.2.1 (n.place S).2.2.2 with
    | some m => X.get m
    | none => 0) = _
  rw [nameAt_place S h n hn]

/-- The laid matrices are 0 at any row or column that is not inside the shape. No premise on the
numbers. -/
theorem lay_off (S : Sz) (X : Src) (σ : Seg) (μ : MatName) (r c : ℕ)
    (ho : ¬ (r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2)) : lay S X σ μ r c = 0 :=
  if_neg ho

/-- A segment in whose list a matrix has a number is a segment of the proof. -/
theorem below_of_mu {S : Sz} {σ : Seg} {μ : MatName} (hM : (S.mu σ μ).isSome = true) :
    σ.Below S.nGr := by
  by_contra hb
  unfold Sz.mu at hM
  rw [if_neg hb] at hM
  exact absurd hM (by simp)

/-- Under "OK" a matrix that has a number in the list of a segment has the shape of its owner's
matrix. It says something at qa of attention, at xbI from group 1 on and at xbL; elsewhere both
sides are one term. -/
theorem shape_owner (S : Sz) (h : S.OK) (σ : Seg) (μ : MatName)
    (hM : (S.mu σ μ).isSome = true) :
    S.shape (S.owner σ μ).1 (S.owner σ μ).2 = S.shape σ μ := by
  have hσ := below_of_mu hM
  have hs : S.shape σ μ = (S.rows μ, S.k σ μ) := if_pos hM
  cases σ with
  | ff g =>
    cases μ with
    | xbI =>
      by_cases h0 : g = 0
      · rw [show S.owner (.ff g) .xbI = (.ff g, .xbI) from if_pos h0]
      · rw [show S.owner (.ff g) .xbI = (.ff (g - 1), .xbO) from if_neg h0, hs]
        have hg : g < S.nGr := hσ
        exact Sz.shape_feat (S := S) (σ := .ff (g - 1)) (μ := .xbO) (p := 0)
          (show g - 1 < S.nGr by omega) rfl Nat.one_pos
    | _ => rfl
  | att g =>
    cases μ with
    | qa =>
      rw [hs]
      exact Sz.shape_feat (S := S) (σ := .ff g) (μ := .qa) (p := 0) hσ rfl Nat.one_pos
    | _ => rfl
  | head =>
    cases μ with
    | xbL =>
      rw [hs]
      have := h.nGr
      exact Sz.shape_feat (S := S) (σ := .ff (S.nGr - 1)) (μ := .xbO) (p := 0)
        (show S.nGr - 1 < S.nGr by omega) rfl Nat.one_pos
    | _ => rfl

/-- An owner is its own owner. -/
theorem owner_owner (S : Sz) (σ : Seg) (μ : MatName) :
    S.owner (S.owner σ μ).1 (S.owner σ μ).2 = S.owner σ μ := by
  cases σ with
  | ff g =>
    cases μ with
    | xbI =>
      by_cases h0 : g = 0
      · have e : S.owner (.ff g) .xbI = (.ff g, .xbI) := if_pos h0
        rw [e]
        exact e
      · rw [show S.owner (.ff g) .xbI = (.ff (g - 1), .xbO) from if_neg h0]
        rfl
    | _ => rfl
  | att g => cases μ <;> rfl
  | head => cases μ <;> rfl

/-- **A borrowed matrix is its owner's.** Under "OK", at a segment of the proof, the laid matrix
under a reader's name is the laid matrix under its owner's name, at all rows and columns. -/
theorem lay_owner (S : Sz) (h : S.OK) (X : Src) (σ : Seg) (hσ : σ.Below S.nGr) (μ : MatName) :
    lay S X σ μ = lay S X (S.owner σ μ).1 (S.owner σ μ).2 := by
  by_cases hM : (S.mu σ μ).isSome = true
  · funext r c
    unfold lay
    rw [shape_owner S h σ μ hM, owner_owner]
  · have e : S.owner σ μ = (σ, μ) := by
      unfold Sz.mu at hM
      rw [if_pos hσ] at hM
      cases σ <;> cases μ <;> first | rfl | exact absurd rfl hM
    rw [e]

/-- Under "OK" and for 0 ≤ B: if the cell of every valid name is at most B in absolute value, so is
every entry of the laid matrices. -/
theorem lay_small (S : Sz) (X : Src) (B : ℤ) (hB : 0 ≤ B)
    (hX : ∀ n : Name, n.Valid S → |X.get n| ≤ B) (h : S.OK) (σ : Seg) (μ : MatName) (r c : ℕ) :
    |lay S X σ μ r c| ≤ B := by
  unfold lay
  by_cases hin : r < (S.shape σ μ).1 ∧ c < (S.shape σ μ).2
  · rw [if_pos hin]
    cases hN : S.nameAt (S.owner σ μ).1 (S.owner σ μ).2 r c with
    | some m => exact hX m (nameAt_back S h _ _ _ _ m hN).1
    | none => simpa using hB
  · rw [if_neg hin]
    simpa using hB

end Final

/-! ## Padding -/

section Padding
open Inst.Model.FFSeg.IndexFacts (offL offL_cons_self offL_cons_ne offL_add_le OFF_eq mx_of_mem)

/-- The ranges of the items of a list without repeats tile the numbers below the sum of their sizes.
-/
theorem ranges_tile {α : Type} [DecidableEq α] (g : α → ℕ) :
    ∀ {l : List α}, l.Nodup → ∀ {φ : ℕ}, φ < (l.map g).sum →
      ∃ X ∈ l, offL g l X ≤ φ ∧ φ < offL g l X + g X
  | [], _, φ, h => absurd h (by simp)
  | a :: l, hn, φ, h => by
    rw [List.map_cons, List.sum_cons] at h
    by_cases h1 : φ < g a
    · exact ⟨a, List.mem_cons_self, by rw [offL_cons_self]; omega, by rw [offL_cons_self]; omega⟩
    · obtain ⟨X, hX, h2, h3⟩ := ranges_tile g (List.nodup_cons.1 hn).2 (φ := φ - g a) (by omega)
      have hne : a ≠ X := fun e => (List.nodup_cons.1 hn).1 (e ▸ hX)
      exact ⟨X, List.mem_cons_of_mem _ hX, by rw [offL_cons_ne g l hne]; omega,
        by rw [offL_cons_ne g l hne]; omega⟩

/-- The library's list of the arrays of a matrix has no repeats. -/
theorem arrs_nodup (μ : FFSeg.Mx) : (FFSeg.arrs μ).Nodup := by cases μ <;> decide

/-- "ffName" returns "none" exactly from the matrix's number of features in use on. -/
theorem ffName_none_iff (D : FFSeg.Dim) (μ : FFSeg.Mx) (φ i : ℕ) :
    ffName D μ φ i = none ↔ FFSeg.nFeatMx D μ ≤ φ := by
  unfold ffName
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h
    by_contra hlt
    obtain ⟨X, hX, h1, h2⟩ := ranges_tile (FFSeg.Arr.nFeat D) (arrs_nodup μ) (φ := φ)
      (show φ < ((FFSeg.arrs μ).map (FFSeg.Arr.nFeat D)).sum from Nat.lt_of_not_le hlt)
    have e : FFSeg.OFF D X = offL (FFSeg.Arr.nFeat D) (FFSeg.arrs μ) X := by
      rw [OFF_eq, mx_of_mem _ _ hX]
    exact h X hX (decide_eq_true (by rw [e]; exact ⟨h1, h2⟩))
  · intro h X hX hd
    have hd' := of_decide_eq_true hd
    have e : FFSeg.OFF D X = offL (FFSeg.Arr.nFeat D) (FFSeg.arrs μ) X := by
      rw [OFF_eq, mx_of_mem _ _ hX]
    have h3 : offL (FFSeg.Arr.nFeat D) (FFSeg.arrs μ) X + X.nFeat D ≤ FFSeg.nFeatMx D μ :=
      offL_add_le (FFSeg.Arr.nFeat D) hX
    rw [e] at hd'
    omega

/-- σ owns the matrix of features μ: as "isFeat", with xbI in group 0 alone. -/
def ownsFeat : Seg → MatName → Bool
  | .ff g, .xbI => g == 0
  | σ, μ => isFeat σ μ

/-- Under "OK", in a matrix of features that its segment owns, at a position below 2^lt:
"nameOfFeat" returns "none" exactly at a feature that is not in use. -/
theorem nameOfFeat_none_iff {S : Sz} (h : S.OK) {σ : Seg} {μ : MatName}
    (ho : ownsFeat σ μ = true) {φ i : ℕ} (hi : i < 2 ^ S.lt) :
    S.nameOfFeat σ μ φ i = none ↔ S.n μ ≤ φ := by
  have hiA : i < S.DA.T := by rw [Sz.DA_T h]; exact hi
  have ff : ∀ (g : ℕ) (ν : FFSeg.Mx),
      (ffName S.DF ν φ i).map (Name.ff g) = none ↔ FFSeg.nFeatMx S.DF ν ≤ φ := fun g ν => by
    rw [Option.map_eq_none_iff]
    exact ffName_none_iff S.DF ν φ i
  cases σ with
  | ff g =>
    cases μ with
    | af p => exact ff g .af
    | ad p => exact ff g .ad
    | ar => exact ff g .ar
    | qa => exact ff g .qa
    | xbO => exact ff g .xout
    | xbI =>
      have h0 : g = 0 := by simpa [ownsFeat] using ho
      show (if g = 0 then _ else none) = none ↔ _
      rw [if_pos h0]
      exact ff g .xin
    | _ => exact Bool.noConfusion ho
  | att g =>
    cases μ with
    | ah =>
      show (ahName S.DA φ i).map (Name.att g) = none ↔ Phi S.DA .ah ≤ φ
      rw [Option.map_eq_none_iff]
      constructor
      · intro e
        by_contra hlt
        obtain ⟨c, hc, -⟩ := (ahName_spec S.DA hiA).1 (Nat.lt_of_not_le hlt)
        rw [e] at hc
        exact absurd hc (by simp)
      · intro hle
        exact (ahName_spec S.DA hiA).2 (Nat.not_lt.2 hle)
    | ao =>
      show (aoName S.DA φ i).map (Name.att g) = none ↔ Phi S.DA .ao ≤ φ
      rw [Option.map_eq_none_iff]
      constructor
      · intro e
        by_contra hlt
        obtain ⟨c, hc, -⟩ := (aoName_spec S.DA hiA).1 (Nat.lt_of_not_le hlt)
        rw [e] at hc
        exact absurd hc (by simp)
      · intro hle
        exact (aoName_spec S.DA hiA).2 (Nat.not_lt.2 hle)
    | _ => exact Bool.noConfusion ho
  | head =>
    cases μ with
    | hf p =>
      show (if φ < S.n (.hf p) then some (Name.hf φ i) else none) = none ↔ _
      by_cases hφ : φ < S.n (.hf p)
      · rw [if_pos hφ]; simp; exact hφ
      · rw [if_neg hφ]; simp; omega
    | hd =>
      show (if φ < S.n .hd then some (Name.hd φ i) else none) = none ↔ _
      by_cases hφ : φ < S.n .hd
      · rw [if_pos hφ]; simp; exact hφ
      · rw [if_neg hφ]; simp; omega
    | hr =>
      show (if φ < S.n .hr then some (Name.hr φ i) else none) = none ↔ _
      by_cases hφ : φ < S.n .hr
      · rw [if_pos hφ]; simp; exact hφ
      · rw [if_neg hφ]; simp; omega
    | _ => exact Bool.noConfusion ho

/-- A matrix of features that its segment owns is a matrix of features. -/
theorem isFeat_of_owns {σ : Seg} {μ : MatName} (ho : ownsFeat σ μ = true) :
    isFeat σ μ = true := by
  cases σ <;> cases μ <;> first | rfl | exact ho

/-- **Padding is "none".** Under "OK", in a matrix of features that its segment owns, at a row and
column inside the shape: "nameAt" returns "none" exactly if the feature at that place is not in use.
-/
theorem nameAt_none_iff (S : Sz) (h : S.OK) (σ : Seg) (μ : MatName) (r c : ℕ)
    (ho : ownsFeat σ μ = true) (hr : r < (S.shape σ μ).1) (hc : c < (S.shape σ μ).2) :
    S.nameAt σ μ r c = none ↔ S.n μ ≤ (S.featOf μ r c).1 := by
  rw [Sz.nameAt_of_isFeat (isFeat_of_owns ho) ⟨hr, hc⟩]
  exact nameOfFeat_none_iff h ho (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- In a part of as, at a row and column inside the shape: "nameAt" returns "none" exactly if the
cell's number at that place is not in use. No premise on the numbers. -/
theorem nameAt_as_none_iff (S : Sz) (g p r c : ℕ) (hr : r < (S.shape (.att g) (.as p)).1)
    (hc : c < (S.shape (.att g) (.as p)).2) :
    S.nameAt (.att g) (.as p) r c = none ↔ S.n (.as p) ≤ S.cellOf (.as p) r c := by
  unfold Sz.nameAt
  rw [if_pos ⟨hr, hc⟩]
  show (asName S.DA (S.cellOf (.as p) r c)).map (Name.att g) = none ↔
    SM S.DA + SD S.DA ≤ S.cellOf (.as p) r c
  rw [Option.map_eq_none_iff]
  constructor
  · intro e
    by_contra hlt
    obtain ⟨ρ, jj, b, x, hc', -⟩ := (asName_spec S.DA).1 (Nat.lt_of_not_le hlt)
    rw [e] at hc'
    exact absurd hc' (by simp)
  · intro hle
    exact (asName_spec S.DA).2 (Nat.not_lt.2 hle)

end Padding

/-! ## Attention's borrowed names -/

section Borrowed
variable {S : Sz}

/-- Under "Fit" the query heads, the channels and the heads of keys and values are the same numbers
in "DA" and in P; the layers of a group in "DA" are 2^ll. -/
theorem sizes_agree (f : S.Fit) :
    S.DA.nH = S.P.nq ∧ S.DA.ch = S.P.ch ∧ S.DA.nG = S.P.nkv ∧ S.DA.nl = 2 ^ S.ll := by
  refine ⟨?_, f.ch.symm, f.nkv.symm, rfl⟩
  show 2 ^ S.lg * (S.P.nq / S.P.nkv) = S.P.nq
  rw [← f.nkv]
  exact Nat.mul_div_cancel' f.nq

/-- Under "Fit" attention's feature of a query is the feed-forward segment's feature of q. -/
theorem phi_qry (f : S.Fit) (k b gk i n : ℕ) :
    phi S.DA (.qry k b gk i n) =
      FFSeg.feat S.DF .q k (S.DA.lamOf b) (S.DA.ch * S.DA.head gk b + n) := by
  obtain ⟨e1, e2, -, e4⟩ := sizes_agree f
  show S.DA.ch * (S.DA.nH * (S.DA.nl * k + S.DA.lamOf b) + S.DA.head gk b) + n =
    0 + (k * 2 ^ S.ll + S.DA.lamOf b) * (S.P.nq * S.P.ch) + (S.DA.ch * S.DA.head gk b + n)
  rw [e1, e2, e4]
  ring

/-- Under "Fit" attention's feature of a key is the feed-forward segment's feature of kx. -/
theorem phi_key (f : S.Fit) (k lam gk j n : ℕ) :
    phi S.DA (.key k lam gk j n) = FFSeg.feat S.DF .kx k lam (S.DA.ch * gk + n) := by
  obtain ⟨e1, e2, e3, e4⟩ := sizes_agree f
  show 2 * (S.DA.ch * (S.DA.nH * S.DA.nl)) + (S.DA.ch * (S.DA.nG * (S.DA.nl * k + lam) + gk) + n) =
    (2 * 2 ^ S.ll * (S.P.nq * S.P.ch) + 0) + (k * 2 ^ S.ll + lam) * (S.P.nkv * S.P.ch) +
      (S.DA.ch * gk + n)
  rw [e1, e2, e3, e4]
  ring

/-- Under "Fit" attention's feature of a value is the feed-forward segment's feature of v. -/
theorem phi_val (f : S.Fit) (k lam gk j n : ℕ) :
    phi S.DA (.val k lam gk j n) = FFSeg.feat S.DF .v k lam (S.DA.ch * gk + n) := by
  obtain ⟨e1, e2, e3, e4⟩ := sizes_agree f
  show 2 * (S.DA.ch * (S.DA.nH * S.DA.nl)) + 2 * (S.DA.ch * (S.DA.nG * S.DA.nl)) +
      (S.DA.ch * (S.DA.nG * (S.DA.nl * k + lam) + gk) + n) =
    (2 * 2 ^ S.ll * (S.P.nq * S.P.ch) + (2 * 2 ^ S.ll * (S.P.nkv * S.P.ch) + 0)) +
      (k * 2 ^ S.ll + lam) * (S.P.nkv * S.P.ch) + (S.DA.ch * gk + n)
  rw [e1, e2, e3, e4]
  ring

/-- Under "Fit" attention's feature of an output is the feed-forward segment's feature of o. -/
theorem phi_out (f : S.Fit) (k b gk i n : ℕ) :
    phi S.DA (.out k b gk i n) =
      FFSeg.feat S.DF .o k (S.DA.lamOf b) (S.DA.ch * S.DA.head gk b + n) := by
  obtain ⟨e1, e2, e3, e4⟩ := sizes_agree f
  show 2 * (S.DA.ch * (S.DA.nH * S.DA.nl)) + 4 * (S.DA.ch * (S.DA.nG * S.DA.nl)) +
      (S.DA.ch * (S.DA.nH * (S.DA.nl * k + S.DA.lamOf b) + S.DA.head gk b) + n) =
    (2 * 2 ^ S.ll * (S.P.nq * S.P.ch) + (2 * 2 ^ S.ll * (S.P.nkv * S.P.ch) +
      (2 * 2 ^ S.ll * (S.P.nkv * S.P.ch) + 0))) +
      (k * 2 ^ S.ll + S.DA.lamOf b) * (S.P.nq * S.P.ch) + (S.DA.ch * S.DA.head gk b + n)
  rw [e1, e2, e3, e4]
  ring

/-- Under "Fit" the library's two counts of the features of qa agree. -/
theorem Phi_qa (f : S.Fit) : Phi S.DA .qa = S.n .qa := by
  obtain ⟨e1, e2, e3, e4⟩ := sizes_agree f
  show 4 * (S.DA.ch * (S.DA.nH * S.DA.nl)) + 4 * (S.DA.ch * (S.DA.nG * S.DA.nl)) =
    2 * 2 ^ S.ll * (S.P.nq * S.P.ch) + (2 * 2 ^ S.ll * (S.P.nkv * S.P.ch) +
      (2 * 2 ^ S.ll * (S.P.nkv * S.P.ch) + (2 * 2 ^ S.ll * (S.P.nq * S.P.ch) + 0)))
  rw [e1, e2, e3, e4]
  ring

/-- **Lender and borrower name one entry**, under "Fit", for all numbers, in range or not:
attention's name of a query is laid where the feed-forward segment lays its own cell of q. -/
theorem place_qry (f : S.Fit) (g k b gk i n : ℕ) :
    (Name.att g (.qry k b gk i n)).place S =
      (Name.ff g ⟨.q, k, S.DA.lamOf b, S.DA.ch * S.DA.head gk b + n, i⟩).place S :=
  congrArg (fun φ => S.atFeat (.ff g) .qa φ i) (phi_qry f k b gk i n)

/-- The same for attention's output and the array o, under "Fit". -/
theorem place_out (f : S.Fit) (g k b gk i n : ℕ) :
    (Name.att g (.out k b gk i n)).place S =
      (Name.ff g ⟨.o, k, S.DA.lamOf b, S.DA.ch * S.DA.head gk b + n, i⟩).place S :=
  congrArg (fun φ => S.atFeat (.ff g) .qa φ i) (phi_out f k b gk i n)

/-- The same for a key and the array kx, under "Fit". -/
theorem place_key (f : S.Fit) (g k lam gk j n : ℕ) :
    (Name.att g (.key k lam gk j n)).place S =
      (Name.ff g ⟨.kx, k, lam, S.DA.ch * gk + n, j⟩).place S :=
  congrArg (fun φ => S.atFeat (.ff g) .qa φ j) (phi_key f k lam gk j n)

/-- The same for a value and the array v, under "Fit". -/
theorem place_val (f : S.Fit) (g k lam gk j n : ℕ) :
    (Name.att g (.val k lam gk j n)).place S =
      (Name.ff g ⟨.v, k, lam, S.DA.ch * gk + n, j⟩).place S :=
  congrArg (fun φ => S.atFeat (.ff g) .qa φ j) (phi_val f k lam gk j n)

end Borrowed

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.Sz.wc_setPart
#print axioms OnBytes.HonestTrace.Sz.kF_setPart
#print axioms OnBytes.HonestTrace.Sz.n_setPart
#print axioms OnBytes.HonestTrace.Sz.part_setPart
#print axioms OnBytes.HonestTrace.Sz.setPart_part
#print axioms OnBytes.HonestTrace.Sz.nameOfFeat_setPart
#print axioms OnBytes.HonestTrace.Sz.wc_pos
#print axioms OnBytes.HonestTrace.Sz.np_pos
#print axioms OnBytes.HonestTrace.Sz.kF_eq
#print axioms OnBytes.HonestTrace.Sz.mu_feat
#print axioms OnBytes.HonestTrace.Sz.shape_feat
#print axioms OnBytes.HonestTrace.Sz.part_lt
#print axioms OnBytes.HonestTrace.Sz.atFeat_inShape
#print axioms OnBytes.HonestTrace.Sz.featOf_atFeat
#print axioms OnBytes.HonestTrace.Sz.atFeat_featOf
#print axioms OnBytes.HonestTrace.ffName_feat
#print axioms OnBytes.HonestTrace.ffName_back
#print axioms OnBytes.HonestTrace.bg_formula
#print axioms OnBytes.HonestTrace.fK_formula
#print axioms OnBytes.HonestTrace.fI_formula
#print axioms OnBytes.HonestTrace.fL_formula
#print axioms OnBytes.HonestTrace.ahName_spec
#print axioms OnBytes.HonestTrace.aoName_spec
#print axioms OnBytes.HonestTrace.asName_spec
#print axioms OnBytes.HonestTrace.Sz.DA_T
#print axioms OnBytes.HonestTrace.Sz.n_famOf
#print axioms OnBytes.HonestTrace.Sz.isFeat_famOf
#print axioms OnBytes.HonestTrace.Sz.isFeat_setPart
#print axioms OnBytes.HonestTrace.Sz.atFeat_setPart
#print axioms OnBytes.HonestTrace.Sz.nameAt_of_isFeat
#print axioms OnBytes.HonestTrace.Sz.nameAt_atFeat
#print axioms OnBytes.HonestTrace.Sz.shape_as
#print axioms OnBytes.HonestTrace.Sz.atCell_lt
#print axioms OnBytes.HonestTrace.Sz.atCell_inShape
#print axioms OnBytes.HonestTrace.Sz.cellOf_atCell
#print axioms OnBytes.HonestTrace.Sz.atCell_cellOf
#print axioms OnBytes.HonestTrace.Sz.shape_plane
#print axioms OnBytes.HonestTrace.Sz.kP_mul
#print axioms OnBytes.HonestTrace.Sz.bitNo_lt
#print axioms OnBytes.HonestTrace.Sz.atBit_inShape
#print axioms OnBytes.HonestTrace.Sz.bitName_atBit
#print axioms OnBytes.HonestTrace.Sz.bitName_back
#print axioms OnBytes.HonestTrace.x0_of_xin
#print axioms OnBytes.HonestTrace.nameOfFeat_famOf
#print axioms OnBytes.HonestTrace.back_ff
#print axioms OnBytes.HonestTrace.pos_lt
#print axioms OnBytes.HonestTrace.place_att_feat
#print axioms OnBytes.HonestTrace.nameOfFeat_back
#print axioms OnBytes.HonestTrace.place_inShape
#print axioms OnBytes.HonestTrace.nameAt_planeEq
#print axioms OnBytes.HonestTrace.nameAt_place
#print axioms OnBytes.HonestTrace.place_inj
#print axioms OnBytes.HonestTrace.back_as
#print axioms OnBytes.HonestTrace.nameAt_back
#print axioms OnBytes.HonestTrace.nameAt_plane
#print axioms OnBytes.HonestTrace.owner_famOf
#print axioms OnBytes.HonestTrace.owner_place
#print axioms OnBytes.HonestTrace.lay_place
#print axioms OnBytes.HonestTrace.lay_off
#print axioms OnBytes.HonestTrace.below_of_mu
#print axioms OnBytes.HonestTrace.shape_owner
#print axioms OnBytes.HonestTrace.owner_owner
#print axioms OnBytes.HonestTrace.lay_owner
#print axioms OnBytes.HonestTrace.lay_small
#print axioms OnBytes.HonestTrace.ranges_tile
#print axioms OnBytes.HonestTrace.arrs_nodup
#print axioms OnBytes.HonestTrace.ffName_none_iff
#print axioms OnBytes.HonestTrace.nameOfFeat_none_iff
#print axioms OnBytes.HonestTrace.isFeat_of_owns
#print axioms OnBytes.HonestTrace.nameAt_none_iff
#print axioms OnBytes.HonestTrace.nameAt_as_none_iff
#print axioms OnBytes.HonestTrace.sizes_agree
#print axioms OnBytes.HonestTrace.phi_qry
#print axioms OnBytes.HonestTrace.phi_key
#print axioms OnBytes.HonestTrace.phi_val
#print axioms OnBytes.HonestTrace.phi_out
#print axioms OnBytes.HonestTrace.Phi_qa
#print axioms OnBytes.HonestTrace.place_qry
#print axioms OnBytes.HonestTrace.place_out
#print axioms OnBytes.HonestTrace.place_key
#print axioms OnBytes.HonestTrace.place_val
