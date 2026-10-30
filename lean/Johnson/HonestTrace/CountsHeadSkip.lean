-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHeadSkip.lean

If Head.layout returns, the library's terms for the keys of the lookup of the output head's calls do
not read the cells of the planes' matrix bH.

The library's terms for the head's key vectors (Ends.H.kvH, OnBytes/Tie/Pv/Lookup/Ends/H.lean) name
a cell by a family of matrices, a feature and a position (Ends.H.cellAt): a feature whose number is
too large for its family runs on into the next matrix. The planes' matrix has the number NHf + 2,
after hf's NHf parts, hd and hr. This file bounds every feature of hf, hd and hr that a key reads,
so that none runs on into that matrix; the stream's matrices come after it, so their features need
no bound.

Notation: as in Johnson/HonestTrace/CountsHead.lean; d, V, XL, T and NHf are fields of P.h; JV, k,
m, kD, mD, kR and mR are fields of P.L.

Main theorems:
* "HeadSkip.kvH_congr": if Head.layout P.h tau returns P.L, and two readings cell' and cell agree at
  every name but the cells of matrix number NHf + 2 ("HeadSkip.Agree"), then Ends.H.kvH P cell' q i
  = Ends.H.kvH P cell q i for all q and i.
* "keysSkipBH": if Head.layout P.h tau returns P.L, KeysSkipBH P cell (CountsHead.lean) holds of
  every reading cell in every field with decidable equality.

The steps stand in the namespace HeadSkip: "mats" (in which matrix a feature below its family's
number of features lies), one theorem for each of Ends/H.lean's readers of cells (hfC, hdC, hrC,
xbC, limbs, aw, ra, d1, d2, ex, nrm, xs, dig, digs, recip, costC, costB, wH, lg, midK, lowK),
"bd_of_col" (the bound on an entry that Ends.H.colH finds, by its segment's name), "affH_congr",
"gamH_congr".

Limits. The bounds come from Head.layout's own tests and numbers; that Head.layout returns for some
shape is not shown in this file. kvH_congr has no bound on q and i because colH finds listed entries
alone, at every column. The fields b, cov, win and lay of P are arbitrary. Nothing is said of the
cells of the stream's matrices, whose numbers begin at NHf + 3, but that they are not bH's.

Not claimed: that kvH is what a verifier reads; that a prover's committed cells are any of these
readings; anything on soundness or zero knowledge.

-/
import Johnson.HonestTrace.CountsHead

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model
open OnBytes.Ends.H (NameH PubH)

namespace HeadSkip

/-! ## In which matrix a feature lies -/

/-- For N, u > 0 and F < feat: with k := roundUp feat (N u) / (N u), F / (k u) < N. -/
theorem hf_lt {feat N u F : ℕ} (hN : 0 < N) (hu : 0 < u) (hF : F < feat) :
    F / (roundUp feat (N * u) / (N * u) * u) < N := by
  have hw : 0 < N * u := Nat.mul_pos hN hu
  have h1 := (Road.Hd.roundUp_bounds feat hw).1
  have h2 : roundUp feat (N * u) / (N * u) * (N * u) = roundUp feat (N * u) :=
    Nat.div_mul_cancel (Road.Hd.dvd_roundUp _ _)
  apply Nat.div_lt_of_lt_mul
  have h3 : roundUp feat (N * u) / (N * u) * u * N = roundUp feat (N * u) / (N * u) * (N * u) := by
    ring
  rw [h3, h2]
  omega

/-- For u > 0 and F < x: with k := roundUp x u / u, F / (k u) = 0. -/
theorem one_lt {x u F : ℕ} (hu : 0 < u) (hF : F < x) : F / (roundUp x u / u * u) = 0 := by
  apply Nat.div_eq_of_lt
  rw [Nat.div_mul_cancel (Road.Hd.dvd_roundUp _ _)]
  exact Nat.lt_of_lt_of_le hF (Road.Hd.roundUp_bounds x hu).1

/-- If Head.layout h tau returns L: a feature below 4 d + (3 + exc) JV lies in one of hf's NHf parts
(F / (k (m / T)) < NHf); a feature below 2 d lies in the one matrix hd (F / (kD (mD / T)) = 0); a
feature below ledNRH XL lies in the one matrix hr (F / (kR (mR / T)) = 0). -/
theorem mats {h : Head.Shape} {tau : Array F} {L : Head.HL} (hy : Head.layout h tau = .ok L) :
    (∀ F, F < 4 * h.d + (3 + exc) * L.JV → F / (L.k * (L.m / h.T)) < h.NHf) ∧
    (∀ F, F < 2 * h.d → F / (L.kD * (L.mD / h.T)) = 0) ∧
    (∀ F, F < ledNRH h.XL → F / (L.kR * (L.mR / h.T)) = 0) := by
  have hadm := (Road.Hd.admittedH_of_layout hy).adm
  simp only [Head.admitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
  unfold Head.layout at hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨L0, hn, hy⟩ := Road.ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  cases hy
  unfold Head.numbers at hn
  obtain ⟨-, hn⟩ := Road.Hd.ok_of_needed hn
  obtain ⟨e3, hn⟩ := Road.Hd.ok_of_needed hn
  cases hn
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt,
    beq_eq_false_iff_ne] at e3
  have pos : ∀ a, h.lt ≤ a → 0 < 2 ^ a / h.T := fun a ha =>
    Nat.div_pos (Nat.pow_le_pow_right (by norm_num) ha) (Nat.pow_pos (by norm_num))
  refine ⟨fun F hF => ?_, fun F hF => ?_, fun F hF => ?_⟩
  · exact hf_lt (by omega) (pos h.lmhf (by omega)) hF
  · exact one_lt (pos h.lmhd (by omega)) hF
  · exact one_lt (pos h.lmhr (by omega)) hF

/-! ## Two readings that agree outside the planes' matrix -/

/-- The readings cell' and cell agree at every name but the cells of matrix number P.h.NHf + 2. -/
structure Agree {K : Type} (P : PubH) (cell' cell : NameH → K) : Prop where
  mat : ∀ m r c, m ≠ P.h.NHf + 2 → cell' (.cell m r c) = cell (.cell m r c)
  wt : ∀ r c, cell' (.w r c) = cell (.w r c)

/-- Two folds over one list from one start are equal if their steps agree at the list's members. -/
theorem foldl_congr {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ s, ∀ a ∈ l, f s a = g s a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h b a List.mem_cons_self]
    exact foldl_congr f g l _ fun s a' ha' => h s a' (List.mem_cons_of_mem _ ha')

/-- For l < n and x < J: l J + x < n J. -/
theorem limb_lt {l n x J : ℕ} (hl : l < n) (hx : x < J) : l * J + x < n * J := by
  have h1 : (l + 1) * J ≤ n * J := Nat.mul_le_mul_right _ hl
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

section
variable {K : Type} {P : PubH} {tau : Array F} {cell' cell : NameH → K}

open Ends.H

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for F < 4 d + (3 + exc) JV
Ends.H.hfC is the same at cell' and at cell. -/
theorem hfC_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {F : ℕ}
    (hF : F < 4 * P.h.d + (3 + exc) * P.L.JV) (t : ℕ) : hfC P cell' F t = hfC P cell F t := by
  have k := (mats hy).1 F hF
  exact A.mat _ _ _ (by omega)

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for F < 2 d Ends.H.hdC is
the same at cell' and at cell. -/
theorem hdC_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {F : ℕ}
    (hF : F < 2 * P.h.d) (t : ℕ) : hdC P cell' F t = hdC P cell F t := by
  have k := (mats hy).2.1 F hF
  exact A.mat _ _ _ (by omega)

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for F < ledNRH XL
Ends.H.hrC is the same at cell' and at cell. -/
theorem hrC_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {F : ℕ}
    (hF : F < ledNRH P.h.XL) (t : ℕ) : hrC P cell' F t = hrC P cell F t := by
  have k := (mats hy).2.2 F hF
  exact A.mat _ _ _ (by omega)

/-- If Agree P cell' cell holds, Ends.H.xbC is the same at cell' and at cell, at every feature: its
matrices' numbers begin at NHf + 3. -/
theorem xbC_congr (A : Agree P cell' cell) (F t : ℕ) : xbC P cell' F t = xbC P cell F t := by
  unfold xbC cellAt
  exact A.mat _ _ _
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)))

variable [Field K]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for x < J and off + n J ≤
4 d + (3 + exc) JV Ends.H.limbs n off J x is the same at cell' and at cell. -/
theorem limbs_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell)
    {n off J x : ℕ} (hx : x < J) (hb : off + n * J ≤ 4 * P.h.d + (3 + exc) * P.L.JV) (t : ℕ) :
    limbs P cell' n off J x t = limbs P cell n off J x t := by
  unfold limbs
  refine foldl_congr _ _ _ _ fun s l hl => ?_
  have k := limb_lt (List.mem_range.1 hl) hx
  rw [hfC_congr hy A (by omega)]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for k < d Ends.H.nrm is
the same at cell' and at cell. -/
theorem nrm_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {k : ℕ}
    (hk : k < P.h.d) (t : ℕ) : nrm P cell' k t = nrm P cell k t := by
  unfold nrm
  rw [hdC_congr hy A (by omega), hdC_congr hy A (by omega)]

/-- If Agree P cell' cell holds, Ends.H.xs is the same at cell' and at cell. -/
theorem xs_congr (A : Agree P cell' cell) (k t : ℕ) : xs P cell' k t = xs P cell k t := by
  unfold xs
  exact foldl_congr _ _ _ _ fun s l _ => by rw [xbC_congr A]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for idx < ledNRH XL
Ends.H.dig is the same at cell' and at cell. -/
theorem dig_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {idx : ℕ}
    (hi : idx < ledNRH P.h.XL) (t : ℕ) : dig P cell' idx t = dig P cell idx t := by
  unfold dig
  rw [hrC_congr hy A hi]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for first + n ≤ ledNRH XL
Ends.H.digs first n is the same at cell' and at cell. -/
theorem digs_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {first n : ℕ}
    (hi : first + n ≤ ledNRH P.h.XL) (t : ℕ) : digs P cell' first n t = digs P cell first n t := by
  unfold digs
  refine foldl_congr _ _ _ _ fun s j hj => ?_
  have k := List.mem_range.1 hj
  rw [dig_congr hy A (by omega)]

/-- If Agree P cell' cell holds, Ends.H.wH is the same at cell' and at cell: it reads cells of the
weights alone. -/
theorem wH_congr (A : Agree P cell' cell) (k v : ℕ) : wH P cell' k v = wH P cell k v := by
  unfold wH
  exact foldl_congr _ _ _ _ fun s δ _ => by rw [A.wt]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then Ends.H.lg is the same at
cell' and at cell. -/
theorem lg_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (v t : ℕ) :
    lg P cell' v t = lg P cell v t := by
  unfold lg
  refine foldl_congr _ _ _ _ fun s k hk => ?_
  rw [nrm_congr hy A (List.mem_range.1 hk), wH_congr A]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for x < d Ends.H.aw is the
same at cell' and at cell. -/
theorem aw_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {x : ℕ}
    (hx : x < P.h.d) (t : ℕ) : aw P cell' x t = aw P cell x t := by
  have O := Road.Hd.admittedH_of_layout hy
  exact limbs_congr hy A hx (by rw [O.oAw]; omega) t

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for x < d Ends.H.ra is the
same at cell' and at cell. -/
theorem ra_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {x : ℕ}
    (hx : x < P.h.d) (t : ℕ) : ra P cell' x t = ra P cell x t := by
  have O := Road.Hd.admittedH_of_layout hy
  exact limbs_congr hy A hx (by rw [O.oRa]; omega) t

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for v < JV Ends.H.d1 is
the same at cell' and at cell. -/
theorem d1_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {v : ℕ}
    (hv : v < P.L.JV) (t : ℕ) : d1 P cell' v t = d1 P cell v t := by
  have O := Road.Hd.admittedH_of_layout hy
  have e6 : (3 + exc) * P.L.JV = 6 * P.L.JV := rfl
  exact limbs_congr hy A hv (by rw [O.oD1]; omega) t

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for v < JV Ends.H.d2 is
the same at cell' and at cell. -/
theorem d2_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {v : ℕ}
    (hv : v < P.L.JV) (t : ℕ) : d2 P cell' v t = d2 P cell v t := by
  have O := Road.Hd.admittedH_of_layout hy
  have e6 : (3 + exc) * P.L.JV = 6 * P.L.JV := rfl
  exact limbs_congr hy A hv (by rw [O.oD2]; omega) t

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for v < JV Ends.H.ex is
the same at cell' and at cell. -/
theorem ex_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {v : ℕ}
    (hv : v < P.L.JV) (t : ℕ) : ex P cell' v t = ex P cell v t := by
  have O := Road.Hd.admittedH_of_layout hy
  have e6 : (3 + exc) * P.L.JV = 6 * P.L.JV := rfl
  have e3 : exc * P.L.JV = 3 * P.L.JV := rfl
  exact limbs_congr hy A hv (by rw [O.oE]; omega) t

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for v < JV Ends.H.midK is
the same at cell' and at cell. -/
theorem midK_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {v : ℕ}
    (hv : v < P.L.JV) (t : ℕ) : midK P cell' v t = midK P cell v t := by
  unfold midK
  rw [d1_congr hy A hv]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for v < JV Ends.H.lowK is
the same at cell' and at cell. -/
theorem lowK_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {v : ℕ}
    (hv : v < P.L.JV) (t : ℕ) : lowK P cell' v t = lowK P cell v t := by
  unfold lowK
  rw [d2_congr hy A hv]

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then Ends.H.recip is the same
at cell' and at cell. -/
theorem recip_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (t : ℕ) :
    recip P cell' t = recip P cell t := by
  unfold recip
  refine digs_congr hy A ?_ t
  simp only [ledNRH, ledNR, ledNE]
  split_ifs <;> omega

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then Ends.H.costC is the same
at cell' and at cell. -/
theorem costC_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (t : ℕ) :
    costC P cell' t = costC P cell t := by
  unfold costC
  refine digs_congr hy A ?_ t
  simp only [ledNRH, ledNE]
  omega

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then Ends.H.costB is the same
at cell' and at cell. -/
theorem costB_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (t : ℕ) :
    costB P cell' t = costB P cell t := by
  unfold costB
  refine dig_congr hy A ?_ t
  simp only [ledNRH, ledNE]
  omega

/-! ## The keys -/

/-- The bounds on entry x of a segment, by the segment's name sn: x < d for NF, NFH, CNF; x < JV for
HD0, HD1, HD2; Head.firstEntry P.L sn + x < JV for HE0, HE1; x < ledNRH XL for ROW. -/
structure Bd (P : PubH) (sn : String) (x : ℕ) : Prop where
  d : sn = "NF" ∨ sn = "NFH" ∨ sn = "CNF" → x < P.h.d
  jv : sn = "HD0" ∨ sn = "HD1" ∨ sn = "HD2" → x < P.L.JV
  he : sn = "HE0" ∨ sn = "HE1" → Head.firstEntry P.L sn + x < P.L.JV
  row : sn = "ROW" → x < ledNRH P.h.XL

/-- If Head.layout P.h tau returns P.L, and Ends.H.colH P.L q j is entry x of a segment sn, then Bd
P sn x holds. -/
theorem bd_of_col (hy : Head.layout P.h tau = .ok P.L) {q j : ℕ} {sn : String} {x : ℕ}
    (hc : colH P.L q j = some (sn, x)) : Bd P sn x := by
  obtain ⟨y, f1, hx⟩ := HeadPub.entry_seg hy hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (rfl | rfl | rfl) <;> simp [Head.segments] at f1 <;> subst f1 <;> exact hx
  · rintro (rfl | rfl | rfl) <;> simp [Head.segments] at f1 <;> subst f1 <;> exact hx
  · intro k
    exact HeadPub.entry_lt hy hc (by rcases k with rfl | rfl <;> simp [Head.perEntry])
  · rintro rfl
    simp [Head.segments] at f1
    subst f1
    exact hx

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then for an entry with Bd P sn
x Ends.H.affH is the same at cell' and at cell. -/
theorem affH_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) {sn : String}
    {x : ℕ} (B : Bd P sn x) (t : ℕ) : affH P cell' sn x t = affH P cell sn x t := by
  unfold affH
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · have hx := B.d (Or.inl (by simpa using h1))
    rw [aw_congr hy A hx, ra_congr hy A hx]
  · have hx := B.d (Or.inr (Or.inl (by simpa using h2)))
    rw [ra_congr hy A hx]
  · have hx := B.jv (Or.inl (by simpa using h3))
    rw [costC_congr hy A, costB_congr hy A, midK_congr hy A hx, lowK_congr hy A hx]
  · have hx := B.jv (Or.inr (Or.inl (by simpa using h4)))
    rw [midK_congr hy A hx]
  · have hx := B.jv (Or.inr (Or.inr (by simpa using h5)))
    rw [lowK_congr hy A hx]
  · have hx := B.he (by simpa using h6)
    dsimp only
    rw [midK_congr hy A hx, ex_congr hy A hx]
  · have hx := B.row (by simpa using h7)
    rw [dig_congr hy A hx]
  · have hx := B.row (by simpa using h7)
    rw [dig_congr hy A hx]
  · have hx := B.d (Or.inr (Or.inr (by simpa using h9)))
    rw [aw_congr hy A hx, nrm_congr hy A hx]
  · rfl

/-- If Head.layout P.h tau returns P.L and Agree P cell' cell holds, then Ends.H.gamH is the same at
cell' and at cell. -/
theorem gamH_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (sn : String)
    (x t : ℕ) : gamH P cell' sn x t = gamH P cell sn x t := by
  unfold gamH
  split_ifs
  · rw [recip_congr hy A, xs_congr A]
  · rw [lg_congr hy A, lg_congr hy A]
  · rfl

/-- **The keys do not read the planes' matrix.** If Head.layout P.h tau returns P.L and Agree P
cell' cell holds, then Ends.H.kvH P cell' q i = Ends.H.kvH P cell q i for all q and i. -/
theorem kvH_congr (hy : Head.layout P.h tau = .ok P.L) (A : Agree P cell' cell) (q i : ℕ) :
    kvH P cell' q i = kvH P cell q i := by
  unfold kvH kvOf
  cases hc : colH P.L q (i / P.h.T) with
  | none => rfl
  | some a =>
    obtain ⟨sn, x⟩ := a
    show segH P cell' sn x (i % P.h.T) = segH P cell sn x (i % P.h.T)
    unfold segH
    rw [affH_congr hy A (bd_of_col hy hc), gamH_congr hy A]

end

end HeadSkip

/-- withBH P cell and cell agree at every name but the cells of matrix number P.h.NHf + 2. -/
theorem agree_withBH {K : Type} [Field K] [DecidableEq K] (P : PubH) (cell : NameH → K) :
    HeadSkip.Agree P (withBH P cell) cell :=
  ⟨fun _ _ _ hm => if_neg hm, fun _ _ => rfl⟩

/-- **Laying bH changes no key.** If Head.layout P.h tau returns P.L, then KeysSkipBH P cell holds
of every reading cell. -/
theorem keysSkipBH {K : Type} [Field K] [DecidableEq K] {tau : Array F} (P : PubH)
    (hy : Head.layout P.h tau = .ok P.L) (cell : NameH → K) : KeysSkipBH P cell :=
  fun q _ i _ => HeadSkip.kvH_congr hy (agree_withBH P cell) q i

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.HeadSkip.hf_lt
#print axioms OnBytes.HonestTrace.HeadSkip.one_lt
#print axioms OnBytes.HonestTrace.HeadSkip.mats
#print axioms OnBytes.HonestTrace.HeadSkip.foldl_congr
#print axioms OnBytes.HonestTrace.HeadSkip.limb_lt
#print axioms OnBytes.HonestTrace.HeadSkip.hfC_congr
#print axioms OnBytes.HonestTrace.HeadSkip.hdC_congr
#print axioms OnBytes.HonestTrace.HeadSkip.hrC_congr
#print axioms OnBytes.HonestTrace.HeadSkip.xbC_congr
#print axioms OnBytes.HonestTrace.HeadSkip.limbs_congr
#print axioms OnBytes.HonestTrace.HeadSkip.nrm_congr
#print axioms OnBytes.HonestTrace.HeadSkip.xs_congr
#print axioms OnBytes.HonestTrace.HeadSkip.dig_congr
#print axioms OnBytes.HonestTrace.HeadSkip.digs_congr
#print axioms OnBytes.HonestTrace.HeadSkip.wH_congr
#print axioms OnBytes.HonestTrace.HeadSkip.lg_congr
#print axioms OnBytes.HonestTrace.HeadSkip.aw_congr
#print axioms OnBytes.HonestTrace.HeadSkip.ra_congr
#print axioms OnBytes.HonestTrace.HeadSkip.d1_congr
#print axioms OnBytes.HonestTrace.HeadSkip.d2_congr
#print axioms OnBytes.HonestTrace.HeadSkip.ex_congr
#print axioms OnBytes.HonestTrace.HeadSkip.midK_congr
#print axioms OnBytes.HonestTrace.HeadSkip.lowK_congr
#print axioms OnBytes.HonestTrace.HeadSkip.recip_congr
#print axioms OnBytes.HonestTrace.HeadSkip.costC_congr
#print axioms OnBytes.HonestTrace.HeadSkip.costB_congr
#print axioms OnBytes.HonestTrace.HeadSkip.bd_of_col
#print axioms OnBytes.HonestTrace.HeadSkip.affH_congr
#print axioms OnBytes.HonestTrace.HeadSkip.gamH_congr
#print axioms OnBytes.HonestTrace.HeadSkip.kvH_congr
#print axioms OnBytes.HonestTrace.agree_withBH
#print axioms OnBytes.HonestTrace.keysSkipBH
