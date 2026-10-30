-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAt.lean

PremF (Johnson/HonestTrace/LookDefs.lean), the premises of the statements on the rounds rsF of a
sub-proof's lookup, at the lookups of the calls of the three kinds of sub-proof: a group of layers,
attention, the output head.

Notation. NC, kT, cK are fields of the lookup's shape h : Forest.Shape; d = kT + cK; n_c, k_c are
FoNums.nOf h c and FoNums.kOf h c; the planes' matrix has 2^lm rows and NC 2^(kT + 5 - lm) columns.
ν reads the places Fo.Pl (OnBytes/Tie/Pv/Lookup/Forest/FoV.lean). C : Chal K holds the challenges.
"The three side premises" are: ν .zero = 0; θ = 0 where the shape has one call; C.Fits h.v h.d 5.

Main theorems:
* "bAt_plane": if 5 ≤ lm ≤ kT + 5, ν reads plane h lm H r c, cast into K, at every place .cell r c
  inside the matrix, and ν .zero = 0, then for u < 2^d and j < 32 what ν reads at the place
  (Fo.numsF h lm jLK θ).bAt u j is the cell of plane at FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j).
* "premF_of_law": under the four premises of midP_joint (Johnson/HonestTrace/CountsLaw.lean:
  FoNums.ok h; every key in its call's table; every padding place holds the call's padding row;
  PubFits h pad), 5 ≤ lm ≤ kT + 5, the premise on ν's cells at hitsOf h (tabOf K h) kv pad, and the
  three side premises: PremF h lm jLK kv θ al ν C.
* "premF_G", "premF_A", "premF_H": PremF at a group of layers, at attention and at the head, under
  the premises of lawG, lawA and lawH, if ν reads the cells of the sub-proof's planes' matrix inside
  the matrix, and under the three side premises.

Limits. The premises are assumed, not proved. Among lawG's is Road.Switches, a premise on the
shape's switches that is no test of the Lean verifier under OnBytes/Model/ (by a reading of
Layer.layout's tests, OnBytes/Model/LayerLayout.lean: they let other values of these switches pass).
jLK, the number of the lookup's first mask entry, is an arbitrary argument, and so is what ν reads
at the places .mask j and .key c i.

Not claimed: anything on what follows from PremF; that a prover's committed cells meet the premises.

-/
import Johnson.HonestTrace.LookDefs
import Johnson.HonestTrace.CountsRect
import Johnson.HonestTrace.CountsLayers
import Johnson.HonestTrace.CountsAttention
import Johnson.HonestTrace.CountsHead

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (layout)
open OnBytes.Road (Switches)
open OnBytes.Ends.H (NameH PubH)

section
variable {K : Type} [Field K]

/-- If 5 ≤ lm ≤ kT + 5, ν reads plane h lm H r c, cast into K, at every place .cell r c with r below
2^lm and c below NC 2^(kT + 5 - lm), and ν .zero = 0: then for u < 2^d and j < 32 what ν reads at
(Fo.numsF h lm jLK θ).bAt u j is the cell of plane at
FoNums.cellRC h lm (u / 2^cK, u % 2^cK, j), cast into K. -/
theorem bAt_plane (h : Forest.Shape) (lm jLK : ℕ) (θ : K) (H : Hits) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm), ν (.cell r c) = (plane h lm H r c : K))
    (h0 : ν .zero = 0) {u j : ℕ} (hu : u < 2 ^ h.d) (hj : j < 32) :
    ν ((_root_.Fo.numsF h lm jLK θ).bAt u j) =
      (plane h lm H (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).1
        (FoNums.cellRC h lm (u / 2 ^ h.cK, u % 2 ^ h.cK, j)).2 : K) := by
  have ht : u / 2 ^ h.cK < 2 ^ h.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  show ν (match FoNums.cellOf h u j with
    | some x => .cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
    | none => .zero) = _
  unfold FoNums.cellOf
  by_cases hc : u % 2 ^ h.cK < h.NC
  · rw [if_pos hc]
    obtain ⟨i1, i2⟩ := cellRC_in h h5 hlm ht hc hj
    exact hν _ i1 _ i2
  · rw [if_neg hc]
    have hf : bit h H (u / 2 ^ h.cK) (u % 2 ^ h.cK) j = false := by simp [bit, hc]
    show ν .zero = _
    rw [h0, plane_cellRC h lm H h5 hlm ht hj, hf]
    simp

variable [DecidableEq K]

/-- Let FoNums.ok h hold; for every call c below NC let every place below 2^(n_c) of kv c hold the
value of a row below 2^(k_c) of tabOf K h c, and every padding place the value of the call's padding
row; let PubFits h pad hold; let 5 ≤ lm ≤ kT + 5; let ν read plane h lm (hitsOf h (tabOf K h) kv
pad) r c, cast into K, at every place .cell r c inside the matrix, and 0 at .zero; let θ be 0 where
the shape has one call; let C.Fits h.v h.d 5 hold. Then PremF h lm jLK kv θ al ν C. -/
theorem premF_of_law (h : Forest.Shape) (kv : ℕ → ℕ → K) (pad : ℕ → ℕ → Bool)
    (hok : FoNums.ok h = true)
    (hin : ∀ c < h.NC, Cb.Lkp.InTable (FoNums.nOf h c) (FoNums.kOf h c) (kv c) (tabOf K h c))
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, pad c i = true →
      kv c i = tabOf K h c (FoNums.t0Of h c))
    (hpub : PubFits h pad) {lm : ℕ} (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (jLK : ℕ)
    (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm),
      ν (.cell r c) = (plane h lm (hitsOf h (tabOf K h) kv pad) r c : K))
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several h = false → θ = 0) (C : Chal K)
    (hC : C.Fits h.v h.d 5) : PremF h lm jLK kv θ al ν C :=
  ⟨hok, h5, hlm, h1, h0,
    law_bits h kv pad hok hin hpad hpub h5 hlm _
      (fun _ hu _ hj => bAt_plane h lm jLK θ _ h5 hlm ν hν h0 hu hj) θ al, hC⟩

/-- If Layer.layout h pc returns P.y, Switches h holds, for every call c below NC every place below
2^(n_c) of G.kvG P g cell c holds the value of a row below 2^(k_c) of tabOf, LaidB P g cell holds, ν
reads cell (.cell (G.iB P.y) r c) at every place .cell r c inside the matrix and 0 at .zero, θ is 0
where the shape has one call, and C.Fits holds at the shape's v and d: then PremF holds at P.y.fo,
lmb, the key vectors G.kvG P g cell, θ, al, ν and C. -/
theorem premF_G {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c))
    (hb : LaidB P g cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.y.h.lmb, ∀ c < P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb),
      ν (.cell r c) = cell (.cell (G.iB P.y) r c))
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several P.y.fo = false → θ = 0) (C : Chal K)
    (hC : C.Fits P.y.fo.v P.y.fo.d 5) :
    PremF P.y.fo P.y.h.lmb jLK (G.kvG P g cell) θ al ν C := by
  obtain ⟨hok, h5, hlm⟩ := ok_of_layout hy
  have hcs := (calls_size hok).1
  exact premF_of_law P.y.fo (G.kvG P g cell) (padG P.y) hok hin
    (fun c hc i _ hp => kvG_pad P g cell (by omega) hp) (pubFits_G hy S) h5 hlm jLK ν
    (fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)) h0 θ al h1 C hC

/-- If Attention.shapeHid lid cf returns (S, fs), for every call c below NC every place below
2^(n_c) of A.kvA S fs cell c holds the value of a row below 2^(k_c) of tabOf, LaidBA S fs cell
holds, ν reads cell ⟨S.cf.NAs + 2, r, c⟩ at every place .cell r c inside the matrix and 0 at .zero,
θ is 0 where the shape has one call, and C.Fits holds at fs.v and fs.d: then PremF holds at fs, lmb,
the key vectors A.kvA S fs cell, θ, al, ν and C. -/
theorem premF_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, Cb.Lkp.InTable (FoNums.nOf fs c) (FoNums.kOf fs c)
      (Ends.A.kvA S fs cell c) (tabOf K fs c))
    (hb : LaidBA S fs cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ S.cf.lmb, ∀ c < fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb),
      ν (.cell r c) = cell ⟨S.cf.NAs + 2, r, c⟩)
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several fs = false → θ = 0) (C : Chal K)
    (hC : C.Fits fs.v fs.d 5) : PremF fs S.cf.lmb jLK (Ends.A.kvA S fs cell) θ al ν C := by
  obtain ⟨s1, s2⟩ := size_A hs
  exact premF_of_law fs (Ends.A.kvA S fs cell) (padA S) (ok_A hs) hin
    (fun c hc i _ hp => kvA_pad S fs cell (by omega) (by omega) hp) (pubFits_A hs) (lmb_A hs).1
    (lmb_A hs).2 jLK ν (fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)) h0 θ al h1 C hC

/-- If Head.layout P.h tau returns P.L, for every call c below NC every place below 2^(n_c) of
H.kvH P cell c holds the value of a row below 2^(k_c) of tabOf, FillerIsPad P cell and
LaidBH P cell hold, ν reads cell (.cell (P.h.NHf + 2) r c) at every place .cell r c inside the
matrix and 0 at .zero, θ is 0 where the shape has one call, and C.Fits holds at the shape's v and d:
then PremF holds at P.L.fs, lmbH, the key vectors H.kvH P cell, θ, al, ν and C. -/
theorem premF_H {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L)
    (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) (hb : LaidBH P cell) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
      ν (.cell r c) = cell (.cell (P.h.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : K) (h1 : FoNums.several P.L.fs = false → θ = 0) (C : Chal K)
    (hC : C.Fits P.L.fs.v P.L.fs.d 5) :
    PremF P.L.fs P.h.lmbH jLK (Ends.H.kvH P cell) θ al ν C := by
  obtain ⟨hok, h5, hlm⟩ := ok_H hy
  exact premF_of_law P.L.fs (Ends.H.kvH P cell) (padH P.h P.L) hok hin
    (fun _ hc _ hi hp => kvH_pad P cell hfill hc (calls_size hok).1 hi hp) (pubFits_H hy) h5 hlm
    jLK ν (fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)) h0 θ al h1 C hC

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.bAt_plane
#print axioms OnBytes.HonestTrace.Look.premF_of_law
#print axioms OnBytes.HonestTrace.Look.premF_G
#print axioms OnBytes.HonestTrace.Look.premF_A
#print axioms OnBytes.HonestTrace.Look.premF_H
