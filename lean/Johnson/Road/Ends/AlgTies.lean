-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgTies.lean: from the record Fits to the record TiesG.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (ties_of_fits) TiesG (Johnson/Road/Ends/AlgLin.lean) follows from the record Fits itself,
when the cells c of Fits are G.lean's reading cell at G.lean's own places (cG), the environment v is
P's at group g, and two public clauses hold (every tensor lies in one of the four families of
matrices; the stream's place). So whatever world meets Fits at c := cG P cell meets the two records,
Fits and TiesG, that alg_line and alg_call ask; their other premises stay. fits_of_layout_any
(Johnson/Road/FormsKeysAdmit.lean) gives such a world, worldAt, for any cells.
Does not say: that the public premises of fits_of_layout_any hold together at a shape (a run at a
made-up shape, without Sized and Numerals: Johnson/Road/FormsKeysRun8.lean).
-/
import Johnson.Road.Ends.AlgLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Ends
open OnBytes.Model (Reading World Aff tenCell TenAt)
open OnBytes.Model.Layer (Env Ten)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr val xS)

section Ties

variable {K : Type} [Field K]

/-- G.lean's reading, as the cells of Johnson/Road/FormsKeysKit.lean: matrix number (0 af, 1 ad, 2
ar, 3 qa; 4 the stream that comes in, 5 the stream that goes out), feature, token. -/
def cG (P : Model.Layer.Pub) (cell : G.NameG → K) : Cells K := fun mat φ i =>
  if mat = 4 then cell (G.cellAt (G.iXI P.y) P.y.mxb P.y.kxb P.y.T φ i)
  else if mat = 5 then cell (G.cellAt (G.iXO P.y) P.y.mxb P.y.kxb P.y.T φ i)
  else cell (G.famCell P.y mat φ i)

/-- A tensor that tensorAt finds is the layout's tensor of that name. -/
theorem T_of_tensorAt {v : Env} {X Z : String} {ten : Ten} {b : ℕ}
    (h : v.tensorAt X Z = some (ten, b)) : v.y.T_ X = some ten := by
  unfold Env.tensorAt at h
  obtain ⟨t0, h1, h2⟩ := bind_some h
  obtain ⟨tb, _, h4⟩ := bind_some h2
  have e : (t0, tb) = (ten, b) := Option.some.inj h4
  rw [h1, (Prod.mk.inj e).1]

variable {P : Model.Layer.Pub} {cell : G.NameG → K} {t : Cell → K}

/-- The library's value of a tied array is G.lean's tensor of its name, plus the offset. -/
theorem val_of_tied {X : Arr} {Tn : Ten} (hT : P.y.T_ (arrName X) = some Tn)
    (Ti : Tied (cG P cell) t X Tn.mat Tn.place) (hm : Tn.mat < 4) (inst j i : ℕ) :
    val t X inst j i = G.ten P cell (arrName X) inst j i + ((X.off : ℤ) : K) := by
  have h := tied_raw Ti inst j i
  unfold raw at h
  have e : G.ten P cell (arrName X) inst j i =
      ∑ k ∈ range Tn.place.nl, (256 : K) ^ k * cG P cell Tn.mat (tenCell Tn.place k inst j) i := by
    unfold G.ten
    rw [hT]
    show G.sumN Tn.nl (fun l => (256 : K) ^ l *
      cell (G.famCell P.y Tn.mat (Tn.OFF + (l * Tn.cnt + inst) * Tn.J + j) i)) = _
    rw [sumN_eq]
    refine sum_congr rfl fun k _ => ?_
    unfold cG
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  rw [e, h]
  ring

/-- A border of the stream, tied at the stream's place, is G.lean's xb. -/
theorem raw_of_border {X : Arr} {mat M0 : ℕ} (Ti : Tied (cG P cell) t X mat P.y.xb)
    (hxb : P.y.xb = ⟨0, P.y.h.xl, 1, P.y.h.d⟩)
    (hc : ∀ φ i, cG P cell mat φ i = cell (G.cellAt M0 P.y.mxb P.y.kxb P.y.T φ i)) (j i : ℕ) :
    raw t X 0 j i = G.xb P cell M0 j i := by
  rw [← tied_raw Ti 0 j i]
  unfold G.xb
  rw [sumN_eq, hxb]
  refine sum_congr rfl fun k _ => ?_
  rw [hc]
  have e : tenCell ⟨0, P.y.h.xl, 1, P.y.h.d⟩ k 0 j = k * P.y.h.d + j := by
    unfold tenCell
    simp
  rw [e]

end Ties

section Fits

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {t : Cell → K} {low u : ℕ → K} {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}

/-- **TiesG follows from Fits.** -/
theorem ties_of_fits (F : Fits ρ W v D (cG P cell) t low u) (hy : v.y = P.y) (hsc : v.sc = P.sc)
    (hg : v.g = g) (hm : ∀ (n : String) (Tn : Ten), P.y.T_ n = some Tn → Tn.mat < 4)
    (hxb : P.y.xb = ⟨0, P.y.h.xl, 1, P.y.h.d⟩) : TiesG P g cell D t := by
  have vLong : ∀ X : Arr, readLong X = true → ∀ inst j i : ℕ,
      val t X inst j i = G.ten P cell (arrName X) inst j i + ((X.off : ℤ) : K) := by
    intro X hX inst j i
    obtain ⟨ten, b, h1, h2, -⟩ := F.long X hX
    have hT : P.y.T_ (arrName X) = some ten := hy ▸ T_of_tensorAt h1
    exact val_of_tied hT h2 (hm _ _ hT) inst j i
  have vShort : ∀ X : Arr, readShort X = true → ∀ inst j i : ℕ,
      val t X inst j i = G.ten P cell (arrName X) inst j i + ((X.off : ℤ) : K) := by
    intro X hX inst j i
    obtain ⟨ten, b, h1, h2, -⟩ := F.short X hX
    have hT : P.y.T_ (arrName X) = some ten := hy ▸ T_of_tensorAt h1
    exact val_of_tied hT h2 (hm _ _ hT) inst j i
  have vRow : ∀ inst j i : ℕ,
      val t .D inst j i = G.ten P cell (arrName .D) inst j i + ((Arr.off .D : ℤ) : K) := by
    intro inst j i
    obtain ⟨trow, b, -, h2, -, h4, -⟩ := F.rowTab
    have hT : P.y.T_ (arrName .D) = some trow := hy ▸ h2
    exact val_of_tied hT h4 (hm _ _ hT) inst j i
  obtain ⟨bI, bO, bF, txs, -, -, -, -, -, t0, t8, -⟩ := F.stream
  rw [hy] at t0 t8
  have hLam : P.y.Lam = D.nl := hy ▸ F.Lam
  refine
    { val := fun X hX inst j i => ?_
      xs := fun s j i _ => ?_
      p3 := hy ▸ F.p3, gcl := hy ▸ F.gcl, rcl := hy ▸ F.rcl, xl := hy ▸ F.xl, hq := hy ▸ F.hq
      hv := hy ▸ F.hv, ho := hy ▸ F.ho, hgD := hy ▸ F.hgD, huD := hy ▸ F.huD, hdD := hy ▸ F.hdD
      hr := hy ▸ F.hr, fe := hy ▸ F.fe, NE := hy ▸ F.NE, dq := hy ▸ F.dq
      kq := fun lam h => ?_, kk := fun lam h => ?_, kv := fun lam h => ?_, ko := fun lam h => ?_
      kg := fun lam h => ?_, ku := fun lam h => ?_, kd := fun lam h => ?_, K1 := fun lam h => ?_
      K2 := fun lam h => ?_, kr := fun lam h h' => ?_, kgR := fun lam h h' => ?_
      kuR := fun lam h h' => ?_, K1le := F.K1le, K2le := F.K2le }
  · cases X <;> first
      | exact absurd hX (by decide)
      | exact vLong _ rfl inst j i
      | exact vShort _ rfl inst j i
      | exact vRow inst j i
  · unfold G.xs
    by_cases h0 : s = 0
    · subst h0
      have b0 : ((0 : ℕ) == 0) = true := rfl
      rw [b0, if_pos rfl, xS_first]
      exact raw_of_border t0 hxb (fun _ _ => by unfold cG; rw [if_pos rfl]) j i
    · have b0 : (s == 0) = false := by simpa using h0
      rw [b0, if_neg Bool.false_ne_true]
      by_cases h1 : s = 2 * D.nl
      · have b1 : (s == 2 * P.y.Lam) = true := by rw [hLam]; simpa using h1
        rw [b1, if_pos rfl, xS_last D t h0 h1]
        exact raw_of_border t8 hxb
          (fun _ _ => by unfold cG; rw [if_neg (by decide), if_pos rfl]) j i
      · have b1 : (s == 2 * P.y.Lam) = false := by rw [hLam]; simpa using h1
        rw [b1, if_neg Bool.false_ne_true, xS_mid D t h0 h1]
        unfold raw
        rw [vLong .xs rfl]
        simp [arrName, Arr.off]
  · rw [← hsc, ← hg, ← hy]; exact F.kq lam h
  · rw [← hsc, ← hg, ← hy]; exact F.kk lam h
  · rw [← hsc, ← hg, ← hy]; exact F.kv lam h
  · rw [← hsc, ← hg, ← hy]; exact F.ko lam h
  · rw [← hsc, ← hg, ← hy]; exact F.kg lam h
  · rw [← hsc, ← hg, ← hy]; exact F.ku lam h
  · rw [← hsc, ← hg, ← hy]; exact F.kd lam h
  · rw [← hsc, ← hg, ← hy]; exact F.K1 lam h
  · rw [← hsc, ← hg, ← hy]; exact F.K2 lam h
  · rw [← hsc, ← hg, ← hy]; exact F.kr lam h h'
  · rw [← hsc, ← hg, ← hy]; exact F.kgR lam h h'
  · rw [← hsc, ← hg, ← hy]; exact F.kuR lam h h'

end Fits

#print axioms ties_of_fits

end OnBytes.Road.Alg
