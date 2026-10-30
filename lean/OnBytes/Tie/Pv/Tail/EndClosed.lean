-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndClosed.lean: the brackets of a tie and of a read with the batching element
written out, behind weightsF (OnBytes/Model/Tail.lean).

Definitions, statements and proofs.
Main names:
  `Powered tl theta`: what powersF sets from the batching element, and its test on the shapes.
  `powersF_spec`, `foldSums_spec`, `weightsF_spec`: which fields these routines set.
  `Powered.wl_val`, `Powered.wr_val`, `Powered.sum_vp`, `Powered.sum_vt`: the weights.
  `Powered.tieBracket_closed`, `Powered.readBracket_closed`: the two brackets.
Limits: the sums over the drawn matrix's columns (gamX, gamV) stay letters here. The entries are
those of virtual rows.

-/
import OnBytes.Tie.Pv.Tail.EndLoops
import OnBytes.Tie.Pv.Tail.EndClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-! ## Sums -/

theorem list_sum_getD {α : Type} (g : α → K) (d : α) :
    ∀ l : List α, (l.map g).sum = ∑ i ∈ Finset.range l.length, g (l.getD i d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', list_sum_getD g d l]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The sum of a vector's entries, read. -/
theorem sumE_sum (v : Array E) :
    ρ.val (sumE v) = ∑ i ∈ Finset.range v.size, ρ.val (v.getD i zeroE) := by
  rw [sumE_val, list_sum_getD ρ.val zeroE]
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem tieLeft_size (s : ShP) (rows lo wl : Array E) (h : tieLeft s rows lo = some wl) :
    wl.size = s.m := by
  unfold tieLeft at h
  split at h
  · cases h
  · have e := Option.some.inj h
    subst e
    simp

/-! ## What weightsF leaves -/

/-- What powersF sets from the batching element, and its test on the shapes. -/
structure Powered (tl : HTailF2) (theta : E) : Prop where
  vp : tl.vp = powers theta tl.tau
  vt : tl.vt = powers theta tl.tau
  rowX : tl.rowX = tl.shp.map fun s => powers (powE theta tl.stepF) s.mS
  loX : tl.loX = tl.shp.map fun _ => #[oneE]
  eqFirst : tl.eqFirst = tl.shp.foldl
    (fun a s => a.push (a.getD (a.size - 1) 0 + tl.stepF * 2 ^ clog2 s.mS)) #[0]
  shape : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).J = 1 ∧ (tl.shp.getD mu {}).Rd = 0 ∧
    (tl.shp.getD mu {}).R = (tl.shp.getD mu {}).mS ∧
    (tl.shp.getD mu {}).Rr = (tl.shp.getD mu {}).mS ∧
    (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3

theorem powersF_spec (tl tl2 : HTailF2) (F : Fork) (h : tl.powersF F = some tl2) :
    Powered tl2 F.theta ∧
      tl2 = { tl with vt := tl2.vt, vp := tl2.vp, eqFirst := tl2.eqFirst, rowX := tl2.rowX,
                      loX := tl2.loX } := by
  unfold HTailF2.powersF at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hc
    have e := Option.some.inj h
    subst e
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, beq_iff_eq,
      List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, fun mu hmu => ?_⟩, rfl⟩
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc.2 mu hmu
    exact ⟨h1, h2, h3, h4, h5⟩

theorem foldSums_spec (x y : HTailF2) (mu : Nat) (h : x.foldSums mu = some y) :
    y = { x with foldTakenF := y.foldTakenF, gamX := y.gamX, gamV := y.gamV } := by
  unfold HTailF2.foldSums at h
  dsimp only at h
  split_ifs at h <;> (cases h; rfl)

theorem foldSums_fold : ∀ (l : List Nat) (x y : HTailF2),
    l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) x = some y →
    y = { x with foldTakenF := y.foldTakenF, gamX := y.gamX, gamV := y.gamV }
  | [], x, y, h => by
    have e : x = y := by simpa using h
    subst e
    rfl
  | mu :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    cases hq : x.foldSums mu with
    | none => simp [hq] at h
    | some t =>
      rw [hq] at h
      have h2 : l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) t = some y := by simpa using h
      have e1 := foldSums_spec x t mu hq
      have e2 := foldSums_fold l t y h2
      rw [e2, e1]

/-- weightsF changes neither state nor context; of the smallness test's state it sets vt, vp,
eqFirst, rowX, loX,
gamX, gamV, foldTakenF alone; and what powersF set stands. -/
theorem weightsF_spec (tl tl1 : HTailF2) (F F1 : Fork) (c c1 : Ctx)
    (h : tl.weightsF F c = .ok ((tl1, F1), c1)) :
    F1 = F ∧ c1 = c ∧ Powered tl1 F.theta ∧
      tl1 = { tl with vt := tl1.vt, vp := tl1.vp, eqFirst := tl1.eqFirst, rowX := tl1.rowX,
                      loX := tl1.loX, gamX := tl1.gamX, gamV := tl1.gamV,
                      foldTakenF := tl1.foldTakenF } := by
  unfold HTailF2.weightsF at h
  simp only [bind_ok, ask_ok, get_ok] at h
  obtain ⟨tl2, F2, c2, ⟨hp, hF, hc⟩, hf, hF', hc'⟩ := h
  obtain ⟨hP, e2⟩ := powersF_spec tl tl2 F hp
  have e1 := foldSums_fold _ _ _ hf
  refine ⟨hF'.trans hF, hc'.trans hc, ?_, ?_⟩
  · rw [e1]
    exact ⟨hP.vp, hP.vt, hP.rowX, hP.loX, hP.eqFirst, hP.shape⟩
  · rw [e1, e2]

/-! ## The letters in closed form -/

theorem getD_map {α β : Type} (f : α → β) (a : Array α) (i : Nat) (d : β) (d' : α)
    (h : i < a.size) :
    (a.map f).getD i d = f (a.getD i d') := by
  simp [Array.getD, h]

namespace Powered
variable {tl : HTailF2} {theta : E} (hP : Powered tl theta)
include hP

theorem sum_vp : ρ.val (sumE tl.vp) = ∑ u ∈ Finset.range tl.tau, ρ.val theta ^ u := by
  rw [sumE_sum, hP.vp, powers_size]
  apply Finset.sum_congr rfl
  intro u hu
  rw [powers_val ρ _ _ _ (Finset.mem_range.1 hu)]

theorem sum_vt : ρ.val (sumE tl.vt) = ∑ u ∈ Finset.range tl.tau, ρ.val theta ^ u := by
  rw [hP.vt, ← hP.vp]
  exact hP.sum_vp ρ

/-- wl[i] = B^(i % 3) theta^(stepF (i / 3)). -/
theorem wl_val (mu : Nat) (hmu : mu < tl.NM) (hsz : mu < tl.shp.size)
    (hm : (tl.shp.getD mu {}).m ≤ 3 * (tl.shp.getD mu {}).mS) (wl : Array E)
    (hwl : tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]) = some wl)
    (i : Nat) (hi : i < (tl.shp.getD mu {}).m) :
    ρ.val (wl.getD i zeroE) = ((2 : K) ^ 20) ^ (i % 3) * ρ.val theta ^ (tl.stepF * (i / 3)) := by
  rw [tieLeft_one ρ _ _ _ _ (hP.shape mu hmu).1 hwl i hi, hP.rowX, hP.loX,
    getD_map _ _ _ _ {} hsz, getD_map _ _ _ _ {} hsz, powers_val ρ _ _ _ (by omega), ρ.pow]
  have : (#[oneE] : Array E).getD 0 zeroE = oneE := rfl
  rw [this, ρ.one, mul_one, ← pow_mul (ρ.val theta)]

/-- wr[p] = gamX[p]. -/
theorem wr_val (mu : Nat) (hmu : mu < tl.NM) (hsz : mu < tl.shp.size) (wr : Array E)
    (hwr : tieRight (tl.shp.getD mu {}) (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]) = some wr)
    (p : Nat) (hp : p < (tl.shp.getD mu {}).k) :
    ρ.val (wr.getD p zeroE) = ρ.val ((tl.gamX.getD mu #[]).getD p zeroE) := by
  rw [tieRight_one ρ _ _ _ _ (hP.shape mu hmu).1 hwr p hp, hP.loX, getD_map _ _ _ _ {} hsz]
  have : (#[oneE] : Array E).getD 0 zeroE = oneE := rfl
  rw [this, ρ.one, mul_one]

/-- The tie's bracket in closed form: theta stands in it through vp, wl (written out) and gamX
alone;
the entries are still those of virtual rows. -/
theorem tieBracket_closed (mu : Nat) (hmu : mu < tl.NM) (hsz : mu < tl.shp.size)
    (hm : (tl.shp.getD mu {}).m ≤ 3 * (tl.shp.getD mu {}).mS) (wl wr : Array E)
    (hwl : tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]) = some wl)
    (hwr : tieRight (tl.shp.getD mu {}) (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]) = some wr) :
    tieBracket ρ W tl mu =
      -((2 : K) ^ 17 * ((∑ u ∈ Finset.range tl.tau, ρ.val theta ^ u)
          * ∑ i ∈ Finset.range (tl.shp.getD mu {}).m,
              ((2 : K) ^ 20) ^ (i % 3) * ρ.val theta ^ (tl.stepF * (i / 3))))
        + ∑ i ∈ Finset.range (tl.shp.getD mu {}).m,
            ((2 : K) ^ 20) ^ (i % 3) * ρ.val theta ^ (tl.stepF * (i / 3))
              * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 0 0).getD 0 + i)
        + (2 : K) ^ 10 * ∑ i ∈ Finset.range (tl.shp.getD mu {}).m,
            ((2 : K) ^ 20) ^ (i % 3) * ρ.val theta ^ (tl.stepF * (i / 3))
              * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 1 0).getD 0 + i)
        - ∑ p ∈ Finset.range (tl.shp.getD mu {}).k,
            ρ.val ((tl.gamX.getD mu #[]).getD p zeroE) * W.entry (tl.gtTree.getD mu 0) 0 p := by
  have hw := hP.wl_val ρ mu hmu hsz hm wl hwl
  have hr := hP.wr_val ρ mu hmu hsz wr hwr
  simp only [tieBracket, hwl, hwr, Option.getD_some, runSum_eq_sum, Nat.zero_add,
    (hP.shape mu hmu).1, Nat.one_mul]
  rw [hP.sum_vp ρ, sumE_sum, tieLeft_size _ _ _ _ hwl]
  congr 1
  · congr 1
    · congr 1
      · congr 3
        exact Finset.sum_congr rfl fun i hi => hw i (Finset.mem_range.1 hi)
      · exact Finset.sum_congr rfl fun i hi => by rw [hw i (Finset.mem_range.1 hi)]
    · congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hw i (Finset.mem_range.1 hi)]
  · exact Finset.sum_congr rfl fun p hp => by rw [hr p (Finset.mem_range.1 hp)]

/-- The read's bracket with its sums written out: theta stands in it through vt (written out) and
gamV alone. -/
theorem readBracket_closed (F0 : Fork) (x : HFun × Nat) :
    readBracket ρ W tl F0 x =
      -((2 : K) ^ 17 * ((∑ j ∈ Finset.range x.1.phi.size, ρ.val (x.1.phi.getD j zeroE))
          * ∑ u ∈ Finset.range tl.tau, ρ.val theta ^ u))
        - ∑ d ∈ Finset.range (tl.mats.getD x.1.mat {}).k,
            ρ.val ((tl.gamV.getD x.1.mat #[]).getD d zeroE)
              * W.entry ((tl.ix.U.getD x.1.tree none).getD 0)
                  (posOf tl x.1 x.2 d / colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0))
                  (posOf tl x.1 x.2 d % colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0))
        + ∑ j ∈ Finset.range x.1.len, ρ.val (x.1.phi.getD j zeroE)
            * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j)
        + (2 : K) ^ 10 * ∑ j ∈ Finset.range x.1.len, ρ.val (x.1.phi.getD j zeroE)
            * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j) := by
  simp only [readBracket, runSum_eq_sum, Nat.zero_add, ρ.mul]
  rw [hP.sum_vt ρ, sumE_sum]

end Powered

#print axioms weightsF_spec
#print axioms Powered.tieBracket_closed
#print axioms Powered.readBracket_closed

end OnBytes.Tie.Pv.Tail.Port
