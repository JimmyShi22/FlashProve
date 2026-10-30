-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsRaw.lean: a payer of K08Claims' fifth premise (RawRows) that
goes through no routine of `verify-on-bytes`: from a yes of the plain test by a second computation
(rkSelfTestP, SelfTests.lean), which stands behind the adding.

Statements and proofs. After OnBytes/Tie/Pv/Tail/EndTested.lean (tileSelfTest_ok) and EndRaw.lean
(tileSelfTest_tiles, rawRows_run), which say the like of the routine tileSelfTestF in a context. USED
OF THE FILES UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE, BY NAME IN THIS FILE's OWN CODE:
SelfTested, ReadsRaw, UnitRow, rawRows_tested, zz_rows, tau_lt, blocks_eq, RawRows, readsList, posOf,
uOf, colsU; of the record wants, callHeld, piecesTile. THROUGH rkSelfTestP's TEXT AND ReadsRaw: ReadsRow,
forestHeld, pointsHeld, pieceWeightsHeld, tieShapeHeld, tieWeightsHeld, planesShapeHeld,
planesWeightsHeld, readShapeHeld, readWeightsHeld.
Main names:
  guard_ok: a guard of a plain test, taken apart.
  rk_tested: a yes of rkSelfTestP gives SelfTested and the two public facts on the tiling.
  rawRows_plain: with ReadsRaw at the tested ledger and two premises on public numbers: RawRows.
  **K08Raw** (a closed Prop), **k08_raw**: RawRows as K08Claims asks it.
Limits: ReadsRaw (the world reads the virtual rows in use under the ledger's row weights) stays a
premise, and it is RawRows' whole half on the world: what the test's yes adds is that the written weights
are powers of the batching element, and 1. So do the two on public numbers and "the tested ledger has the
batching element of F". rk_tested spends seven of the test's eleven guards (all eleven: rk_all,
EquationsSelf.lean).

-/
import Johnson.Desc.First.TailClaims.EquationsFrame
import Johnson.Desc.First.TailClaims.SelfTests
import OnBytes.Tie.Pv.Tail.EndRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow rawRows_tested zz_rows tau_lt blocks_eq)

/-- A guard of a plain test: "unless c do throw e", and then the rest. -/
theorem guard_ok {β : Type} (c : Prop) [Decidable c] (e : String) (x : Except String β)
    (k : PUnit → Except String β) (b : β)
    (h : (if c then x else ((throw e : Except String PUnit) >>= k)) = .ok b) :
    c ∧ x = .ok b := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact ⟨hc, h⟩
  · rw [if_neg hc] at h
    cases h

/-- The last guard of a plain test. -/
theorem guard_last (c : Prop) [Decidable c] (e : String) (b : PUnit)
    (h : (if c then pure PUnit.unit else throw e : Except String PUnit) = .ok b) : c := by
  by_cases hc : c
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- A yes of the plain test by a second computation. After tileSelfTest_ok and tileSelfTest_tiles. -/
theorem rk_tested (tl : HTailF2) (F : Fork) (h : rkSelfTestP tl F = .ok ()) :
    SelfTested tl F ∧ ∃ g nbW Wn, tl.heard = some g ∧ tl.wants = some (nbW, Wn) ∧
      ([0, 1].all (tl.callHeld g nbW)) = true ∧ tl.piecesTile F Wn = true := by
  unfold rkSelfTestP at h
  split at h
  case h_2 => cases h
  rename_i g hg
  split at h
  case h_2 => cases h
  rename_i jo hjo
  split at h
  case h_2 => cases h
  rename_i nbW Wn hw
  dsimp only at h
  obtain ⟨h5, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h7, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h8, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h10, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h12, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h14, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨h16, h⟩ := guard_ok _ _ _ _ _ h
  have h18 := guard_last _ _ _ h
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  refine ⟨⟨nbW, Wn, hw, h5.1.1, ?_, ?_, ?_, h16, h18⟩, g, nbW, Wn, hg, hw, h5.2, h7⟩
  · intro mu hmu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h12
    exact h12.1.1.2 mu hmu
  · intro u hu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h14
    have := h14.1.1 u hu
    exact ⟨this.1, this.2.trans this.1⟩
  · intro mu hmu
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h14
    exact h14.1.2 mu hmu

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The four equations, in a world that reads the rows so (ReadsRaw), from a yes of the plain test,
under the two premises on public numbers. After rawRows_run. -/
theorem rawRows_plain (tl : HTailF2) (F G : Fork) (funs : Array HFun) (W : World K)
    (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl funs F W A) (h : rkSelfTestP tl F = .ok ())
    (hrows : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2)
    (hU : ∀ x ∈ readsList tl funs, UnitRow F (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU G (uOf tl x.1)) :
    RawRows W tl G funs (ρ.val F.theta) A := by
  obtain ⟨hT, g, nbW, Wn, -, hw, hc, hp⟩ := rk_tested tl F h
  have hc0 : tl.callHeld g nbW 0 = true := by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    exact hc.1
  have ht := tau_lt tl F g nbW Wn hw hc0 hp
  exact rawRows_tested ρ tl F G funs W A hW hT (zz_rows tl F Wn hp)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by decide))))
    (blocks_eq tl F hT hrows) hU

end

/-- **RawRows, as K08Claims asks it, from the plain test behind the adding.** The list "K8.equations" is
made at the record tl and the ledger F and returns tl' and F1. Later, at a ledger Fc with F's batching
element, the plain test by a second computation says yes at tl' with any lsTail laid. The world reads the
virtual rows in use under Fc's row weights (ReadsRaw); the array of the digits has the virtual rows that
the first computation lays; each table's vector is one row with the weight 1 that holds every place that
a read names. Then RawRows at tl, F1 and F's batching element. -/
def K08Raw : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K) (A : Nat → Nat → Nat → K)
    (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 Fc : Fork) (cls : List Claim)
    (ls : Array E),
    equations front tl funs F = .ok (tl', F1, cls) → Fc.theta = F.theta →
    rkSelfTestP { tl' with lsTail := ls } Fc = .ok () →
    ReadsRaw ρ { tl' with lsTail := ls } funs Fc W A →
    (Fc.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 →
    (∀ x ∈ readsList tl funs, UnitRow Fc (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU F1 (uOf tl x.1)) →
    RawRows W tl F1 funs (ρ.val F.theta) A

theorem k08_raw : K08Raw := by
  intro K _ ρ W A front tl tl' funs F F1 Fc cls ls h hth hrk hW hrows hU
  have c1 : ∀ {α : Sort _} (f : HTailF2 → α),
      (∀ (t : HTailF2) (x : Option Nat), f { t with joinObj9 := x } = f t) →
      (∀ (t : HTailF2) (x : E), f { t with bitFactor9 := x } = f t) →
      (∀ (t u : HTailF2),
        f { t with
            vt := u.vt, vp := u.vp, eqFirst := u.eqFirst, rowX := u.rowX, loX := u.loX,
            gamX := u.gamX, gamV := u.gamV, foldTakenF := u.foldTakenF } = f t) →
      (∀ (t : HTailF2) (x y : Array Nat) (z : Nat),
        f { t with tieObj := x, tiesOn := y, nX4Laid := z } = f t) →
      (∀ (t : HTailF2) (x : Array E), f { t with lsTail := x } = f t) →
      f { tl' with lsTail := ls } = f tl :=
    fun f r1 r2 r3 r4 r5 => (r5 tl' ls).trans (eq_same f h r1 r2 r3 r4)
  have hrows' : (Fc.trees.getD ({ tl' with lsTail := ls } : HTailF2).ix.ZZ {}).rows.size =
      2 * ({ tl' with lsTail := ls } : HTailF2).zzBlocks + 2 := by
    rw [c1 (fun t => (Fc.trees.getD t.ix.ZZ {}).rows.size = 2 * t.zzBlocks + 2)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl)]
    exact hrows
  have hU' : ∀ x ∈ readsList ({ tl' with lsTail := ls } : HTailF2) funs,
      UnitRow Fc (uOf ({ tl' with lsTail := ls } : HTailF2) x.1) ∧
      ∀ d, d < ((({ tl' with lsTail := ls } : HTailF2).mats.getD x.1.mat {}).k) →
        posOf ({ tl' with lsTail := ls } : HTailF2) x.1 x.2 d <
          colsU F1 (uOf ({ tl' with lsTail := ls } : HTailF2) x.1) := by
    rw [c1 (fun t => ∀ x ∈ readsList t funs, UnitRow Fc (uOf t x.1) ∧
        ∀ d, d < (t.mats.getD x.1.mat {}).k → posOf t x.1 x.2 d < colsU F1 (uOf t x.1))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl)]
    exact hU
  have hr := rawRows_plain ρ _ Fc F1 funs W A hW hrk hrows' hU'
  rw [hth] at hr
  exact
    ⟨(c1 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowTies c =
          ∑ u ∈ range t.tau, ρ.val F.theta ^ u * A t.ix.ZZ u c)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ => rfl)).mp hr.ties,
      (c1 (fun t => ∀ c, W.entry t.ix.ZZ t.zzRowReads c =
          ∑ u ∈ range t.tau, ρ.val F.theta ^ u * A t.ix.ZZ u c)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ => rfl)).mp hr.reads,
      (c1 (fun t => ∀ mu, mu < t.NM → ∀ p, W.entry (t.gtTree.getD mu 0) 0 p =
          ∑ i' ∈ range (t.shp.getD mu {}).mS,
            ρ.val F.theta ^ (t.stepF * i') * A (t.gtTree.getD mu 0) i' p)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ => rfl)).mp hr.syms,
      (c1 (fun t => ∀ x ∈ readsList t funs, ∀ d, d < (t.mats.getD x.1.mat {}).k →
          W.entry (uOf t x.1) (posOf t x.1 x.2 d / colsU F1 (uOf t x.1))
            (posOf t x.1 x.2 d % colsU F1 (uOf t x.1)) = A (uOf t x.1) 0 (posOf t x.1 x.2 d))
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (fun _ _ => rfl)).mp hr.tabs⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_raw
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rk_tested
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rawRows_plain
