-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByCols.lean: proof of `Spec.col_eq` (RunBySpec.lean). The
column of the tree that a code switch sends is the same list of words, at every position, whether
it is computed on words (`colOf`, Fmt/M1Own.lean) or over the field (`aCol`,
Johnson/Desc/K12/Honest/Stages.lean). Hypotheses: h ≤ k, `Tab`, and k = 0 at a last stage.

  `colBy_eq`     the proof
  `col_symE_wr`, `col_fresh`, `col_main0`, `col_mask0`   lemmas on one symbol, one block, one row
  `col_tab`      `Tab` can always be met
  `col_parts`    k = 0 at a last stage is needed: an example with k = 1 where the columns differ

By what. A symbol computed on words has words below the prime (`okE_symE`,
OnBytes/Slice/SimBase.lean) and decodes to the field's symbol of the decoded lists (`toE_symE`,
OnBytes/Slice/SimBasic.lean), so it is that symbol, encoded (`eq_ofE`, RunByTab.lean).

Limits.
- Whether the hypothesis h ≤ k is needed is not shown.
- The first tree's column (`colOf` at first = true) is not covered.
- Two definitions give the same words. Nothing follows on trees, salts or hashes, or on what a
  verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTab
import OnBytes.Slice.SimBase
import Johnson.Prover.Link.BaseClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE lst toE_symE okE_symE rowNo_zero)
open Johnson.Prover.Link (PS wr μOf symG symG_congr lst_wr mainOf maskOf muOf_main muOf_mask
  lastCol stageColW freshSym wordsOf)
open Fmt.M1 (E Code Stage symE cp)
open Fmt.M1.Own (PSt colOf syms words)
open H2K.Pub (sgOf)

/-! ## 1 Symbols -/

/-- A symbol computed on words is the field's symbol of the decoded lists, encoded. -/
theorem col_symE (C : Code) (x : ℕ) (m rho : List E) :
    symE C x m rho = ofE (symG C x (lst m) (lst rho)) :=
  eq_ofE (okE_symE C x m rho) (toE_symE C x m rho)

theorem col_symE_wr (C : Code) (x : ℕ) (f g : ℕ → GE) :
    symE C x (wr C.l f) (wr C.r g) = ofE (symG C x f g) := by
  rw [col_symE, symG_congr C x (lst (wr C.l f)) f (lst (wr C.r g)) g
    (fun j hj => lst_wr _ _ j hj) fun q hq => lst_wr _ _ q hq]

theorem col_syms (C : Code) (x n : ℕ) (F G : ℕ → ℕ → GE) :
    syms C x ((List.range n).map fun b => wr C.l (F b)) ((List.range n).map fun b => wr C.r (G b)) =
      wr n fun b => symG C x (F b) (G b) := by
  unfold syms
  rw [List.length_map, List.length_range]
  refine List.map_congr_left fun b hb => ?_
  have hb' : b < n := List.mem_range.1 hb
  show symE C x (((List.range n).map fun b => wr C.l (F b)).getD b [])
    (((List.range n).map fun b => wr C.r (G b)).getD b []) = ofE (symG C x (F b) (G b))
  rw [getD_range n _ _ b hb', getD_range n _ _ b hb', col_symE_wr]

theorem col_syms_one (C : Code) (x : ℕ) (f g : ℕ → GE) :
    syms C x [wr C.l f] [wr C.r g] = [ofE (symG C x f g)] := by
  show [symE C x (wr C.l f) (wr C.r g)] = _
  rw [col_symE_wr]

/-! ## 2 The one row of a stage with k = 0 and h = 0 -/

/-- At k = 0 and h = 0 the message's one main row is the main table, below the row's length. -/
theorem col_main0 (s : Stage) (P : PS) (k0 : s.k = 0) (h0 : s.h = 0) (j : ℕ) (hj : j < s.C.l) :
    mainOf (sgOf s) (μOf (sgOf s) P) j = P.tabM j := by
  have e : (sgOf s).h + (sgOf s).g = 0 := by
    rw [sg_k (s := s) (by omega), k0]
  unfold mainOf
  rw [dif_pos (show j < (sgOf s).C.l from hj), muOf_main, rowNo_zero e, e, pow_zero, one_mul,
    zero_add]

/-- At h = 0 the message's one mask row is the mask table, below the row's length. -/
theorem col_mask0 (s : Stage) (P : PS) (h0 : s.h = 0) (j : ℕ) (hj : j < s.Z.l) :
    maskOf (sgOf s) (μOf (sgOf s) P) j = P.tabZ j := by
  have e : (sgOf s).h = 0 := h0
  unfold maskOf
  rw [dif_pos (show j < (sgOf s).Z.l from hj), muOf_mask, rowNo_zero e, e, pow_zero, one_mul,
    zero_add]

/-! ## 3 The two columns -/

/-- The column at a stage that is not the last: a symbol of each main row, of each mask row, and of
each row of the fresh table. -/
theorem col_mid (s : Stage) (P : PS) (p : PSt) (hk : s.h ≤ s.k) (T : Tab s false P p) (x : ℕ) :
    colOf s false false p x = stageColW (sgOf s) P.tabM P.tabZ P.tM P.tZ P.fM P.fT x := by
  have hP : p.P = (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b) := T.ride
  have hPi : p.Pi = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b) := T.rideT
  show (syms s.C x p.M p.Rh).flatMap words ++
      (syms s.Z (cp s.Z x) p.W p.Sg ++ syms s.Z (cp s.Z x) p.P p.Pi).flatMap words =
    wordsOf (wr (2 ^ ((sgOf s).h + (sgOf s).g))
        (fun b => symG s.C x (fun j => P.tabM (b + 2 ^ ((sgOf s).h + (sgOf s).g) * j)) (P.tM b)) ++
      (wr (2 ^ s.h) (fun b => symG s.Z (x % 2 ^ s.Z.a) (fun j => P.tabZ (b + 2 ^ s.h * j)) (P.tZ b))
        ++ wr (2 ^ s.h) fun b => symG s.Z (x % 2 ^ s.Z.a) (P.fM b) (P.fT b)))
  rw [sg_k hk, T.main, T.mainT, T.mask, T.maskT, hP, hPi,
    col_syms s.C x (2 ^ s.k) (fun b c => P.tabM (b + 2 ^ s.k * c)) P.tM,
    col_syms s.Z (cp s.Z x) (2 ^ s.h) (fun b c => P.tabZ (b + 2 ^ s.h * c)) P.tZ,
    col_syms s.Z (cp s.Z x) (2 ^ s.h) P.fM P.fT, ← List.flatMap_append]
  rfl

/-- The third block of the column of `col_mid`: a symbol of each row of the fresh table. -/
theorem col_fresh (s : Stage) (P : PS) (p : PSt) (T : Tab s false P p) (x : ℕ) :
    (syms s.Z (cp s.Z x) p.P p.Pi).flatMap words =
      wordsOf (wr (2 ^ (sgOf s).h) (freshSym (sgOf s) P.fM P.fT x)) := by
  have hP : p.P = (List.range (2 ^ s.h)).map fun b => wr s.Z.l (P.fM b) := T.ride
  have hPi : p.Pi = (List.range (2 ^ s.h)).map fun b => wr s.Z.r (P.fT b) := T.rideT
  rw [hP, hPi, col_syms s.Z (cp s.Z x) (2 ^ s.h) P.fM P.fT]
  rfl

/-- The column at a last stage with k = 0 and h = 0: the message's main symbol, the masking word's,
the message's mask symbol, the masking word's. -/
theorem col_last (s : Stage) (P : PS) (p : PSt) (k0 : s.k = 0) (h0 : s.h = 0)
    (T : Tab s true P p) (x : ℕ) : colOf s false true p x = lastCol (sgOf s) P x := by
  have hP : p.P = [wr s.C.l P.sM, wr s.Z.l (P.fM 0)] := T.ride
  have hPi : p.Pi = [wr s.C.r P.sT, wr s.Z.r (P.fT 0)] := T.rideT
  have cM := symG_congr s.C x (fun c => P.tabM (0 + 2 ^ 0 * c)) (mainOf (sgOf s) (μOf (sgOf s) P))
    (P.tM 0) (P.tM 0) (fun j hj => by
      show P.tabM (0 + 2 ^ 0 * j) = _
      rw [col_main0 s P k0 h0 j hj, pow_zero, one_mul, zero_add]) fun _ _ => rfl
  have cW := symG_congr s.Z (cp s.Z x) (fun c => P.tabZ (0 + 2 ^ 0 * c))
    (maskOf (sgOf s) (μOf (sgOf s) P)) (P.tZ 0) (P.tZ 0) (fun j hj => by
      show P.tabZ (0 + 2 ^ 0 * j) = _
      rw [col_mask0 s P h0 j hj, pow_zero, one_mul, zero_add]) fun _ _ => rfl
  have hM : syms s.C x p.M p.Rh =
      [ofE (symG s.C x (mainOf (sgOf s) (μOf (sgOf s) P)) (P.tM 0))] := by
    rw [T.main, T.mainT, col_syms s.C x (2 ^ s.k) (fun b c => P.tabM (b + 2 ^ s.k * c)) P.tM, k0,
      ← cM]
    rfl
  have hW : syms s.Z (cp s.Z x) p.W p.Sg =
      [ofE (symG s.Z (cp s.Z x) (maskOf (sgOf s) (μOf (sgOf s) P)) (P.tZ 0))] := by
    rw [T.mask, T.maskT,
      col_syms s.Z (cp s.Z x) (2 ^ s.h) (fun b c => P.tabZ (b + 2 ^ s.h * c)) P.tZ, h0, ← cW]
    rfl
  show ((syms s.C x p.M p.Rh ++ syms s.C x (p.P.take 1) (p.Pi.take 1)) ++
      (syms s.Z (cp s.Z x) p.W p.Sg ++
        syms s.Z (cp s.Z x) (p.P.drop 1) (p.Pi.drop 1))).flatMap words = _
  rw [hM, hW, hP, hPi]
  show (([_] ++ syms s.C x [wr s.C.l P.sM] [wr s.C.r P.sT]) ++
      ([_] ++ syms s.Z (cp s.Z x) [wr s.Z.l (P.fM 0)] [wr s.Z.r (P.fT 0)])).flatMap words = _
  rw [col_syms_one, col_syms_one]
  rfl

theorem colBy_eq : Spec.col_eq := by
  intro s last P p hk h0 T
  funext x
  cases last with
  | false => exact col_mid s P p hk T x
  | true => exact col_last s P p (h0 rfl) (by have := h0 rfl; omega) T x

/-! ## 4 The hypotheses: `Tab` can always be met; k = 0 at a last stage is needed -/

/-- For every stage and every state P some lists of words satisfy `Tab`. -/
theorem col_tab (s : Stage) (last : Bool) (P : PS) : ∃ p : PSt, Tab s last P p :=
  ⟨⟨_, _, _, _, _, _⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- At a last stage with k = 1 and h = 0 the two columns can differ: `colOf` has a symbol of each of
the two main rows, `aCol` of one. One example is shown: both codes have a = l = r = 0, the state
holds zeros, and the lengths of the two columns at position 0 are compared. -/
theorem col_parts : ∃ (s : Stage) (P : PS) (p : PSt), s.h ≤ s.k ∧ Tab s true P p ∧
    colOf s false true p ≠ aCol true s P := by
  refine ⟨⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 1, 0, 0⟩,
    ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
      fun _ => 0⟩,
    ⟨_, _, _, _, _, _⟩, Nat.zero_le _, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun e => ?_⟩
  have l := congrArg List.length (congrFun e 0)
  exact absurd l (by decide)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.col_symE
#print axioms ProofFile.Honest.K12.Light.col_symE_wr
#print axioms ProofFile.Honest.K12.Light.col_syms
#print axioms ProofFile.Honest.K12.Light.col_syms_one
#print axioms ProofFile.Honest.K12.Light.col_main0
#print axioms ProofFile.Honest.K12.Light.col_mask0
#print axioms ProofFile.Honest.K12.Light.col_mid
#print axioms ProofFile.Honest.K12.Light.col_fresh
#print axioms ProofFile.Honest.K12.Light.col_last
#print axioms ProofFile.Honest.K12.Light.colBy_eq
#print axioms ProofFile.Honest.K12.Light.col_tab
#print axioms ProofFile.Honest.K12.Light.col_parts
