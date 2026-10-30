-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Bools.lean: the two conditions on the public record that kind K13's laws
promise and ask (`FrontOk`, Johnson/Desc/K13/Law/M4Law.lean; `EvalLaid`,
Johnson/Desc/K13/Law/Laid.lean), as tests with code, so that a run can evaluate them at a record.
Definitions, and statements with their proofs.
Main names:
  `claimMadeB`, `claimMade_iff`: a claim is made of a row exactly if each of its single entries is
    on mask rows.
  `frontOkB P s`, `frontOkB_iff`. `evalInB`, `evalInB_iff`. `evalLaidB P s`, `evalLaidB_iff`.
Equality of two rows of the statement is decided field by field: the instances are derived here,
inside this file's namespace, so that their names are its own.
Used of `verify-on-bytes`, pure functions: `linEvalRow`, `linLayW`, `memberClaim`.

What is not claimed. That either test says yes at a real record: neither has been run. That later
blocks keep `EvalLaid` or `FrontOk`: claimed by nobody.

-/
import Johnson.Desc.K13.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame)

deriving instance DecidableEq for OnBytes.Tensor
deriving instance DecidableEq for OnBytes.Term
deriving instance DecidableEq for OnBytes.Single
deriving instance DecidableEq for OnBytes.Coeffs
deriving instance DecidableEq for OnBytes.Run
deriving instance DecidableEq for OnBytes.Form
deriving instance DecidableEq for OnBytes.MainForm
deriving instance DecidableEq for OnBytes.Row

/-- Each single entry of the claim is on mask rows. -/
def claimMadeB (c : LinClaim) : Bool := c.masks.toList.all fun u => decide (u.part = .mask)

/-- A claim is made of a row exactly if each of its single entries is on mask rows. -/
theorem claimMade_iff (c : LinClaim) : claimMadeB c = true ↔ ∃ row, c = memberClaim row := by
  constructor
  · intro h
    refine ⟨rowOfClaim c, ?_⟩
    simp only [claimMadeB, List.all_eq_true, decide_eq_true_eq] at h
    have e : (((c.masks.toList.map fun m => ((⟨m.oracle, m.index⟩ : Slot), m.coeff)).map
        fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single))) = c.masks.toList := by
      rw [List.map_map]
      refine (List.map_congr_left fun u hu => ?_).trans (List.map_id _)
      show (⟨u.oracle, .mask, u.index, u.coeff⟩ : Single) = u
      rw [← h u hu]
    show c = { g := c.g, psi := c.psi, masks := (List.map _ (List.map _ c.masks.toList)).toArray,
               target := c.target }
    rw [e]
  · rintro ⟨row, rfl⟩
    simp [claimMadeB, memberClaim]

/-- `FrontOk`, as a test with code. -/
def frontOkB (P : Where) (s : S) : Bool :=
  match linAt s with
  | none => true
  | some l => claimMadeB l.claim && decide (P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits)

/-- It says yes exactly where the condition holds. -/
theorem frontOkB_iff {F : Frame} (P : Where) (s : S) (y : F.E.Str) :
    frontOkB P s = true ↔ FrontOk P ((s, y) : S × F.E.Str) := by
  unfold frontOkB FrontOk
  cases hl : linAt s with
  | none => simp
  | some l =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, claimMade_iff, Option.some.injEq]
    exact ⟨fun h l' e => by rw [← e]; exact h, fun h => h l rfl⟩

/-- `EvalIn`, as a test with code. -/
def evalInB (St : Statement) (w : ℕ) (lay : VectorLay) (masks : MaskForm) : Bool :=
  decide (w < St.oracles.size) && decide (tableSize St w .main = 2 ^ lay.bits) &&
    masks.all fun t => decide (t.1.oracle < St.oracles.size) &&
      decide (t.1.index < tableSize St t.1.oracle .mask)

/-- It says yes exactly where the condition holds. -/
theorem evalInB_iff (St : Statement) (w : ℕ) (lay : VectorLay) (masks : MaskForm) :
    evalInB St w lay masks = true ↔ EvalIn St w lay masks := by
  simp only [evalInB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.there, h.size⟩, h.masks⟩⟩

/-- `EvalLaid`, as a test with code. -/
def evalLaidB (P : Where) (s : S) : Bool :=
  match linAt s with
  | none => false
  | some l =>
    claimMadeB l.claim && decide (P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits) &&
      match linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin), s.st.groups[l.own]? with
      | some r, some G =>
        decide (r ∈ G.rows.toList) &&
          evalInB s.st l.w (linLayW s.st.codes P.lin) (rowOfClaim l.claim).masks
      | _, _ => false

/-- It says yes exactly where the condition holds. -/
theorem evalLaidB_iff (P : Where) (s : S) : evalLaidB P s = true ↔ EvalLaid P s := by
  unfold evalLaidB EvalLaid
  constructor
  · intro h
    cases hl : linAt s with
    | none =>
      rw [hl] at h
      cases h
    | some l =>
      rw [hl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hc, hb⟩, h3⟩ := h
      obtain ⟨row, hrow⟩ := (claimMade_iff _).1 hc
      cases hr : linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin) with
      | none =>
        rw [hr] at h3
        cases h3
      | some r =>
        cases hG : s.st.groups[l.own]? with
        | none =>
          rw [hr, hG] at h3
          cases h3
        | some G =>
          rw [hr, hG] at h3
          simp only [Bool.and_eq_true, decide_eq_true_eq, evalInB_iff] at h3
          refine ⟨l, row, r, G, rfl, hrow, hb, by rw [← hrow]; exact hr, hG, h3.1, ?_⟩
          have e : (rowOfClaim l.claim).masks = row.masks := by rw [hrow, rowOfClaim_member]
          rw [← e]
          exact h3.2
  · rintro ⟨l, row, r, G, hl, hrow, hb, hr, hG, hm, hE⟩
    rw [hl]
    have hr' : linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin) = some r := by
      rw [hrow]
      exact hr
    simp only [hr', hG, Bool.and_eq_true, decide_eq_true_eq, evalInB_iff]
    refine ⟨⟨(claimMade_iff _).2 ⟨row, hrow⟩, hb⟩, hm, ?_⟩
    rw [hrow, rowOfClaim_member]
    exact hE

end VerifiableInference.Desc.K13.Law
