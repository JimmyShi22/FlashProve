-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndSame.lean: which fields of the smallness test's state two of its routines
set, and that the shapes that addTreesF lays fit the matrices (OnBytes/Model/Tail.lean).

Definitions, statements and proofs.
Main names:
  `linJoin9_spec`, `linBits9_spec`: the state that comes back is the one that went in but for one
    field.
  `Fits tl`: each shape has its matrix's numbers of rows of cells and of columns. `Fits.of_same`.
  `addTreesF_fits`: what addTreesF returns has `Fits`, and one shape for each matrix.
Limits: nothing on what the routines do to the sub-proof's state or to the chain.
-/
import OnBytes.Tie.Pv.Tail.EndLoops
import OnBytes.Tie.Pv.Tail.EndClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

/-! ## Two routines, one by one -/

theorem linJoin9_spec (tl tl' : HTailF2) (F F' : Fork) (c c' : Ctx)
    (h : tl.linJoin9 F c = .ok ((tl', F'), c')) : tl' = { tl with joinObj9 := tl'.joinObj9 } := by
  unfold HTailF2.linJoin9 at h
  simp only [bind_ok, pure_ok] at h
  iterate 9 obtain ⟨_, _, _, _, h⟩ := h
  obtain ⟨rfl, _, _⟩ := h
  rfl

theorem linBits9_spec (tl tl' : HTailF2) (F F' : Fork) (c c' : Ctx)
    (h : tl.linBits9 F c = .ok ((tl', F'), c')) :
    tl' = { tl with bitFactor9 := tl'.bitFactor9 } := by
  unfold HTailF2.linBits9 at h
  simp only [bind_ok, pure_ok] at h
  iterate 6 obtain ⟨_, _, _, _, h⟩ := h
  obtain ⟨rfl, _, _⟩ := h
  rfl

/-! ## The shapes fit the matrices -/

theorem excBind_ok {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

/-- The shapes fit the matrices: rows of cells and columns. -/
def Fits (tl : HTailF2) : Prop :=
  ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).m = (tl.mats.getD mu {}).m ∧
    (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k

/-- Fits reads NM, shp and mats alone. -/
theorem Fits.of_same {a b : HTailF2} (h : Fits a) (h1 : b.NM = a.NM) (h2 : b.shp = a.shp)
    (h3 : b.mats = a.mats) : Fits b := by
  intro mu hmu
  rw [h2, h3]
  exact h mu (h1 ▸ hmu)

theorem throw_bind_ne {α β : Type} (e : String) (f : α → Except String β) (b : β) :
    ((throw e : Except String α) >>= f) ≠ .ok b := by
  intro h
  cases h

theorem ite_throw_ok {β : Type} (c : Prop) [Decidable c] (e : String)
    (k : PUnit → Except String β) (b : β) :
    (if c then ((throw e : Except String PUnit) >>= k) else (pure PUnit.unit >>= k)) = .ok b ↔
      ¬ c ∧ k PUnit.unit = .ok b := by
  by_cases hc : c
  · simp only [hc, not_true_eq_false, false_and, iff_false]
    exact throw_bind_ne _ _ _
  · simp only [hc, not_false_eq_true, true_and]
    rfl

/-- addTreesF's last test: in the record that it returns the shapes fit the matrices; it has one
shape
for each matrix; and it turns nUF, tabFirst, tabLen, plOwn, plFor, shp alone. -/
theorem addTreesF_fits (tl tl' : HTailF2) (F F' : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    Fits tl' ∧ tl'.shp.size = tl'.NM ∧
      tl' = { tl with nUF := tl'.nUF, tabFirst := tl'.tabFirst, tabLen := tl'.tabLen,
                      plOwn := tl'.plOwn, plFor := tl'.plFor, shp := tl'.shp } := by
  unfold HTailF2.addTreesF at h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r1, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r2, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r3, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨gz, Fz, Tz⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨⟨gb, Fb, Tb⟩, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r4, _, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨hfit, h⟩ := (ite_throw_ok _ _ _ _).1 h
  have e := Except.ok.inj h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, _, _⟩ := e
  refine ⟨?_, by simp, rfl⟩
  intro mu hmu
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, beq_iff_eq] at hfit
  exact hfit mu hmu

#print axioms addTreesF_fits
#print axioms linJoin9_spec
#print axioms linBits9_spec

end OnBytes.Tie.Pv.Tail.Port
