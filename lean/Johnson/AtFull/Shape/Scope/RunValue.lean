-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/RunValue.lean: THE RUN ON SHAPES AT ANY Z KEEPS ITS VALUE UP TO RelAt: at
every border, the run over the table's own steps under the head at Z and the run over the second
text at the numerals at the stored files both return, in RelAt, or both refuse. A joining; nothing
is evaluated.

* table_run_in_scope: from the steps' relation (CellRel at the members below 358).
* bool_at_border: a Bool on shapes that RelAt cannot part, true at the stored files' border, is
  true at Z's.

Limits. The steps' relation is a premise. At a border of an attention link the two shapes are in
RelX: they may part in the calls' tables in look and lookHeard: a Bool that reads these is not
covered (hβ shuts it out). Nothing says that the run at the stored files returns: hc and h1 are a
closed line at the stored files, owed by whoever wants the Bool; RunsAll's pieces give the run's value
at their own borders alone.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- Equal steps and tests on the right of Alike. -/
theorem alike_right {R : ShA → ShA → Prop} {y : Except String ShA}
    {g g' : Nat → ShA → Except String ShA}
    {v v' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (hg : g = g') (hv : v = v') (b : Nat) (a : ShA)
    (h : Alike (α := ShA) (β := ShA) R y ((firstZA g' v').run b a)) :
    Alike (α := ShA) (β := ShA) R y ((firstZA g v).run b a) := by
  subst hg hv
  exact h

/-- **THE RUN's VALUE AT ANY Z, UP TO RelAt.** -/
theorem table_run_in_scope (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (hS : ∀ n, n < 358 → CellRel Zp.p.X X₀ n (TabL.cells (LW Zp.p.X) n) (TabL.cells (LW X₀) n))
    (b : Nat) (hb : b ≤ 358) :
    Alike (α := ShA) (β := ShA) (RelAt Zp.p.X X₀ b)
      ((firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run b startShA)
      ((shapeL (LWn X₀)).run b startShA) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨X₁, hX₁, hl⟩ := atXL_zFull hsz lettersTest_atXL
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX₀)
  rw [g_of_alike (lw_alike h O), vals_of_alike (lw_alike h O)]
  refine alike_right (g' := fun n => (TabL.cells (LW X₁) n).1) (v' := fun n => (TabL.cells (LW X₁) n).2)
    (funext fun k => congrArg Prod.fst (cells_alike (lwn_alike hl) k).symm)
    (funext fun k => congrArg Prod.snd (cells_alike (lwn_alike hl) k).symm) b startShA ?_
  exact run_rel (shapeL (LW Zp.p.X)) (shapeL (LW X₁)) (RelAt Zp.p.X X₁) (relAt_of_eq rfl) b
    fun n hn c c' q => hS n (by omega) c c' q

/-- **A Bool on shapes that RelAt cannot part, at Z's border.** -/
theorem bool_at_border (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (hS : ∀ n, n < 358 → CellRel Zp.p.X X₀ n (TabL.cells (LW Zp.p.X) n) (TabL.cells (LW X₀) n))
    {b : Nat} (hb : b ≤ 358) (β : ShA → Bool)
    (hβ : ∀ a a', RelAt Zp.p.X X₀ b a a' → β a = β a') {c : ShA}
    (hc : (shapeL (LWn X₀)).run b startShA = .ok c) (h1 : β c = true) :
    ∃ c' : ShA, (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).run b startShA = .ok c' ∧
      β c' = true := by
  rcases table_run_in_scope hsz h hB hX₀ hS b hb with ⟨c1, c2, e1, e2, q⟩ | ⟨-, n2⟩
  · have e : c2 = c := Except.ok.inj (e2.symm.trans hc)
    subst e
    exact ⟨c1, e1, (hβ _ _ q).trans h1⟩
  · rw [hc] at n2
    cases n2

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.table_run_in_scope
#print axioms Johnson.AtFull.Shape.Scope.bool_at_border
