-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/Join.lean: THE RUN ON SHAPES AT EVERY FILES IN THE GOALS' SCOPE, FROM THE
RUN AT THE STORED FULL-SIZE FILES AND THE STEPS' RELATION. A joining; nothing is evaluated.

* CellRel X X₀ n c c': the first halves of two cells at member n go alike under RelAt (Scope/Rel.lean).
* steps_rel: the table's cells at X and X₀ go alike at every member below 358, from the same of the
  front, of each link's fourteen places, of the head's sixteen and of the five behind.
* **table_yes_in_scope**: under the head at ANY Z, baseOf's return, the steps' relation, hsz, and
  RunsAll's pieces at the stored files: the premise hyes of first_chain_debts at Z.

Limits. THE STEPS' RELATION AND THE PIECES ARE PREMISES HERE. hsz is a premise: the side library
shows it. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Sim
import Johnson.AtFull.Shape.Scope.RelScope
import Johnson.AtFull.Shape.JoinTable

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

/-- The first halves of two cells at member n go alike. -/
def CellRel (X X₀ : Verify.Public) (n : Nat) (c c' : Cell) : Prop :=
  ∀ a a', RelAt X X₀ n a a' → Alike (RelAt X X₀ (n + 1)) (c.1 a) (c'.1 a')

/-- Outside an attention link, cells with equal first halves go alike. -/
theorem cellRel_of_eq {X X₀ : Verify.Public} {n : Nat} {c c' : Cell} (hO : oddAt n = false)
    (e : c.1 = c'.1) : CellRel X X₀ n c c' := by
  intro a a' h
  have h' : a = a' := by
    unfold RelAt at h
    rw [hO] at h
    exact h
  subst h'
  rw [e]
  cases c'.1 a with
  | ok b => exact Or.inl ⟨b, b, rfl, rfl, relAt_of_eq rfl⟩
  | error s => exact Or.inr ⟨rfl, rfl⟩

/-- **THE TABLE's CELLS GO ALIKE**, from its rows. -/
theorem steps_rel {X X₀ : Verify.Public}
    (hF : CellRel X X₀ 0 (liftQ .ok, noVals) (liftQ .ok, noVals))
    (hL : ∀ l j, l < 24 → j < 14 → CellRel X X₀ (14 * l + j + 1)
      ((TabL.linkRow (LW X) l).at j) ((TabL.linkRow (LW X₀) l).at j))
    (hH : ∀ j, j < 16 → CellRel X X₀ (337 + j)
      ((TabL.headRow (LW X)).at j) ((TabL.headRow (LW X₀)).at j))
    (hB : ∀ j, j < 5 → CellRel X X₀ (353 + j)
      ((TabL.backRow (LW X)).at j) ((TabL.backRow (LW X₀)).at j))
    (n : Nat) (hn : n < 358) :
    CellRel X X₀ n (TabL.cells (LW X) n) (TabL.cells (LW X₀) n) := by
  unfold TabL.cells table
  by_cases h0 : n = 0
  · subst h0
    exact hF
  rw [if_neg h0, if_neg h0]
  by_cases h1 : n < 337
  · rw [if_pos h1, if_pos h1]
    have e : n = 14 * ((n - 1) / 14) + (n - 1) % 14 + 1 := by omega
    have k := hL ((n - 1) / 14) ((n - 1) % 14) (by omega) (by omega)
    rw [← e] at k
    exact k
  rw [if_neg h1, if_neg h1]
  by_cases h2 : n < 353
  · rw [if_pos h2, if_pos h2]
    have e : n = 337 + (n - 337) := by omega
    have k := hH (n - 337) (by omega)
    rw [← e] at k
    exact k
  rw [if_neg h2, if_neg h2]
  have e : n = 353 + (n - 353) := by omega
  have k := hB (n - 353) (by omega)
  rw [← e] at k
  exact k

/-- Inside a link: the border behind a place that is not the last has the same answer. -/
theorem oddAt_inside {l j : Nat} (hl : l < 24) (hj : j < 13) :
    oddAt (14 * l + j + 1 + 1) = oddAt (14 * l + j + 1) := by
  unfold oddAt
  have e1 : (14 * l + j + 1 + 1 - 1) / 14 = l := by omega
  have e2 : (14 * l + j + 1 - 1) / 14 = l := by omega
  rw [e1, e2]
  have a1 : decide (1 ≤ 14 * l + j + 1 + 1) = true := by simp
  have a2 : decide (1 ≤ 14 * l + j + 1) = true := by simp
  have b1 : decide (14 * l + j + 1 + 1 < 337) = true := decide_eq_true (by omega)
  have b2 : decide (14 * l + j + 1 < 337) = true := decide_eq_true (by omega)
  rw [a1, a2, b1, b2]

/-- The border at a link's place: the link's parity. -/
theorem oddAt_place {l j : Nat} (hl : l < 24) (hj : j < 14) :
    oddAt (14 * l + j + 1) = (l % 2 == 1) := by
  unfold oddAt
  have e2 : (14 * l + j + 1 - 1) / 14 = l := by omega
  rw [e2]
  have a2 : decide (1 ≤ 14 * l + j + 1) = true := by simp
  have b2 : decide (14 * l + j + 1 < 337) = true := decide_eq_true (by omega)
  rw [a2, b2]
  rfl

/-- No border from the head's link on is an attention link's. -/
theorem oddAt_behind {n : Nat} (hn : 337 ≤ n) : oddAt n = false := by
  unfold oddAt
  have b : decide (n < 337) = false := decide_eq_false (by omega)
  rw [b]
  simp

/-- At 0 neither. -/
theorem oddAt_zero : oddAt 0 = false := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE RUN ON SHAPES RETURNS AT THE HEAD's OWN LETTERS, AT ANY Z**: from the steps' relation
between Z's record and the stored files' record, and the pieces at the stored files. -/
theorem table_yes_in_scope (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hS : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      SameRead Zp.p.X X₀ → ∀ n, n < 358 →
        CellRel Zp.p.X X₀ n (TabL.cells (LW Zp.p.X) n) (TabL.cells (LW X₀) n))
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true := by
  obtain ⟨X₀, hX₀⟩ := record_there hsz
  have hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    ProofFile.Law.pub_public h.laid.pub
  have SR := sameRead_in_scope hX₀ h.scope hX
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  rw [yes_at_LW h O]
  have e : (shapeL (LW Zp.p.X)).yes startShA 358 = (shapeL (LW X₀)).yes startShA 358 :=
    yes_of_rel (RelAt Zp.p.X X₀) (fun n hn a a' hr => hS X₀ hX₀ SR n hn a a' hr)
      (relAt_of_eq rfl)
  rw [e]
  obtain ⟨X₁, hX₁, hl⟩ := atXL_zFull hsz lettersTest_atXL
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX₀)
  rw [yes_at_LWn hl]
  have k := yes_of_runsAll len c K hp X₁ hX₀
  rw [h0, hK] at k
  exact k

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.oddAt_inside
#print axioms Johnson.AtFull.Shape.Scope.oddAt_place
#print axioms Johnson.AtFull.Shape.Scope.oddAt_behind
#print axioms Johnson.AtFull.Shape.Scope.steps_rel
#print axioms Johnson.AtFull.Shape.Scope.table_yes_in_scope
