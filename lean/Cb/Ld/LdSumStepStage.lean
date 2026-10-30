-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepStage.lean: the codes between the folding rounds when the rows of the tables are
indexed by cubes, and the errors of the two kinds of rounds.

Definitions, statements and proofs; they use Cb/Ld/LdSumStepCx.lean and the laws of pairs and
interleavings (Cb/Ld/LdRelProofsCode.lean).

Main names:
  `LdCode.stg C Z Zw k h`, a stage: main rows on the cube of k variables under C, rows of two masks
    on the cube of h variables under Z and Zw, side by side. The first variable is folded first: the
    two halves of a table L are the rows L (Fin.cons false b) and L (Fin.cons true b) (`consB`).
  `Halving.stepA C Z Zw k h`: from the stage (k + 1, h + 1) to the stage (k, h): all three tables
    are halved.
  `Halving.stepB C Z Zw k h`: from the stage (k + 1, h) to the stage (k, h): the main table is
    halved, the masks rest.
  Everything from the three codes: `Spec.lss_stg_laws`, `Spec.lss_stg_dist` (a stage has the laws,
  and the distance d, if C, Z, Zw have), `Spec.lss_stepA_laws`, `Spec.lss_stepB_laws` (the two
  halvings have `Halving.Laws d`: stepA always, stepB if Z and Zw have their laws and the distance
  d).
  `Spec.lss_roundA`, `Spec.lss_roundB`: the error of a round of either kind, as in `Spec.lds_round`
    (Cb/Ld/LdSumStep.lean), with hypotheses on C, Z, Zw (`CodesOK`: laws, distance d > e), the
    agreement counts of the tables after the round, the list of the stage before it, and the premise
    on κ of `Spec.lds_round`.
    Under these hypotheses the number of values γ at which some witness after the round is not taken
    by the extractor (`back`) to a witness before it is at most (b + (bs + bw)) + L κ in
    `Spec.lss_roundA`, at most b + L κ in `Spec.lss_roundB`.
  `Spec.lss_cnt_val`: challenges drawn from any finite set with an injective map to a finite set V
    (in its use: E): the counts over that set are no larger.
  What the folds are, entry by entry: `il_foldW_fst`, `il_foldW_snd`, `il_fold_apply` (by
  definition).

Notation: `e`: a radius, counted in long positions (`LdCode.Near`); `LdCode.Dist d`, of a code `C`:
for all m, r not both 0, `C.T (C.enc m r)` is non-zero at d long positions or more;
`LdCode.ListAt e L`: every native word has at most L pairs (message, randomness) whose encoding is
within e long positions; `LdCode.MCAat e b`, and so at `bs`, `bw` (the agreement counts): mutual
correlated agreement on lines under the transformation, as a count of exceptional θ; `Φ`, `Φ'`: the
claims before and after the round, predicates on pairs (message, randomness) (`Φ'`: one for each
value of the verifier's message); `cnt`: the number of elements of a finite type with a property
(Prob/Cnt.lean). The `LdCode` names of this paragraph are those of Cb/Ld/LdRel.lean.

Limits: what the head of Cb/Ld/LdSumStep.lean lists as not said is not said here either. Here the
laws and the distance are hypotheses on C, Z, Zw, from which those of the stages follow. One round
at a time; the claims Φ, Φ' are arbitrary.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStepCx
import Cb.Ld.LdRelProofsCode
import Cb.Gen.CodeListRows

set_option autoImplicit false

namespace Cb
open Prob LdCode

/-- A corner of the cube of k + 1 variables: its first coordinate and the rest. -/
def consB (k : ℕ) : Bool × (Fin k → Bool) ≃ (Fin (k + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun b := (b 0, Fin.tail b)
  left_inv p := Prod.ext (Fin.cons_zero (α := fun _ => Bool) p.1 p.2)
    (Fin.tail_cons (α := fun _ => Bool) p.1 p.2)
  right_inv b := Fin.cons_self_tail b

/-- A stage. -/
abbrev LdCode.stg {E P : Type} (C Z Zw : LdCode E P) (k h : ℕ) : LdCode E P :=
  (C.il (Fin k → Bool)).pair ((Z.il (Fin h → Bool)).pair (Zw.il (Fin h → Bool)))

namespace Halving
variable {E P : Type}

/-- All three tables are halved in their first variable. -/
def stepA (C Z Zw : LdCode E P) (k h : ℕ) : Halving (stg C Z Zw (k + 1) (h + 1)) (stg C Z Zw k h) :=
  all C Z Zw (consB k) (consB h) (consB h)

/-- The main table is halved in its first variable, the masks rest. -/
def stepB (C Z Zw : LdCode E P) (k h : ℕ) : Halving (stg C Z Zw (k + 1) h) (stg C Z Zw k h) :=
  main C ((Z.il (Fin h → Bool)).pair (Zw.il (Fin h → Bool))) (consB k)

section
variable [Field E] (C : LdCode E P) {R R' : Type} [Fintype R] [DecidableEq R] [Fintype R']
  [DecidableEq R'] (ρ : Bool × R' ≃ R)

theorem il_foldW_fst (γ : E) (w : (C.il R).MR) (j : R' × C.J) :
    ((il C ρ).foldW γ w).1 j = (1 - γ) * w.1 (ρ (false, j.1), j.2) + γ * w.1 (ρ (true, j.1), j.2) :=
  rfl

theorem il_foldW_snd (γ : E) (w : (C.il R).MR) (q : R' × C.Q) :
    ((il C ρ).foldW γ w).2 q = (1 - γ) * w.2 (ρ (false, q.1), q.2) + γ * w.2 (ρ (true, q.1), q.2) :=
  rfl

theorem il_fold_apply (γ : E) (f : (C.il R).Word) (p : C.NP) (s : R' × C.NS p) :
    (il C ρ).fold γ f p s = (1 - γ) * f p (ρ (false, s.1), s.2) + γ * f p (ρ (true, s.1), s.2) :=
  rfl

end
end Halving

namespace Spec
variable (E : Type) [Field E] (P : Type) [Fintype P]

def lss_stg_laws : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h : ℕ), C.Laws → Z.Laws → Zw.Laws → (stg C Z Zw k h).Laws

def lss_stg_dist : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h d : ℕ), C.Dist d → Z.Dist d → Zw.Dist d → (stg C Z Zw k h).Dist d

def lss_stepA_laws : Prop := ∀ (C Z Zw : LdCode E P) (k h d : ℕ), (Halving.stepA C Z Zw k h).Laws d

def lss_stepB_laws : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h d : ℕ),
    Z.Laws → Zw.Laws → Z.Dist d → Zw.Dist d → (Halving.stepB C Z Zw k h).Laws d

/-- What both rounds ask of the three codes.

A condition with parameters, which other statements and theorems use; it is not itself a claim. -/
def CodesOK (C Z Zw : LdCode E P) (d e : ℕ) : Prop :=
  (C.Laws ∧ Z.Laws ∧ Zw.Laws) ∧ (C.Dist d ∧ Z.Dist d ∧ Zw.Dist d) ∧ e < d

/-- A round in which all three tables are halved. -/
def lss_roundA [Finite E] : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h d e L b bs bw κ : ℕ), CodesOK E P C Z Zw d e →
    (C.il (Fin k → Bool)).MCAat e b → (Z.il (Fin h → Bool)).MCAat e bs →
    (Zw.il (Fin h → Bool)).MCAat e bw → (stg C Z Zw (k + 1) (h + 1)).ListAt e L →
    ∀ (Φ : (stg C Z Zw (k + 1) (h + 1)).MR → Prop) (Φ' : E → (stg C Z Zw k h).MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ ((Halving.stepA C Z Zw k h).foldW γ w)) ≤ κ) →
      ∀ f, cnt (fun γ =>
          ∃ w',
            ((stg C Z Zw k h).Near e ((Halving.stepA C Z Zw k h).fold γ f)
                ((stg C Z Zw k h).enc w'.1 w'.2) ∧
              Φ' γ w') ∧
            ¬ ((stg C Z Zw (k + 1) (h + 1)).Near e f
                ((stg C Z Zw (k + 1) (h + 1)).enc ((Halving.stepA C Z Zw k h).back d γ f w').1
                  ((Halving.stepA C Z Zw k h).back d γ f w').2) ∧
              Φ ((Halving.stepA C Z Zw k h).back d γ f w'))) ≤
        (b + (bs + bw)) + L * κ

/-- A round in which the main table is halved and the masks rest. -/
def lss_roundB [Finite E] : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h d e L b κ : ℕ), CodesOK E P C Z Zw d e →
    (C.il (Fin k → Bool)).MCAat e b → (stg C Z Zw (k + 1) h).ListAt e L →
    ∀ (Φ : (stg C Z Zw (k + 1) h).MR → Prop) (Φ' : E → (stg C Z Zw k h).MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ ((Halving.stepB C Z Zw k h).foldW γ w)) ≤ κ) →
      ∀ f, cnt (fun γ =>
          ∃ w',
            ((stg C Z Zw k h).Near e ((Halving.stepB C Z Zw k h).fold γ f)
                ((stg C Z Zw k h).enc w'.1 w'.2) ∧
              Φ' γ w') ∧
            ¬ ((stg C Z Zw (k + 1) h).Near e f
                ((stg C Z Zw (k + 1) h).enc ((Halving.stepB C Z Zw k h).back d γ f w').1
                  ((Halving.stepB C Z Zw k h).back d γ f w').2) ∧
              Φ ((Halving.stepB C Z Zw k h).back d γ f w'))) ≤ b + L * κ

/-- Challenges from a finite set with an injective map to a finite set V (in its use: E). -/
def lss_cnt_val : Prop :=
  ∀ (Ch V : Type) [Finite Ch] [Finite V] (val : Ch → V),
    Function.Injective val → ∀ Q : V → Prop, cnt (fun c => Q (val c)) ≤ cnt Q

end Spec

section
variable (E : Type) [Field E] (P : Type) [Fintype P]

omit [Fintype P] in
theorem lss_stg_laws : Spec.lss_stg_laws E P := fun C Z Zw _ _ hC hZ hW =>
  ld_laws_pair E P _ _ (ld_laws_il E P C _ hC)
    (ld_laws_pair E P _ _ (ld_laws_il E P Z _ hZ) (ld_laws_il E P Zw _ hW))

theorem lss_stg_dist : Spec.lss_stg_dist E P := fun C Z Zw _ _ d hC hZ hW =>
  ld_dist_pair E P _ _ d (ld_dist_il E P C _ d hC)
    (ld_dist_pair E P _ _ d (ld_dist_il E P Z _ d hZ) (ld_dist_il E P Zw _ d hW))

omit [Field E] in
theorem lss_stepA_laws : Spec.lss_stepA_laws E P := fun C Z Zw k h d =>
  ldc_all_laws E P C Z Zw _ _ _ _ _ _ (consB k) (consB h) (consB h) d

theorem lss_stepB_laws : Spec.lss_stepB_laws E P := fun C Z Zw k _ d hZ hW dZ dW =>
  ldc_main_laws E P C _ _ _ (consB k) d
    (ld_laws_pair E P _ _ (ld_laws_il E P Z _ hZ) (ld_laws_il E P Zw _ hW))
    (ld_dist_pair E P _ _ d (ld_dist_il E P Z _ d dZ) (ld_dist_il E P Zw _ d dW))

theorem lss_roundA [Finite E] : Spec.lss_roundA E P := by
  intro C Z Zw k h d e L b bs bw κ hOK hb hbs hbw hList Φ Φ' hκ f
  obtain ⟨⟨hC, hZ, hW⟩, ⟨dC, dZ, dW⟩, he⟩ := hOK
  exact ldc_round_all E P C Z Zw _ _ _ _ _ _ (consB k) (consB h) (consB h) d e L b bs
    bw κ (lss_stg_laws E P C Z Zw k h hC hZ hW)
    (lss_stg_dist E P C Z Zw k h d dC dZ dW) he (ld_laws_il E P C _ hC)
    (ld_laws_il E P Z _ hZ) (ld_laws_il E P Zw _ hW) hb hbs hbw hList Φ Φ' hκ f

theorem lss_roundB [Finite E] : Spec.lss_roundB E P := by
  intro C Z Zw k h d e L b κ hOK hb hList Φ Φ' hκ f
  obtain ⟨⟨hC, hZ, hW⟩, ⟨dC, dZ, dW⟩, he⟩ := hOK
  exact ldc_round_main E P C _ _ _ (consB k) d e L b κ (lss_stg_laws E P C Z Zw k h hC hZ hW)
    (lss_stg_dist E P C Z Zw k h d dC dZ dW) he (ld_laws_il E P C _ hC)
    (ld_laws_pair E P _ _ (ld_laws_il E P Z _ hZ) (ld_laws_il E P Zw _ hW))
    (ld_dist_pair E P _ _ d (ld_dist_il E P Z _ d dZ) (ld_dist_il E P Zw _ d dW)) hb hList Φ Φ' hκ f

omit [Field E] [Fintype P] in
theorem lss_cnt_val : Spec.lss_cnt_val := fun _ _ _ _ val hv _ =>
  CodeListRows.cnt_le_cnt_of_injective val hv fun _ h => h

end
end Cb
