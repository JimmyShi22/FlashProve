-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkStdErr.lean: for small example instances: the errors of the test that two
encodings hold the same index, built from standard parts, round by round, beside the number of
values of each verifier message.

Statements and proofs. Generic: any configuration, an abstract field, a variable code (`StdLk`,
Cb/Obj/LdObjectLinkStd.lean).

Main names:
  `Spec.stdLk_lists`: if the code and P have a position (`Nonempty`), the list of errors in the
    numbers of the object's link with standard parts (`D.K.nums ..`), read as a plain list
    (Ior/KnowCollRulesChainErr.lean), is, in this order: γ: `errGam ε₀ ε₁`; the joint seed: the
    sending's error; the answers: 0; the locations: `errLoc`; φ: `errPhi`; the bridge: Lc · (the
    evader's number); the base case: bad + L2; (|P| - e - 1)^tb. And the numbers of values of the
    eight verifier messages are those of: γ; joint seeds; one value; pairs of lists of locations; φ;
    the bridge's seeds; the field; lists of tb positions.
  `stdLk_sendErr`, `stdLk_seeds`: two members with independent seeds: the sending's error is 2 ·
    |seeds of one| · ((L choose 2) · the sample's number), of |seeds of one|² joint seeds.
  `Spec.stdLk_small`: every error of that list is below the number of values of its verifier message
    (`Iop.Err.Small`), if the code and P have a position (`Nonempty`), from seven inequalities
    between numbers.

Limits: this file does not say that the seven inequalities can be met. For that see
Cb/Obj/LdObjectLinkToy.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkStd
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

def Spec.stdLk_lists (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLk Cf P)
      (ε₀ ε₁ L t : ℕ) (d₂ : D.K.P.W2) (d₀ : D.K.P.W0),
    (D.K.nums (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀)).err.toList =
      [D.K.P.errGam ε₀ ε₁, ldSendFamErr D.N (Sig.Seeds.indep D.N) (fun _ => L), 0, D.K.P.errLoc,
        D.K.P.errPhi, D.Lc * D.Kc.Z.err, D.bad + D.L2, (Fintype.card P - D.M.e - 1) ^ D.tb] ∧
    (D.K.link (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀)).shape.chalList =
      [Fintype.card D.K.P.Gam, Fintype.card (Sig.Seeds.indep D.N).D, Fintype.card Unit,
        Fintype.card ((Fin D.t₀ → Fin Cf.C₀.n) × (Fin D.t₁ → Fin Cf.C₀.n)),
        Fintype.card (Fin D.l → E), @Fintype.card D.Kc.Z.D D.Kc.Z.fin, Fintype.card E,
        Fintype.card (Fin D.tb → P)]

theorem stdLk_lists (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.stdLk_lists F E := by
  intro Cf _ P _ _ D ε₀ ε₁ L t d₂ d₀
  have hc : (D.Kc.tc d₂).c = (Chain.one (D.Kc.run.link _ _ _)).append (Chain.one _) := rfl
  constructor
  · show (D.K.P.linkC D.K.free D.K.free (D.S L t) ε₀ ε₁ (D.Kc.cZ d₂) d₀).errs = _
    unfold LdLkP.linkC LdLkP.Cl.cZ LdLkP.coreC
    rw [(chainErr_link _ _ _ _ _).1, (chainErr_append _ _ _ _ _ _).1,
      (chainErr_append _ _ _ _ _ _).1, hc]
    simp only [Chain.append, Chain.errs]
    erw [Chain.errs_snoc, Chain.errs_one]
    rfl
  · show (D.K.P.linkC D.K.free D.K.free (D.S L t) ε₀ ε₁ (D.Kc.cZ d₂) d₀).chs = _
    unfold LdLkP.linkC LdLkP.Cl.cZ LdLkP.coreC
    rw [(chainErr_link _ _ _ _ _).2, (chainErr_append _ _ _ _ _ _).2,
      (chainErr_append _ _ _ _ _ _).2, hc]
    simp only [Chain.append, Chain.chs]
    erw [Chain.chs_snoc, Chain.chs_one]
    rfl

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] (D : StdLk Cf P)

/-- the sending's error, for two members with independent seeds -/
theorem stdLk_sendErr (L : ℕ) :
    ldSendFamErr D.N (Sig.Seeds.indep D.N) (fun _ => L) =
      2 * (Fintype.card D.M.Z.D * (L.choose 2 * D.M.Z.err)) := by
  show ∑ a : Bool, (∏ _b ∈ Finset.univ.erase a, Fintype.card D.M.Z.D) * (L.choose 2 * D.M.Z.err) = _
  have h : ∀ a : Bool, (Finset.univ.erase a).card = 1 := by decide
  simp only [Finset.prod_const, h, pow_one, Fintype.sum_bool]
  ring

theorem stdLk_seeds :
    Fintype.card (Sig.Seeds.indep D.N).D = Fintype.card D.M.Z.D * Fintype.card D.M.Z.D := by
  show Fintype.card (Bool → D.M.Z.D) = _
  rw [Fintype.card_fun, Fintype.card_bool, pow_two]

end

def Spec.stdLk_small (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLk Cf P)
      (ε₀ ε₁ L t : ℕ) (d₂ : D.K.P.W2) (d₀ : D.K.P.W0),
    D.K.P.errGam ε₀ ε₁ < Fintype.card D.K.P.Gam →
    2 * (L.choose 2 * D.M.Z.err) < Fintype.card D.M.Z.D →
    D.K.P.errLoc < Fintype.card ((Fin D.t₀ → Fin Cf.C₀.n) × (Fin D.t₁ → Fin Cf.C₀.n)) →
    D.K.P.errPhi < Fintype.card (Fin D.l → E) → D.Lc < Fintype.card E →
    D.bad + D.L2 < Fintype.card E →
    (Fintype.card P - D.M.e - 1) ^ D.tb < Fintype.card (Fin D.tb → P) →
    (D.K.nums (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀)).err.Small

theorem stdLk_small (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.stdLk_small F E := by
  intro Cf _ P _ _ D ε₀ ε₁ L t d₂ d₀ h1 h2 h4 h5 h6 h7 h8
  obtain ⟨e1, e2⟩ := stdLk_lists F E Cf P D ε₀ ε₁ L t d₂ d₀
  refine (chainErr_small _ _).2 ?_
  rw [e1]
  erw [e2]
  refine .cons h1
    (.cons ?_ (.cons Fintype.card_pos (.cons h4 (.cons h5 (.cons ?_ (.cons h7 (.cons h8 .nil)))))))
  · rw [stdLk_sendErr, stdLk_seeds]
    have hp : 0 < Fintype.card D.M.Z.D := Fintype.card_pos
    calc
      2 * (Fintype.card D.M.Z.D * (L.choose 2 * D.M.Z.err)) =
          Fintype.card D.M.Z.D * (2 * (L.choose 2 * D.M.Z.err)) := by ring
      _ < Fintype.card D.M.Z.D * Fintype.card D.M.Z.D := (Nat.mul_lt_mul_left hp).2 h2
  · letI : DecidableEq (D.G.Row D.K.P.RowB) := Classical.decEq _
    show D.Lc * Fintype.card E ^ (Fintype.card (D.G.Row D.K.P.RowB) - 1) <
      Fintype.card (D.G.Row D.K.P.RowB → E)
    have hr : 1 ≤ Fintype.card (D.G.Row D.K.P.RowB) :=
      Fintype.card_pos_iff.2 ⟨Sum.inl (Sum.inr (Sum.inr ()))⟩
    have hq : 0 < Fintype.card E := Fintype.card_pos
    rw [Fintype.card_fun]
    calc
      D.Lc * Fintype.card E ^ (Fintype.card (D.G.Row D.K.P.RowB) - 1) <
          Fintype.card E * Fintype.card E ^ (Fintype.card (D.G.Row D.K.P.RowB) - 1) :=
        (Nat.mul_lt_mul_right (pow_pos hq _)).2 h6
      _ = Fintype.card E ^ (Fintype.card (D.G.Row D.K.P.RowB) - 1 + 1) := (pow_succ' _ _).symm
      _ = Fintype.card E ^ Fintype.card (D.G.Row D.K.P.RowB) := by rw [Nat.sub_add_cancel hr]

end Cb
