-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GlueAtLedgerStep/SharedAtTablesR.lean: TWO FIELDS OF THE PROOF FILE's ROWS IN THEIR SECOND
FORM (Johnson/P5J/SevenOfTiedR.lean: RowsTiedR; Johnson/P5J/TopTablesR.lean: TablesFitR), AT THE ONE
CHOICE Q₂ := THE LEDGER's OWN STEP (stepAt): the field stepQ of tables_fit, and the field
shared_joint_count from the ledger's end. Statements and proofs.

  stepQ_tablesR     TablesFitR's field stepQ, to its letter, at Q₂ := stepAt (tiedNumbers N₁ Ns)
                    (tiedMeaning get Mg₁ Mg) Pm (ocR …) split T.p₂ T.l₂ ext, at every extractor ext:
                    stepQ_at (Johnson/Desc/Sound/StepQAt.lean) called
  tablesFitR_step   whoever has tables_fit at any step Q₂ has it at the ledger's own step: Q₂ stands
                    in the field stepQ alone: so Lean holds that stepQ_tablesR is that field's
                    sentence
  places_true       flatPlaces true links true is flatPlacesOf links true
  sjc_tablesR       the field shared_joint_count's sentence: a row of laws (EachLawsBN) at
                    plTablesR's on₂ and Q₂, whatever is laid over its first chain's two fields: FROM
                    the same row at onQ₂ … Oc … and stepAt … MgL … Oc …, where Oc is ocR … and MgL
                    is tiedMeaning get Mg₁ Mg (two equations)

Can the premises be met? The two equations are to be shown at the letters that are picked: where the
ledger's condition is "ocEnd and a rider on what the first chain hands on" the first should be an
unfolding; the second asks that the ledger's meaning be a tied meaning. NEITHER IS SHOWN HERE. The
row L is the ledger's end: a premise.
Limits. Rules over letters: no law is shown. It closes no row. Nothing on soundness.

-/
import Johnson.P5J.TopTablesR
import Johnson.Desc.Sound.StepQAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ

/-- The list of places with the front is the driver's own. -/
theorem places_true (links : List ModelPart) :
    VerifiableInference.Desc.First.flatPlaces true links true =
      VerifiableInference.Desc.First.flatPlacesOf links true := rfl

section Fit
variable {C : CK} {D : WholeD} {all : List LeftT} {Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type}
  (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
  (get : P × S₁' → P₀ × VerifiableInference.Desc.First.S) (N₁ : Numbers)
  (Mg₁ : VerifiableInference.Desc.First.Meaning P₀ W) (links : List ModelPart) (ps : List Place)
  (Ns : NumbersS) (Mg : MeaningS S₂' (P × S₁') W) (ML : MeaningL S₃' W) (Pm : PromMeaning S₂')
  (PLm : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool) (Rc : P × S₁' → Prop)
  (ext : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → W → W)

/-- **tables_fit's field stepQ, at the ledger's own step.** -/
theorem stepQ_tablesR : ∀ k a b,
    stepAt (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂
      T.l₂ ext k a b →
    onQ₂ (tiedNumbers N₁ Ns) Pm (ocR get N₁ Mg₁ links ps Rc) split T.p₂ T.l₂ (k + 1) b ∧
      ((∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ (k + 1) b w) →
        ∃ w, relQ₂ (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) split T.p₂ T.l₂ k a w) :=
  stepQ_at _ _ _ _ _ _ _ _

/-- **Whoever has tables_fit at any step has it at the ledger's own step**: the step stands in the
field stepQ alone. (So Lean holds that stepQ_tablesR is that field's sentence, to the letter.) -/
theorem tablesFitR_step (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
    (R₀ : (P × S₁') × (EAll D all).Str → W → Prop)
    (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop)
    (f : TablesFitR start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc) :
    TablesFitR start₂ start₃ T Q get N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split
      (stepAt (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm (ocR get N₁ Mg₁ links ps Rc) split
        T.p₂ T.l₂ ext) Rc :=
  ⟨f.len₁, f.len₂, f.len₃, f.END, f.TP, f.SH, f.PW, f.START, f.SH₃, f.POf, f.POb,
    stepQ_tablesR T get N₁ Mg₁ links ps Ns Mg Pm split Rc ext⟩

/-- **The field shared_joint_count's sentence, from the ledger's end.** -/
theorem sjc_tablesR {κ : Type} (key : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → κ) (n : ℕ)
    (Oc : P × S₁' → Strs → Prop) (MgL : MeaningS S₂' (P × S₁') W)
    (hOc : Oc = ocR get N₁ Mg₁ links ps Rc) (hMg : MgL = tiedMeaning get Mg₁ Mg)
    (L : EachLawsBN key (onQ₂ (tiedNumbers N₁ Ns) Pm Oc split T.p₂ T.l₂)
      (stepAt (tiedNumbers N₁ Ns) MgL Pm Oc split T.p₂ T.l₂ ext) n 0 (T.p₂ :: T.l₂))
    (o₁ : ℕ → (P × S₁') × (EAll D all).Str → Prop)
    (q₁ : ℕ → (P × S₁') × (EAll D all).Str → (P × S₁') × (EAll D all).Str → Prop) :
    EachLawsBN key
      ({ plTablesR T get N₁ Mg₁ links ps Ns Mg ML Pm PLm split
          (stepAt (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm (ocR get N₁ Mg₁ links ps Rc) split
            T.p₂ T.l₂ ext) Rc with on₁ := o₁, Q₁ := q₁ } :
        PPlaces D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃')).on₂
      ({ plTablesR T get N₁ Mg₁ links ps Ns Mg ML Pm PLm split
          (stepAt (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ Mg) Pm (ocR get N₁ Mg₁ links ps Rc) split
            T.p₂ T.l₂ ext) Rc with on₁ := o₁, Q₁ := q₁ } :
        PPlaces D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃')).Q₂
      n 0 (T.p₂ :: T.l₂) := by
  subst hOc hMg
  exact L

end Fit

end P5J

#print axioms P5J.places_true
#print axioms P5J.stepQ_tablesR
#print axioms P5J.tablesFitR_step
#print axioms P5J.sjc_tablesR
