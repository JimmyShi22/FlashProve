-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FillWrow.lean: THE ONE FIELD OF THE FIRST TABLE's MEANING THAT IS THE SHARED TABLE's SEAT's TO LAY: wrow: AS A LAYER OVER ANY MEANING. One definition, four theorems by rfl.
WHY. The first table's filling is composed in layers, one owner a field. fillJoint (Johnson/Desc/Sound/FillJoint.lean [not in this library]) lays wrow WITH three fields that another layer owns (pileOne · two public items and a row of the door): it cannot stand in the one term beside that layer. THIS LAYER LAYS wrow ALONE.
  fillWrow Pw rd Mg := { Mg with wrow := fun a _ w => WRow Pw a.2 (rd a w) }: "the row of (Eval) says its claim of the words" (WRow, Johnson/Desc/K13/Law/Letters.lean), at the words that the reader rd gives of the record and the witness. rd IS A LETTER: meant: the reader that serves every sentence on rows.
  fillWrow_wrow: the field · fillWrow_else: NINE OF the other fields, by name, are Mg's (so are all the rest, by the make "{ Mg with wrow := … }": not written out) · fillWrow_says: at rd a w := wordsOn (stOf₁ a) (tabP₁ a w) the field is JointSays' third equation's right side (Johnson/Desc/Sound/PointAtLayers.lean), to the letter: by rfl: stated here without that file's import.
It imports the first table and that one law file: no file of the shared table's.

Limits. A composing. Nothing says that any witness meets the item.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.Means.ItemsTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement)
open OnBytes.Slice (GE)
open OnBytes.Means (Words wordsOn)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (WRow)

variable {P W : Type}

/-- **The layer that lays wrow alone.** -/
def fillWrow (Pw : Where) (rd : P × First.S → W → Words GE) (Mg : Meaning P W) : Meaning P W :=
  { Mg with wrow := fun a _ w => WRow Pw a.2 (rd a w) }

theorem fillWrow_wrow (Pw : Where) (rd : P × First.S → W → Words GE) (Mg : Meaning P W) :
    (fillWrow Pw rd Mg).wrow = fun a _ w => WRow Pw a.2 (rd a w) := rfl

/-- What it does not lay is the meaning's beneath. -/
theorem fillWrow_else (Pw : Where) (rd : P × First.S → W → Words GE) (Mg : Meaning P W) :
    (fillWrow Pw rd Mg).pub = Mg.pub ∧ (fillWrow Pw rd Mg).pubP = Mg.pubP ∧
      (fillWrow Pw rd Mg).more = Mg.more ∧ (fillWrow Pw rd Mg).inOrder = Mg.inOrder ∧
      (fillWrow Pw rd Mg).pin = Mg.pin ∧ (fillWrow Pw rd Mg).pinW = Mg.pinW ∧
      (fillWrow Pw rd Mg).decodes = Mg.decodes ∧ (fillWrow Pw rd Mg).pile = Mg.pile ∧
      (fillWrow Pw rd Mg).pileOne = Mg.pileOne := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At words made off tables: the form in which the law at "LIN point" asks the field. -/
theorem fillWrow_says (Pw : Where) (stOf₁ : P × First.S → Statement)
    (tabP₁ : P × First.S → W → Nat → Bool → Nat → Nat → GE) (Mg : Meaning P W) :
    (fillWrow Pw (fun a w => wordsOn (stOf₁ a) (tabP₁ a w)) Mg).wrow =
      fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)) := rfl

/-- Laid twice it is laid once. -/
theorem fillWrow_twice (Pw : Where) (rd : P × First.S → W → Words GE) (Mg : Meaning P W) :
    fillWrow Pw rd (fillWrow Pw rd Mg) = fillWrow Pw rd Mg := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.fillWrow_wrow
#print axioms VerifiableInference.Desc.Sound.fillWrow_else
#print axioms VerifiableInference.Desc.Sound.fillWrow_says
#print axioms VerifiableInference.Desc.Sound.fillWrow_twice
