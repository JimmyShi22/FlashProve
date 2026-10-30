-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StatedCell.lean: THE ONE FORM IN WHICH EACH KIND's FILES HAND THEIR HALF OF THE EXCHANGE ACROSS A SEGMENT's SECOND SENDING, AND THE EXCHANGE's PREMISE hcell FROM IT. One definition, two theorems.
WORDS. "The verifier's state": the value of type First.S that the verifier carries between two blocks.
WHY. The exchange formsTQ_of_formsQ (Johnson/Desc/Sound/FormsT.lean) hands "formsT" at the state s in front of the second sending from "forms" at the state s' behind it, under hcell: AT THE CELLS THAT THE FORMS NAME, THE DATA READ BEHIND ARE THE STATED DATA IN FRONT. With St := Stated.of (uBySort …) (Johnson/Desc/Sound/StatedAll.lean) the stated data at an array of the second sending are the arm of the open segment's sort: each arm a kind's own term. So hcell is taken by cases, and each kind's files owe their case. One form is written down here, so that three kinds' files do not type three shapes.
  ArmCell Rd own own' u piece run s a b rd: THE FORM: for every form of the run, every entry x that it names, every name c of x's array WITH second s c = true: the committed cell, read behind the sending, is u at the state in front and the first sending's data: (dataQ own' b rd).cell c.1 c.2 x.row x.idx = u s (dataQ own a rd) c x.row x.idx. MEANT: from the block's yes, the smallness test's tie at the state behind, and the kind's law on its tables.
  OtherCells …: the like at an array that is NOT of the second sending: the cell read behind is the cell read in front (cell_rides, Johnson/Desc/Sound/FormsQ.lean, is of that kind).
  hcell_of_arm: StatedIs St u s, ArmCell and OtherCells give hcell, TO THE LETTER of formsTQ_of_formsQ's premise.
  formsTQ_of_arm: so the exchange itself, with hcell gone.

Limits. A rule. Nobody's ArmCell is shown here. WHAT MUST BE ONE ACROSS THE SORTS IS NOT THE FORMULA BUT THE READING OF THE ARRAYS: the tie speaks at its own letter for the table of cells; ArmCell's left side is dataQ by seat: that join is owed once, by nobody named here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StatedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.K9 (segAt? Read Readers formsInT)

section
variable (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S) (a b : K9.Part)
  (rd : ℕ × ℕ → MsgQ)

/-- **THE FORM OF A KIND's HALF**: at an array of the second sending that a form names, the committed cell is the stated function. -/
def ArmCell (u : UFn) : Prop :=
  ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
    ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c → second s c = true →
      (dataQ own' b rd).cell c.1 c.2 x.row x.idx = u s (dataQ own a rd) c x.row x.idx

/-- At every other array that a form names the cell stays. -/
def OtherCells : Prop :=
  ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
    ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c → second s c = false →
      (dataQ own' b rd).cell c.1 c.2 x.row x.idx = (dataQ own a rd).cell c.1 c.2 x.row x.idx

/-- **hcell, to the letter.** -/
theorem hcell_of_arm (St : Stated) (u : UFn) (hSt : StatedIs St u s)
    (h2 : ArmCell Rd own own' piece run s a b rd u) (h1 : OtherCells Rd own own' piece run s a b rd) :
    ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (dataQ own' b rd).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx := by
  intro R hR f hf x hx c hc
  cases hs : second s c with
  | true => rw [hSt.cell _ c _ _ hs]; exact h2 R hR f hf x hx c hc hs
  | false => rw [hSt.other _ c _ _ hs]; exact h1 R hR f hf x hx c hc hs

end

/-- **The exchange, with hcell and hmask's right side unfolded by StatedIs.** -/
theorem formsTQ_of_arm (Rd : Readers) (St : Stated) (u : UFn) (own own' : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (hSt : StatedIs St u s)
    (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInT Rd own piece run s = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (h2 : ArmCell Rd own own' piece run s a b rd u) (h1 : OtherCells Rd own own' piece run s a b rd)
    (hmask : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQ own' b rd).mask x.1 = (dataQ own a rd).mask x.1)
    (h : formsQ Rd own' piece run s' rd) : formsTQ Rd St own piece run s rd :=
  formsTQ_of_formsQ Rd St own own' piece run s s' a b rd ha hb hl hin harr hfill
    (hcell_of_arm Rd own own' piece run s a b rd St u hSt h2 h1)
    (fun R hR f hf x hx => by rw [hSt.mask]; exact hmask R hR f hf x hx) h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.hcell_of_arm
#print axioms VerifiableInference.Desc.Sound.formsTQ_of_arm
