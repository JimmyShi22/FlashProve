-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/YesAtZFullN.lean: yes_of_line (YesAtZFull.lean) FOR A LINE AT THE RECORD WITH
NUMERALS: at the stored full-size files (VerifierAndGoals.storedPublicFiles): if the closed test atXL (fun X => (shapeL
(LWn X)).yes a n) accepts, then under the head, at the maker's own base, the run on shapes over the
table's own steps is true. LWn X (LettersNumerals.lean) is LW X with K2's numbers, K1's four numbers
a link and the merge's seven in numerals. A joining; nothing is evaluated here.

How. Two closed facts speak of what publicOfO returns at these files: the line, and
lettersTest_atXL (LettersNumerals.lean: by Lean's kernel: the numerals are the letters there). A
maker is a function: they speak of one record. There yes_at_LWn turns the one Bool into the other.

  **yes_of_lineN**, yes_of_lineNH (the line under atXH).

Limits. As YesAtZFull.lean's: hsz AND THE LINE ITSELF ARE PREMISES; no such line stands in the
library. At VerifierAndGoals.storedPublicFiles alone; synthetic weights. FOR VerifierAndGoals.zGap, THE OTHER NAMED SET OF PUBLIC
FILES, NO SUCH LAW STANDS. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.YesAtZFull
import Johnson.AtFull.Shape.LettersNumerals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- From an accept at the record with numerals, at what publicOfO returns at the stored files. -/
theorem yes_of_publicN (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).yes a n = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true := by
  obtain ⟨X₀, hX, ht⟩ := hk
  obtain ⟨X₁, hX₁, hl⟩ := atXL_zFull hsz lettersTest_atXL
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  exact yes_of_public h hB ⟨_, hX, (yes_at_LWn hl a n).trans ht⟩

/-- **FROM ONE CLOSED Bool AT THE NUMERALS TO THE RUN ON SHAPES AT THE HEAD's OWN LETTERS.** -/
theorem yes_of_lineN (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : atXL (fun X => (shapeL (LWn X)).yes a n) = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true :=
  yes_of_publicN hsz h hB (atXL_zFull hsz hk)

/-- The same from a line under atXH. -/
theorem yes_of_lineNH (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : atXH (fun X => (shapeL (LWn X)).yes a n) = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true :=
  yes_of_publicN hsz h hB (atXH_zFull hsz hk)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.yes_of_publicN
#print axioms Johnson.AtFull.Shape.yes_of_lineN
#print axioms Johnson.AtFull.Shape.yes_of_lineNH
