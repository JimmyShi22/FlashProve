-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/YesAtZFull.lean: AT THE STORED FULL-SIZE FILES (VerifierAndGoals.storedPublicFiles): FROM ONE CLOSED
Bool TO "THE RUN ON SHAPES RETURNS" AT THE HEAD's OWN LETTERS. If the closed test atXL (fun X =>
(shapeL (LW X)).yes a n) accepts, then under the head P5J.AtMgA at VerifierAndGoals.storedPublicFiles, at the base Bs that
the maker's own ProofFile.baseOf returns at the head's public part Zp, the run on shapes over the table's
own steps, (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n, is true. A joining of laws;
nothing is evaluated here.

How. atXL_zFull (AtX.lean): the accept speaks of the X₀ that publicOfO returns at these files. The
public record in the head's public part is what publicOfO returns (ProofFile.Law.pub_public,
Johnson/Desc/ProofFile/Law/MakerPublic.lean): a maker is a function: X₀ = Zp.p.X. The opening is the
head's (h.laid.opened), and its base is Bs (O.made). yes_at_LW (LettersAtX.lean) carries the Bool
from the table's second text at LW Zp.p.X to the table's own steps.

  **yes_of_line**: as said, general in the start a and the number n.
  yes_of_lineH: the same from a line under atXH (the head's layout by the library's withLaid).

Limits. TWO PREMISES ARE NOT PAID HERE: hsz (the stored layout file has 224975 bytes: shown in the
side library, AtFullSide/Layout/Size.lean) AND THE CLOSED Bool ITSELF: NO LINE atXL … = true STANDS
IN THE LIBRARY. Under the head: that it has a member at VerifierAndGoals.storedPublicFiles is the side library's
headMember_zFull. At VerifierAndGoals.storedPublicFiles alone: three terms written in Ladder/Stored.lean; the example's
weights are synthetic. FOR VerifierAndGoals.zGap, THE OTHER NAMED SET OF PUBLIC FILES, NO SUCH LAW STANDS.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersAtX
import Johnson.AtFull.Shape.AtX

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

/-- From a test's accept at what publicOfO returns at the stored files. -/
theorem yes_of_public (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LW X₀)).yes a n = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true := by
  obtain ⟨X₀, hX, ht⟩ := hk
  obtain rfl : X₀ = Zp.p.X := Except.ok.inj (hX.symm.trans (ProofFile.Law.pub_public h.laid.pub))
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  rw [yes_at_LW h O]
  exact ht

/-- **FROM ONE CLOSED Bool TO THE RUN ON SHAPES AT THE HEAD's OWN LETTERS.** -/
theorem yes_of_line (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : atXL (fun X => (shapeL (LW X)).yes a n) = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true :=
  yes_of_public h hB (atXL_zFull hsz hk)

/-- The same from a line under atXH. -/
theorem yes_of_lineH (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {a : ShA} {n : Nat}
    (hk : atXH (fun X => (shapeL (LW X)).yes a n) = true) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = true :=
  yes_of_public h hB (atXH_zFull hsz hk)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.yes_of_public
#print axioms Johnson.AtFull.Shape.yes_of_line
#print axioms Johnson.AtFull.Shape.yes_of_lineH
