-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ON PUBLIC DATA, IN THE GOALS' SCOPE.
Johnson/Desc/ProofFile/Honest/K3/Term/OwnersOfTheMatricesAtEveryLink.lean: AT EVERY LINK OF THE
PROOF, IN THE GOALS' SCOPE: THE TWO NUMBERS IN THE LABEL OF A MATRIX ARE THOSE OF `Sz.ref`'S OWNER
OF THE MATRIX. CONDITIONAL: on the three premises on the public files, and on the matrix's being
the one that `Sz.ref` has at that link and number.

What it is for. A plan's label gives a matrix's owner as two numbers (`Meaning.ownerK`,
`Meaning.ownerA`), while the sizes name the owner by `Sz.owner`. The library has the step from one
to the other at an attention segment (`owner_numbers_att`,
Johnson/Desc/ProofFile/Honest/K5/Law/PackedAtSeg.lean). This file has it at all 25 links, for the
joining file PackedTraceCellsFromLaysFilling.lean in this folder.

Main names:
  `ownerNumbersAtEveryLink`: **the law**, at every segment of the proof.
  `ownerNumbersAtFeedForward`: the same at a feed-forward segment.
  `ownerNumbersAtHead`: the same at the head.

How. `matAt_eq_some_iff` (Johnson/HonestTrace/Packed.lean) turns the premise on the matrix into the
segment's number and the matrix's number in the list. `Meaning.owner_label`
(Johnson/Goal/Meaning/HidSeatsOf.lean) gives the label's two numbers as `Meaning.ownerOf`. They are
compared with `Sz.owner` (Johnson/HonestTrace/Places.lean) name by name.

Limits. At `Sz.ref`, the full-size example's numbers. That the three premises on the public files
hold is not shown here. It says nothing of what the arrays hold.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedAtSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (Sz Seg MatName matAt_eq_some_iff nameNo_eq_some_iff no?_lt parts_in_scope)

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **At a feed-forward segment, the label's two numbers are those of `Sz.ref`'s owner.**
Conditional: the three premises on the public files; the group is below 12; `number` is the number
of `name` in the segment's list. -/
theorem ownerNumbersAtFeedForward (inScope : VerifierAndGoals.InScope Z = true)
    (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPartMade : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {group : ℕ}
    (groupBelow : group < 12) {number : ℕ} {name : MatName}
    (numberOfName : Sz.ref.nameNo (.ff group) number = some name) :
    Meaning.ownerK (Meaning.labAt X (2 * group) number) =
        (Sz.ref.owner (.ff group) name).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner (.ff group) name).1 (Sz.ref.owner (.ff group) name).2 =
        some (Meaning.ownerA (Meaning.labAt X (2 * group) number)) := by
  have core := OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade
  have listNumber := (nameNo_eq_some_iff Sz.ref _ _ _).1 numberOfName
  have numberBelow : number < 9 := no?_lt Sz.ref listNumber
  have label := Meaning.owner_label publicPartMade core (k := 2 * group) (a := number)
    (by omega) (by rw [Meaning.size_even publicPartMade core groupBelow]; exact numberBelow)
  obtain ⟨-, numberOfXbO, numberOfXbI⟩ := Meaning.ix_of_core publicPartMade core
  unfold Meaning.ownerOf at label
  rw [if_neg (by omega), if_neg (by omega), numberOfXbI, numberOfXbO] at label
  by_cases borrowed : number = 8 ∧ 0 < 2 * group
  · rw [if_pos borrowed] at label
    obtain ⟨ownerLink, ownerNumber⟩ := Prod.mk.inj label
    have nameIs : name = .xbI := MatName.no?_inj listNumber (by rw [borrowed.1]; rfl)
    subst nameIs
    have ownerIs : Sz.ref.owner (.ff group) .xbI = (.ff (group - 1), .xbO) := by
      show (if group = 0 then ((.ff group : Seg), (.xbI : MatName))
        else (.ff (group - 1), .xbO)) = _
      rw [if_neg (by omega)]
    rw [ownerIs, ownerLink, ownerNumber]
    refine ⟨?_, ?_⟩
    · show 2 * group - 2 = 2 * (group - 1)
      omega
    · show Sz.ref.mu (.ff (group - 1)) .xbO = some 7
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff (group - 1)) from
        (show group - 1 < 12 by omega))]
      rfl
  · rw [if_neg borrowed] at label
    obtain ⟨ownerLink, ownerNumber⟩ := Prod.mk.inj label
    have ownerIs : Sz.ref.owner (.ff group) name = (.ff group, name) := by
      cases name with
      | xbI =>
        have numberIsEight : 8 = number := Option.some.inj listNumber
        have groupIsZero : group = 0 := by
          by_contra different
          exact borrowed ⟨numberIsEight.symm, by omega⟩
        subst groupIsZero
        rfl
      | _ => rfl
    rw [ownerIs, ownerLink, ownerNumber]
    refine ⟨rfl, ?_⟩
    show Sz.ref.mu (.ff group) name = some number
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.ff group) from groupBelow)]
    exact listNumber

/-- **At the head, the label's two numbers are those of `Sz.ref`'s owner.** Conditional: the three
premises on the public files; `number` is the number of `name` in the head's list. -/
theorem ownerNumbersAtHead (inScope : VerifierAndGoals.InScope Z = true)
    (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPartMade : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {number : ℕ}
    {name : MatName} (numberOfName : Sz.ref.nameNo .head number = some name) :
    Meaning.ownerK (Meaning.labAt X 24 number) = (Sz.ref.owner .head name).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner .head name).1 (Sz.ref.owner .head name).2 =
        some (Meaning.ownerA (Meaning.labAt X 24 number)) := by
  have core := OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade
  have listNumber := (nameNo_eq_some_iff Sz.ref _ _ _).1 numberOfName
  have numberBelow : number < 8 := no?_lt Sz.ref listNumber
  have label := Meaning.owner_label publicPartMade core (k := 24) (a := number)
    (by omega) (by rw [Meaning.size_head publicPartMade core]; exact numberBelow)
  have headParts := (parts_in_scope inScope filesRead publicPartMade).2.2.2
  obtain ⟨-, numberOfXbO, -⟩ := Meaning.ix_of_core publicPartMade core
  unfold Meaning.ownerOf at label
  rw [if_pos rfl, headParts, numberOfXbO] at label
  by_cases borrowed : number = 4 + 3
  · rw [if_pos borrowed] at label
    obtain ⟨ownerLink, ownerNumber⟩ := Prod.mk.inj label
    have nameIs : name = .xbL := MatName.no?_inj listNumber (by rw [borrowed]; rfl)
    subst nameIs
    have ownerIs : Sz.ref.owner .head .xbL = (.ff 11, .xbO) := rfl
    rw [ownerIs, ownerLink, ownerNumber]
    refine ⟨rfl, ?_⟩
    show Sz.ref.mu (.ff 11) .xbO = some 7
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.ff 11) from (show 11 < 12 by omega))]
    rfl
  · rw [if_neg borrowed] at label
    obtain ⟨ownerLink, ownerNumber⟩ := Prod.mk.inj label
    have ownerIs : Sz.ref.owner .head name = (.head, name) := by
      cases name with
      | xbL => exact absurd (Option.some.inj listNumber).symm borrowed
      | _ => rfl
    rw [ownerIs, ownerLink, ownerNumber]
    refine ⟨rfl, ?_⟩
    show Sz.ref.mu .head name = some number
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr .head from trivial)]
    exact listNumber

end

/-- **At every link, the label's two numbers are those of `Sz.ref`'s owner.** Conditional: the
three premises on the public files; `isTheMatrix`: `Sz.ref` has the matrix `name` of `segment` at
this link and number. -/
theorem ownerNumbersAtEveryLink {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope Z = true) (filesRead : VerifierAndGoals.readFiles Z = .ok pp)
    (publicPartMade : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X)
    {link number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) :
    Meaning.ownerK (Meaning.labAt X link number) = (Sz.ref.owner segment name).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner segment name).1 (Sz.ref.owner segment name).2 =
        some (Meaning.ownerA (Meaning.labAt X link number)) := by
  obtain ⟨segmentBelow, linkIs, numberIs⟩ := (matAt_eq_some_iff Sz.ref _ _ _ _).1 isTheMatrix
  unfold Sz.mu at numberIs
  rw [if_pos segmentBelow] at numberIs
  have numberOfName := (nameNo_eq_some_iff Sz.ref _ _ _).2 numberIs
  cases segment with
  | ff group =>
    have linkIsNumber : link = 2 * group := linkIs.symm
    subst linkIsNumber
    exact ownerNumbersAtFeedForward inScope filesRead publicPartMade segmentBelow numberOfName
  | att group =>
    have linkIsNumber : link = 2 * group + 1 := linkIs.symm
    subst linkIsNumber
    exact ProofFile.Honest.K5.owner_numbers_att inScope filesRead publicPartMade segmentBelow numberOfName
  | head =>
    have linkIsNumber : link = 24 := linkIs.symm
    subst linkIsNumber
    exact ownerNumbersAtHead inScope filesRead publicPartMade numberOfName

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.ownerNumbersAtFeedForward
#print axioms ProofFile.Honest.K3.Term.ownerNumbersAtHead
#print axioms ProofFile.Honest.K3.Term.ownerNumbersAtEveryLink
