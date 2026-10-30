-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MemberOf
import Johnson.Desc.K12.Law.LitO
import Johnson.Desc.K12.Law.BatOneOk
import Johnson.Desc.K12.Law.SpendOk
import Johnson.Desc.K12.JoinGuarded
/-
Johnson/Desc/K12/Law/MemberO.lean: A MEMBER OF PayK, NOT OF THE PROMISE (the promise is FirstOpensOwn ∧ PayK), AND NOT «the law has a member»: at ONE real place: the proximity test O (the opened rows' test on the shared chain; the place whose first fold sends its own mask) of the SMALL stored proof of a build not in this repository. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
FixesP | PayKP (MemberOf.lean) are Fixes | PayK lifted by program. THAT EACH TWIN IS ITS ORIGINAL IS PROVED, BY rfl (Johnson/Desc/K12/Coin/MemberOTrue.lean: fixes_eq · payK_eq · member_O_true): so it is a member of PayK itself.
WHAT IS PROVED: member_O: no premise, no free letter: (a) what the record fixes is there (b) PayKP piO (fun s => rO s.st) (batV0 piO rO) tO (c) AT THE SAME PLACE AND RADII: the block's test on the plan · early · one answer · ownMask · johOk · batOneOk · spendOk · pubOk at the record's codes · batV0 piO rO = 768 (= 384 · 2: the Johnson bound on the list at the planner's radius, times the rows less one).
BY WHAT: Lean's KERNEL alone: «decide +kernel» on tests with code at the literals of LitO.lean; member_of_B. Nothing is trusted to the compiler: the print at the file's end would show it.
piO | rO: Johnson/Desc/K12/Law/PlacesSmall.lean. rO: the planner's own radii at O's three stages: 189103 · 10390 · 21065, KEYED BY THE MAIN CODE's a (18 · 14 · 15; 0 elsewhere): right at O, whose three stages part in a; not to be carried to a place with two stages of one length; (from a print of a program of ours, not in this repository; a later print's own lines say the same [reported, not shown]).
(a) (b) DO NOT READ A FIELD ELEMENT: combineAt, layout and gpOf read places, sizes and shapes. A record with every coefficient struck would pass as well. So the literal is the WHOLE record, and its tie to the stored files is a run's word (LitO.lean's head), not a theorem: THAT tO IS THE RECORD WHICH THE VERIFIER REACHES ON THE STORED FILE IS NOT PROVED. tO IS THE PRINT's RECORD: made by the printing program's own running of the reader and of the blocks in front, not by a description's decision.
THE PLACE's PIECE NUMBER IS THE PRINT's OWN (1); other files seat this test at ⟨2, none, 10, .K12⟩ [reported, not shown]: member_O10 is the same theorem there (the same three evaluations go through at both numbers; that no test here reads the piece number is not shown).
SILLY MEMBERS: o_below: PayKP fails at 767 · o_moved: with the group's number moved beyond the groups nothing is fixed · o_far: johOk says no with the first stage's radius at the code's length · o_alien: memberB says no where the group under test has lost its last member (which clause refuses is not said) · o_comb | o_term: combineAt says yes at the rows that the test takes in, and no where the first of them has its first term on an oracle message that is not there.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Member
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (johOk batV0 spendOk pubOk)
open H2K.First (batOneOk)

/-- The public tests, together. -/
def publicB (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) : Bool :=
  (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk && π.early && π.answers == 1 && johOk π r &&
    batOneOk π && spendOk π && pubOk π K

theorem o_memberB : memberB piO rO tO = true := by decide +kernel
theorem o_publicB : publicB piO rO tO.st.codes = true := by decide +kernel
theorem o_v0 : batV0 piO rO = 768 := by decide +kernel

/-- **A member of PayK at a real place.** -/
theorem member_O :
    (∃ a rest G0 Ly D, FixesP piO tO a rest G0 Ly D) ∧
    PayKP piO (fun s => rO s.st) (batV0 piO rO) tO ∧
    (proximityTestKind guardedProximityTestParts piO : Block T12 Unit).planOk = true ∧ piO.early = true ∧ piO.answers = 1 ∧
    piO.nums.ownMask = true ∧ johOk piO rO = true ∧ batOneOk piO = true ∧ spendOk piO = true ∧
    pubOk piO tO.st.codes = true ∧ batV0 piO rO = 768 := by
  obtain ⟨m1, m2⟩ := member_of_B piO rO tO o_memberB
  have h := o_publicB
  simp only [publicB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨m1, m2, h1, h2, h3, rfl, h4, h5, h6, h7, o_v0⟩

/-- The same place under the piece number at which other files seat it. -/
def piO10 : P12 := { piO with place := ⟨2, none, 10, .K12⟩ }

theorem o10_memberB : memberB piO10 rO tO = true := by decide +kernel
theorem o10_publicB : publicB piO10 rO tO.st.codes = true := by decide +kernel
theorem o10_v0 : batV0 piO10 rO = 768 := by decide +kernel

theorem member_O10 :
    (∃ a rest G0 Ly D, FixesP piO10 tO a rest G0 Ly D) ∧
    PayKP piO10 (fun s => rO s.st) (batV0 piO10 rO) tO ∧
    (proximityTestKind guardedProximityTestParts piO10 : Block T12 Unit).planOk = true ∧ piO10.early = true ∧
    piO10.answers = 1 ∧ piO10.nums.ownMask = true ∧ johOk piO10 rO = true ∧
    batOneOk piO10 = true ∧ spendOk piO10 = true ∧ pubOk piO10 tO.st.codes = true ∧
    batV0 piO10 rO = 768 := by
  obtain ⟨m1, m2⟩ := member_of_B piO10 rO tO o10_memberB
  have h := o10_publicB
  simp only [publicB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨m1, m2, h1, h2, h3, rfl, h4, h5, h6, h7, o10_v0⟩

/-! ## The shorter forms -/

theorem payY_O : PayYP piO (fun s => rO s.st) 768 tO := by
  have h := payY_of member_O.2.1
  rwa [o_v0] at h

theorem payRec_O : PayRecP piO tO := payRec_of member_O.2.1
theorem payNum_O : PayNumP piO tO := payNum_of member_O.2.1

/-! ## Silly members -/

/-- The number is sharp. -/
theorem o_below : ¬ PayKP piO (fun s => rO s.st) 767 tO :=
  not_pay_below piO rO tO o_memberB 767 (by rw [o_v0]; decide)

/-- (a) can fail. -/
theorem o_moved : ¬ ∃ a rest G0 Ly D, FixesP piO { tO with g := 99 } a rest G0 Ly D :=
  no_fixes piO _ (by decide +kernel)

/-- johOk can fail: the first stage's radius at the code's length. -/
theorem o_far : johOk piO (fun s => if s.C.a = 18 then 2 ^ 18 else rO s) = false := by
  decide +kernel

/-- The record with the last member struck from the group under test. -/
def tOalien : T12 :=
  { tO with st := { tO.st with groups := tO.st.groups.modify tO.g fun G =>
      { G with members := G.members.pop, kept := G.kept.pop } } }

/-- The test on the record can fail. -/
theorem o_alien : memberB piO rO tOalien = false := by decide +kernel

/-- The group under test and its layout, as the record gives them. -/
def gO : Group := (tO.st.groups[tO.g]?).getD default
def lyO : GroupLayout := (tO.st.layout tO.g).getD default

/-- combineAt says yes at the rows that the test takes in … -/
theorem o_comb : combineAt (begun tO.st tO.g gO) tO.g ⟨lyO, runRows tO.st gO⟩ = true := by
  decide +kernel

/-- … and no where the first of them has its first term on an oracle message that is not there. -/
theorem o_term : combineAt (begun tO.st tO.g gO) tO.g ⟨lyO, (runRows tO.st gO).modify 0 fun R =>
    { R with terms := R.terms.modify 0 fun T => { T with oracle := 999 } }⟩ = false := by
  decide +kernel

end H2K.Member

#print axioms H2K.Member.member_O
#print axioms H2K.Member.member_O10
#print axioms H2K.Member.payY_O
#print axioms H2K.Member.payRec_O
#print axioms H2K.Member.payNum_O
#print axioms H2K.Member.o_below
#print axioms H2K.Member.o_moved
#print axioms H2K.Member.o_far
#print axioms H2K.Member.o_alien
#print axioms H2K.Member.o_comb
#print axioms H2K.Member.o_term
