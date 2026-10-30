-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/JoinAll.lean: THE JOIN's CONCLUSIONS IN THE FORM IN WHICH MANY OF THEM CAN BE
LAID TOGETHER: "at every record that publicOfO returns at the stored full-size files" in place of
"there is a record that it returns, and …": `RunsAll`, `one_all`, `three_all`, `four_all`,
`RunsAll.chain`, `yes_of_runsAll`. One definition, eleven theorems. General laws and implications;
nothing is evaluated.

Purpose. three_as_one (JoinPieces.lean) and four_as_one (JoinHalves.lean) each conclude ∃ X₀,
publicOfO … = .ok X₀ ∧ ‹the run from one written border returns the next›. Whoever lays 25 links'
facts together would have to make 25 records one. publicOfO is a function: so each fact holds at
EVERY record that it returns, and in that form the facts chain without that step.

Main names.
* `runFrom_chain`: two stretches of a run on shapes, one behind the other, are one stretch (from
  runFrom_add).
* `RunsAll m n a b`: at every X₀ with publicOfO secondHashFunction storedPublicFiles.pol storedPublicFiles.KL (some storedPublicFiles.lay) = .ok X₀:
  (shapeL (LWn X₀)).runFrom m n a = .ok b.
* `runsAll_of_ex`: from the form with "there is". `record_there`: under hsz publicOfO returns a
  record. **`RunsAll.ex`**: the way back: under hsz a RunsAll gives the form with "there is".
  `RunsAll.chain`: RunsAll m n₁ a b → RunsAll (m + n₁) n₂ b c → RunsAll m (n₁ + n₂) a c.
* `runH_eq`: at a record that publicOfO returns, the run over the light cells is the run over the
  table's second text. **`one_all`**: a piece shown by ONE closed fact, its whole value compared
  (atXLC (fun X => wholeB (runH hint X m k c₀) c₁) = true) ⊢ RunsAll m k c₀ c₁.
* **`three_all`**, **`four_all`**: three_as_one's and four_as_one's premises, sign for sign ⊢
  RunsAll m (k + k' + k'') c₀ c₃ | RunsAll m (k + 1 + k'') c₀ c₃: THEIR SISTERS' CONCLUSIONS LESS
  THE CLAUSE "a record is there".
* **`yes_of_runsAll`**: with a named shape at each border (the frame's house's `border len`,
  Johnson/Desc/ProofFile/Honest/Thread/ShapeRun.lean), one RunsAll a piece ⊢ at every such X₀:
  (shapeL (LWn X₀)).yes (c 0) (border len K) = true: yes_of_pieces at that record.
* `toy_three`: three stretches at letters: how lengths and borders are laid as lists, and that Lean
  takes a length spelled as a sum at len k.

Limits. RunsAll HOLDS EMPTILY IF publicOfO RETURNS NOTHING AT THESE FILES: whoever quotes a RunsAll
alone, without hsz beside it, quotes a sentence that does not say that any run returns; under hsz
record_there and RunsAll.ex give the record back. NOTHING HERE HOLDS THE RUN TO THE FIRST SHAPE AND
TO 358 MEMBERS: yes_of_runsAll is general in len, c and K: below 358, or from another first shape,
it gives a true sentence that the rule for acceptance cannot take; from 357 on the table answers
every number with the seal's cell, in silence: so "the n members from m on" speaks of members only
below 358. JoinTable.lean fixes both. yes_of_runsAll drops the last shape c K. The later starts are
spelled as sums (m + n₁; border len k). The closed facts are premises, as in the two files beneath.
shapeL (LWn X₀) is the table's SECOND text at written letters and numerals: LWn X₀ is no test on X₀.
At the format's second hash function; at VerifierAndGoals.storedPublicFiles alone (written copies of public files; synthetic
weights). runFrom_chain is typed at the first chain's state alone, as runFrom_add is. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Shape

/-- **Two stretches of a run, one behind the other, are one stretch.** -/
theorem runFrom_chain (Z : ProofFile.Honest.Shape VerifiableInference.Desc.First.S) {m n₁ n₂ : Nat}
    {a b c : Z.Sh} (h1 : Z.runFrom m n₁ a = .ok b) (h2 : Z.runFrom (m + n₁) n₂ b = .ok c) :
    Z.runFrom m (n₁ + n₂) a = .ok c := by
  rw [runFrom_add, h1]
  exact h2

/-- "From a the n members from m on return b, over the table's second text, AT EVERY RECORD THAT
publicOfO RETURNS at the stored full-size files." IT DOES NOT SAY THAT A RECORD IS THERE: where
publicOfO returns nothing it holds emptily. -/
def RunsAll (m n : Nat) (a b : ShA) : Prop :=
  ∀ X₀ : Verify.Public,
    publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
    (shapeL (LWn X₀)).runFrom m n a = .ok b

/-- publicOfO is a function: what holds at a record that it returns holds at every record that it
returns. -/
theorem runsAll_of_ex {m n : Nat} {a b : ShA}
    (h : ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).runFrom m n a = .ok b) : RunsAll m n a b := by
  obtain ⟨X₁, h1, e⟩ := h
  intro X₀ h0
  obtain rfl : X₁ = X₀ := Except.ok.inj (h1.symm.trans h0)
  exact e

/-- Under hsz a record is there: publicOfO returns at the stored full-size files. By the library's
join of the makers (publicOfO_zFull_of_rest hsz), which has closed facts by Lean's kernel of its own
beneath it (owners_W, widths_W and their kin); the kernel's line lettersTest_atXL is not called. -/
theorem record_there (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
        .ok X₀ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hX⟩ :=
    _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  exact ⟨_, hX⟩

/-- **The way back**: under hsz a RunsAll gives the form with "there is". -/
theorem RunsAll.ex (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {m n : Nat} {a b : ShA}
    (h : RunsAll m n a b) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).runFrom m n a = .ok b := by
  obtain ⟨X₀, hX⟩ := record_there hsz
  exact ⟨X₀, hX, h X₀ hX⟩

/-- **Two such facts, one behind the other, are one.** -/
theorem RunsAll.chain {m n₁ n₂ : Nat} {a b c : ShA} (h1 : RunsAll m n₁ a b)
    (h2 : RunsAll (m + n₁) n₂ b c) : RunsAll m (n₁ + n₂) a c :=
  fun X₀ hX => runFrom_chain _ (h1 X₀ hX) (h2 X₀ hX)

section
variable (hint : Nat → List (Nat × Nat))

/-- At a record that publicOfO returns, the run over the light cells is the run over the table's
second text. -/
theorem runH_eq {pol KL : ByteArray} {lay : Option ByteArray} {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction pol KL lay = .ok X₀) (m k : Nat) (a : ShA) :
    (shapeL (LWn X₀)).runFrom m k a = runH hint X₀ m k a :=
  (runFrom_congr
    (funext fun n => congrArg Prod.fst
      (cellsH_eq hint _ (fun g A hA => hpad_of_public hX g A hA) n))
    (funext fun n => congrArg Prod.snd
      (cellsH_eq hint _ (fun g A hA => hpad_of_public hX g A hA) n)) m k a).symm

/-- **A PIECE SHOWN BY ONE CLOSED FACT**, its whole value compared. -/
theorem one_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k : Nat) (c₀ c₁ : ShA)
    (P : atXLC (fun X => wholeB (runH hint X m k c₀) c₁) = true) : RunsAll m k c₀ c₁ := by
  obtain ⟨X₀, hX, t⟩ := atXLC_zFull hsz P
  exact runsAll_of_ex ⟨X₀, hX, (runH_eq hint hX m k c₀).trans (wholeB_ok t)⟩

/-- **three_as_one, at every record**: LESS ITS CLAUSE "a record is there" (RunsAll.ex gives it
back under hsz). -/
theorem three_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k' k'' : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2 : atXLC (fun X => lessB (runH hint X (m + k) k' (withLk c₁ (lkA hint m k c₀ X))) c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + k') k''
      (withLk c₂ (lkB hint m k k' c₀ c₁ X))) c₃) = true) :
    RunsAll m (k + k' + k'') c₀ c₃ :=
  runsAll_of_ex (three_as_one hint hsz m k k' k'' c₀ c₁ c₂ c₃ P1 P2 P3)

/-- **four_as_one, at every record**: less its clause "a record is there", likewise. -/
theorem four_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k'' : Nat) {l : Nat} (hl : l < 24)
    (ho : l % 2 = 1) (hm : m + k = 14 * l + 9) (j : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (cl : List ClaimSh) (st : ChainSh)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2a : atXLC (fun X => frontB (frontH X l j (withLk c₁ (lkA hint m k c₀ X))) cl st) = true)
    (P2b : atXLC (fun X => backB (backH X l j
      (cl, withLkC st (pairH (frontH X l j (withLk c₁ (lkA hint m k c₀ X)))))) c₁.2 c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + 1) k''
      (withLk c₂ (lkB hint m k 1 c₀ c₁ X))) c₃) = true) :
    RunsAll m (k + 1 + k'') c₀ c₃ :=
  runsAll_of_ex (four_as_one hint hsz m k k'' hl ho hm j c₀ c₁ c₂ c₃ cl st P1 P2a P2b P3)

end

/-- **THE ASSEMBLY's FORM**: with a named shape at each border, one RunsAll a piece gives, at every
record that publicOfO returns, that the run on shapes over all pieces returns: yes_of_pieces'
premise, paid piece by piece without making the pieces' records one. -/
theorem yes_of_runsAll (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (h : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    (shapeL (LWn X₀)).yes (c 0) (ProofFile.Honest.border len K) = true :=
  ProofFile.Honest.yes_of_pieces (shapeL (LWn X₀)) len c K fun k hk => h k hk X₀ hX

/-- A TOY OF THREE STRETCHES, at letters: how a caller lays lengths and borders as lists; that Lean
takes a length spelled as a sum (8 + 1 + 5) at len k, and the numerals 1 and 15 at border len k,
which is itself a sum. -/
theorem toy_three (a b c d : ShA) (h0 : RunsAll 0 1 a b) (h1 : RunsAll 1 14 b c)
    (h2 : RunsAll 15 (8 + 1 + 5) c d) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : (shapeL (LWn X₀)).yes a 29 = true :=
  yes_of_runsAll (fun k => [1, 14, 14].getD k 0) (fun k => [a, b, c, d].getD k a) 3
    (fun k hk => match k, hk with
      | 0, _ => h0
      | 1, _ => h1
      | 2, _ => h2) X₀ hX

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.runFrom_chain
#print axioms Johnson.AtFull.Shape.RunsAll
#print axioms Johnson.AtFull.Shape.runsAll_of_ex
#print axioms Johnson.AtFull.Shape.record_there
#print axioms Johnson.AtFull.Shape.RunsAll.ex
#print axioms Johnson.AtFull.Shape.RunsAll.chain
#print axioms Johnson.AtFull.Shape.runH_eq
#print axioms Johnson.AtFull.Shape.one_all
#print axioms Johnson.AtFull.Shape.three_all
#print axioms Johnson.AtFull.Shape.four_all
#print axioms Johnson.AtFull.Shape.yes_of_runsAll
#print axioms Johnson.AtFull.Shape.toy_three
