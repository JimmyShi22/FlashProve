-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/JoinPieces.lean: THREE CLOSED FACTS ON THREE PIECES OF THE RUN ON SHAPES, THE
TWO INNER BORDERS WRITTEN WITHOUT `look` AND `lookHeard`, JOINED: AT THE PUBLIC RECORD THAT
publicOfO RETURNS AT THE STORED FULL-SIZE FILES THE RUN OVER THE TABLE's SECOND TEXT GOES FROM THE
FIRST WRITTEN SHAPE TO THE LAST. THE THREE FACTS ARE PREMISES HERE. General in the four shapes, the
four numbers and the hints. Five definitions, five theorems; nothing is evaluated.

Purpose. See PairAside.lean. A link of the first chain was too dear for Lean's kernel in one line
(timed trials; not shown here). Cut in three, each piece is a closed Bool under `atXLC`
(AtXCounts.lean), to be shown by the kernel in a file of its own. This file is the part that needs
no kernel line.

The three facts, at shapes c₀ c₁ c₂ c₃ and numbers m k k' k''; runH hint X m k a is the run of k
members from m on over the light cells (`shapeH hint (LWn X)`, TabLight.lean). THE LATER STARTS ARE
SPELLED AS SUMS: m + k and m + k + k' (for link 1: 15 + 8 and 15 + 8 + 1, not 23 and 24): a piece's
file must state its fact so, or turn the numeral by a line of arithmetic.
* P1: from c₀ the k members from m on return x, and x less the two is c₁ (`lessB`).
* P2: from c₁ WITH THE PAIR THAT P1's RUN LEFT (`lkA`: a term in X) the next k' return x, and x less
  the two is c₂.
* P3: from c₂ WITH THE PAIR THAT P2's RUN LEFT (`lkB`) the next k'' return c₃, whole (`wholeB`).

Main names.
* `runFrom_add`: the run from a border splits at every later border. General in the shape; typed at
  the first chain's state alone, though nothing in its proof needs that.
* `runH`, `lessB`, `wholeB`, `lkA`, `lkB`; `lessB_ok`, `wholeB_ok`. The five definitions are marked
  noncomputable: they are meant for Lean's kernel alone, and no code is to be compiled for them.
* **`three_pieces`**: hsz, P1, P2, P3 ⊢ ∃ X₀, publicOfO … = .ok X₀ ∧ ∃ b₁ b₂, the three equations
  (shapeL (LWn X₀)).runFrom … = .ok … that `run_of_pieces` asks. **`three_as_one`**: the same as
  (shapeL (LWn X₀)).runFrom m (k + k' + k'') c₀ = .ok c₃.

How. `atXLC_zFull` carries each fact to what publicOfO returns; a maker is a function, so the three
records are one. There `cellsH_eq`, whose premise `hpad_of_public` pays, and `runFrom_congr`
(LettersRun.lean) turn the light run into the table's. `ok_of_less` (a product's eta) makes of "x
less the two is c" the equation "the run returns c with its own pair". NO LAW THAT A MEMBER LEAVES
THE TWO COMPONENTS IS CALLED OR WANTED.

Limits. UNDER hsz (shown in the side library: AtFullSide/Layout/Size.lean: lay_size) AND UNDER THE
THREE FACTS, WHICH NOBODY SHOWS HERE: no such fact stands in the library. The inner borders b₁ and
b₂ are terms that hold a run: the theorem says that they exist, not what they are. A FACT ALONE CAN
BE TRUE ALTHOUGH THE PIECE IN FRONT REFUSED: lkA and lkB then answer (none, none): only together do
the three say what the conclusion says; a file that states P2 or P3 alone should say so. THE CUT IN
THREE DOES NOT CUT THE WORK IN THREE WHERE A LATER PIECE READS THE PAIR: lkA and lkB are matches on
a run's outcome: to read any part of them the evaluator must bring the run in front to its return;
an attention link's batching reads both components. Nothing holds m + k + k' + k'' below the table's
358 members: from 357 on the table answers with the seal's cell. Each use returns its own record
under "there is": whoever joins many links must make the records one. At VerifierAndGoals.storedPublicFiles alone;
synthetic weights. LWn X₀ is no test on X₀. From shapeL (LWn X₀) to the table's own steps under the
head: `yes_of_publicN` (YesAtZFullN.lean), not called here. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.TabLight
import Johnson.AtFull.Shape.PairAside
import Johnson.AtFull.Shape.AtXCounts
import Johnson.AtFull.Shape.LettersNumerals
import Johnson.AtFull.Shape.ShapeDecEqL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside
open VerifiableInference.PlanWritten (publicOfO)

/-- **The run from a border splits at every later border.** (ShapeRun.lean's run_add, for
runFrom.) -/
theorem runFrom_add (Z : ProofFile.Honest.Shape VerifiableInference.Desc.First.S) (m n₁ : Nat) :
    ∀ (n₂ : Nat) (a : Z.Sh),
      Z.runFrom m (n₁ + n₂) a = (Z.runFrom m n₁ a).bind (Z.runFrom (m + n₁) n₂)
  | 0, a => by
    show Z.runFrom m n₁ a = _
    cases Z.runFrom m n₁ a <;> rfl
  | n₂ + 1, a => by
    show (Z.runFrom m (n₁ + n₂) a).bind (Z.g (m + (n₁ + n₂))) = _
    rw [runFrom_add Z m n₁ n₂ a]
    cases Z.runFrom m n₁ a with
    | error e => rfl
    | ok b =>
      show (Z.runFrom (m + n₁) n₂ b).bind (Z.g (m + (n₁ + n₂))) =
        (Z.runFrom (m + n₁) n₂ b).bind (Z.g (m + n₁ + n₂))
      rw [Nat.add_assoc]

section
variable (hint : Nat → List (Nat × Nat))

/-- The run of k members from m on, over the light cells at LWn X. -/
noncomputable def runH (X : Verify.Public) (m k : Nat) (a : ShA) : Except String ShA :=
  (shapeH hint (LWn X)).runFrom m k a

/-- "It returns x, and x less the two is c." -/
noncomputable def lessB (r : Except String ShA) (c : ShA) : Bool :=
  match r with
  | .ok x => @decide (less x = c) (ByLists.decShAL _ _)
  | .error _ => false

/-- "It returns c." -/
noncomputable def wholeB (r : Except String ShA) (c : ShA) : Bool :=
  match r with
  | .ok x => @decide (x = c) (ByLists.decShAL _ _)
  | .error _ => false

/-- Where lessB accepts, the run returned c with its own pair. -/
theorem lessB_ok {r : Except String ShA} {c : ShA} (h : lessB r c = true) :
    r = .ok (withLk c (pairE r)) := by
  cases r with
  | error e => cases h
  | ok x => exact ok_of_less rfl (@of_decide_eq_true _ (ByLists.decShAL _ _) h)

/-- Where wholeB accepts, the run returned c. -/
theorem wholeB_ok {r : Except String ShA} {c : ShA} (h : wholeB r c = true) : r = .ok c := by
  cases r with
  | error e => cases h
  | ok x => exact congrArg Except.ok (@of_decide_eq_true _ (ByLists.decShAL _ _) h)

/-- The pair that the first piece leaves; (none, none) where that piece's run refuses. -/
noncomputable def lkA (m k : Nat) (c₀ : ShA) (X : Verify.Public) : Pair :=
  pairE (runH hint X m k c₀)

/-- The pair that the second piece leaves; (none, none) where that piece's run refuses. -/
noncomputable def lkB (m k k' : Nat) (c₀ c₁ : ShA) (X : Verify.Public) : Pair :=
  pairE (runH hint X (m + k) k' (withLk c₁ (lkA hint m k c₀ X)))

/-- **THE JOIN OF THREE PIECES WITH THE PAIR SET ASIDE**: three closed facts under atXLC ⊢ at the
record X₀ that publicOfO returns at the stored full-size files: the three equations that
run_of_pieces asks, AT THE TABLE's SECOND TEXT shapeL (LWn X₀). The statement says that two inner
borders exist, not what they are (in the proof: c₁ and c₂ with the pair that the piece in front
left). three_as_one draws its conclusion from this one by runFrom_add. -/
theorem three_pieces (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k' k'' : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2 : atXLC (fun X => lessB (runH hint X (m + k) k' (withLk c₁ (lkA hint m k c₀ X))) c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + k') k''
      (withLk c₂ (lkB hint m k k' c₀ c₁ X))) c₃) = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      ∃ b₁ b₂ : ShA,
        (shapeL (LWn X₀)).runFrom m k c₀ = .ok b₁ ∧
        (shapeL (LWn X₀)).runFrom (m + k) k' b₁ = .ok b₂ ∧
        (shapeL (LWn X₀)).runFrom (m + k + k') k'' b₂ = .ok c₃ := by
  obtain ⟨X₀, hX, t1⟩ := atXLC_zFull hsz P1
  obtain ⟨X₁, hX1, t2⟩ := atXLC_zFull hsz P2
  obtain ⟨X₂, hX2, t3⟩ := atXLC_zFull hsz P3
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX1.symm.trans hX)
  obtain rfl : X₂ = X₁ := Except.ok.inj (hX2.symm.trans hX)
  have hp : ∀ (g : Nat) (A : Attention.Plan), (LWn X₂).XG.A[g]? = some A →
      VerifiableInference.Desc.First.Att.P.padKeyOk
        (VerifiableInference.Desc.First.Att.P.parCOf A).geo = true :=
    fun g A hA => hpad_of_public hX g A hA
  have e : ∀ m k a, (shapeL (LWn X₂)).runFrom m k a = runH hint X₂ m k a := fun m k a =>
    (runFrom_congr (funext fun n => congrArg Prod.fst (cellsH_eq hint _ hp n))
      (funext fun n => congrArg Prod.snd (cellsH_eq hint _ hp n)) m k a).symm
  exact ⟨X₂, hX, withLk c₁ (lkA hint m k c₀ X₂), withLk c₂ (lkB hint m k k' c₀ c₁ X₂),
    (e _ _ _).trans (lessB_ok t1), (e _ _ _).trans (lessB_ok t2), (e _ _ _).trans (wholeB_ok t3)⟩

/-- **THE SAME AS ONE EQUATION**: from c₀ the k + k' + k'' members from m on return c₃: the form in
which run_of_pieces takes a piece whose two borders stand between links. -/
theorem three_as_one (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (m k k' k'' : Nat) (c₀ c₁ c₂ c₃ : ShA)
    (P1 : atXLC (fun X => lessB (runH hint X m k c₀) c₁) = true)
    (P2 : atXLC (fun X => lessB (runH hint X (m + k) k' (withLk c₁ (lkA hint m k c₀ X))) c₂) = true)
    (P3 : atXLC (fun X => wholeB (runH hint X (m + k + k') k''
      (withLk c₂ (lkB hint m k k' c₀ c₁ X))) c₃) = true) :
    ∃ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).runFrom m (k + k' + k'') c₀ = .ok c₃ := by
  obtain ⟨X₀, hX, b₁, b₂, e1, e2, e3⟩ := three_pieces hint hsz m k k' k'' c₀ c₁ c₂ c₃ P1 P2 P3
  refine ⟨X₀, hX, ?_⟩
  rw [runFrom_add, runFrom_add, e1]
  show ((shapeL (LWn X₀)).runFrom (m + k) k' b₁).bind _ = _
  rw [e2]
  show (shapeL (LWn X₀)).runFrom (m + (k + k')) k'' b₂ = _
  rw [← Nat.add_assoc]
  exact e3

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.runFrom_add
#print axioms Johnson.AtFull.Shape.runH
#print axioms Johnson.AtFull.Shape.lessB
#print axioms Johnson.AtFull.Shape.wholeB
#print axioms Johnson.AtFull.Shape.lessB_ok
#print axioms Johnson.AtFull.Shape.wholeB_ok
#print axioms Johnson.AtFull.Shape.lkA
#print axioms Johnson.AtFull.Shape.lkB
#print axioms Johnson.AtFull.Shape.three_pieces
#print axioms Johnson.AtFull.Shape.three_as_one
