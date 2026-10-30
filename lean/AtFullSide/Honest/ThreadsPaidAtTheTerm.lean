-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/ThreadsPaidAtTheTerm.lean: the debts of the three threads at the term's letters.

The shared and the second chain's parts are sharedParts and lastParts, the third family is the run on
shapes, the first chain's falls are firstFalls, and the shared and the second chain have no fall.
At these letters three fields of ThreadDebts are laid here: the shared chain's start, the second
chain's start saying yes, and the depths at the second chain. theDebts does it from ThreadFields.
-/
import AtFullSide.Honest.DoorYesAtTheTerm
import AtFullSide.Honest.ThreadsAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  {h : HeadAtReturn files A} {first : FirstThreadParts A}
  {later : LaterLetters A} {lastLetters : LastLetters A}
  {R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit} {base : ProofFile.PureBase}
  {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}

/-- **How the later chains read the index at the filling's own index**: the weights as the filling
reads them, and the committer's coins by rand. At the term I is matrixInput and rand is randNow. -/
abbrev readsAt (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (I : WiderIn W₀) (rand : IndexCommitterCoins → TableRand) :
    IndexReaders W₀ IndexCommitterCoins :=
  ⟨I.weights A.Z, rand⟩

/-- **The debts for the run to return at the term's letters, from the fields.** -/
theorem theDebtsP {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {rand : IndexCommitterCoins → TableRand}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (late : ∀ c ∈ later.riders, 0 < c.lo)
    (D : ThreadFieldsP h first (readsAt A I rand) (sharedParts h later)
      (lastParts h first lastLetters) R x k) :
    ThreadDebtsP h first (readsAt A I rand) (sharedParts h later) (lastParts h first lastLetters) R
      w₀ rc x k :=
  { D with
    enters₂ := enters_sharedParts hR late
    depths₃ := fun b _ _ k _ _ _ _ _ _ _ _ _ _ =>
      depthsAt_of_declared (depthsDeclared_of_all _ (fun d hd o ho k w hh =>
        lastLetters.tableDepths d (by
          rw [(atPure_at_laid h.head.laid made).2]
          exact hd) o ho k w hh) (b + 1)) k _ }

/-- **The debts at the term's letters, from the fields and the run on shapes.** -/
theorem theDebts {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {rand : IndexCommitterCoins → TableRand}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base)
    {X₀ : OnBytes.Model.Verify.Public}
    (hX₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {c : ShA}
    (hc : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (hcl : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true)
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (late : ∀ c ∈ later.riders, 0 < c.lo)
    (D : ThreadFields h first (readsAt A I rand) (sharedParts h later) (lastParts h first lastLetters) R
      (shapesAtFirst h base) (firstFalls A first.numbers) [] [] x k) :
    TheThreadDebts h first (readsAt A I rand) R w₀ rc x k base later lastLetters :=
  { theDebtsP (S := S) (O := O) made hR late D.toThreadFieldsP with
    yes₁ := D.yes₁
    carry₁ := D.carry₁
    yes₂ := D.yes₂
    yes₃ := D.yes₃
    startJ := D.startJ
    doorYes := door_yes_at_term h first (readsAt A I rand) _ R x k hB hX₀ hc hcl }

/-- **At every tied run, at the term's letters**: the plan serves, and there is a value of ThreadsCJ
with the first chain's falls and no other. The run on shapes in hc and hcl is the one at the stored
files VerifierAndGoals.storedPublicFiles, so this says something where the head's files are those. -/
theorem planAndThreadsAtEveryRun {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
    {rand : IndexCommitterCoins → TableRand}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base)
    {X₀ : OnBytes.Model.Verify.Public}
    (hX₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {c : ShA} (hc : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (hcl : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true)
    (late : ∀ c ∈ later.riders, 0 < c.lo)
    {lastAt : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit → LastLetters A}
    {Tied : W₀ → IndexCommitterCoins → ProofFile.Inst → Prop}
    (stored : ∀ w₀ rc x, Tied w₀ rc x →
      ∀ d ∈ h.description.roundsDeclaredByBlocks.1 ++ h.description.roundsDeclaredByBlocks.2.1 ++ h.description.roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
        ∃ u, A.H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (D : ∀ w₀ rc x k R, Tied w₀ rc x → ready h.description A.B A.H w₀ rc x k = .ok R →
      ThreadFields h first (readsAt A I rand) (sharedParts h later)
        (lastParts h first (lastAt R)) R (shapesAtFirst h base) (firstFalls A first.numbers) [] [] x k) :
    ∀ w₀ rc x k R, Tied w₀ rc x → ready h.description A.B A.H w₀ rc x k = .ok R →
      PlanServes A.H w₀ rc R ∧
      ∃ T : ThreadsCJ h.description A.B A.H w₀ rc x k R,
        T.f₁ = firstFalls A first.numbers ∧ T.f₂ = [] ∧ T.f₃ = [] := fun w₀ rc x k R ht hR =>
  ⟨planServes hR (head_planOk h.head) (D w₀ rc x k R ht hR).rootedSides (stored w₀ rc x ht),
    threadsCJ_of_threads (head_planOk h.head)
      (fromThreadsAtTheTerm made (theDebts made hB hX₀ hc hcl hR late (D w₀ rc x k R ht hR)) hR)⟩

end AtFullSide.Honest

#print axioms AtFullSide.Honest.theDebts
#print axioms AtFullSide.Honest.planAndThreadsAtEveryRun
