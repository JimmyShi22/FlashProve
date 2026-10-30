-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
AtFullSide/Honest/RestOwedAtTheLetters.lean: the two kinds that part 5's gather of the first thread's debt leaves as premises
(RestOwed.k2 and RestOwed.k10, Johnson/AtFull/Shape/Scope/OwesGather.lean), at the first chain's named letters
(AtFullSide/Honest/TheLettersFirst.lean). A joining; nothing is evaluated here.

  typedAtRun_of_tiedYes     the public part of the run's own input is a typed instance's, from the first clause of TiedYes and
                            the return of ready: the premise hw of the code switch's five
  kindTwo_paid_at_letters   KindPaid at the kind K2, from the maker's return, the head and hw: part 1's k2_five_at_letters
                            through part 5's paidAt_of_five
  kindTwo_paid_at_tiedYes   the same with hw paid by typedAtRun_of_tiedYes
  kindTen_paid_at_the_letters   KindPaid at the kind K10: kindTen_paid_at_letters, at the maker under its name baseMaker

Limits. The maker's return and the head are premises, and so are the relation TiedYes and the return of ready. KindPaid speaks
at the stands at which the thread's invariant and what is said hold; that a run stands there is not shown here. Nothing on
soundness, completeness or hiding.
-/
import AtFullSide.K2.AtTheLetters
import AtFullSide.K10.OwedAtLetters
import AtFullSide.Honest.InstanceTie
import Johnson.AtFull.Shape.Scope.OwesByKind
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.OwesOne
open VerifiableInference.Desc (Chain KindName FileDescription)
open P5J (TS)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles WZ TiedYes descZ)
open LPFD.Full (XF)
open OnBytes (TableKey)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open AtFullSide.Honest.TheLetters (first said₁)
open AtFullSide.K2.Base (TypedAtRun k2_five_at_letters)
open Johnson.AtFull.Shape.Scope (KindPaid paidAt_of_five)

/-- **The run's own input is of a typed instance.** Of the relation the first clause alone is read; the description, the book
and the prover at which ready returns are letters. -/
theorem typedAtRun_of_tiedYes (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
    (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ X')
    (Hp : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X')
    {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ Z} {x : ProofFile.Inst}
    (tied : TiedYes Z Zp Np cF run₂ run₃ B G Hp Yes n w x)
    {F : FileDescription ProofFile.Inst} {Bk : ProverCoinCounts} {H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins}
    {k : Coins Bk} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready F Bk H w₀ rc x k = .ok R) : TypedAtRun R.own := by
  obtain ⟨⟨x', -, rfl⟩, -⟩ := tied
  obtain ⟨-, tr, -, hown, -⟩ := ready_ok returns
  exact ⟨(x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2), by rw [hown]⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **RestOwed.k2 at the letters**, from the maker's return, the head and hw. -/
theorem kindTwo_paid_at_letters (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (hw : TypedAtRun R.own) :
    KindPaid (firstLetters h (first h) R.own) (said₁ h R) KindName.K2 :=
  fun _ _ hb hk => paidAt_of_five (L := firstLetters h (first h) R.own)
    (k2_five_at_letters made h R (fun _ _ _ => none) hw hb hk)

/-- **RestOwed.k2 at the letters, at a run whose instance the relation ties.** -/
theorem kindTwo_paid_at_tiedYes (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
    (run₃ : R₃ → ByteArray) {Tr X₀ X' : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Tr X₀ X')
    (Hp : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Tr X₀ X')
    {Yes : FullSizeMatrix → XF → Prop} {n : ℕ} {w : WZ files} {x : ProofFile.Inst}
    (tied : TiedYes files Zp Np cF run₂ run₃ B G Hp Yes n w x)
    {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (returns : ready h.description A.B A.H w₀ rc x k = .ok R) :
    KindPaid (firstLetters h (first h) R.own) (said₁ h R) KindName.K2 :=
  kindTwo_paid_at_letters made h R (typedAtRun_of_tiedYes files Zp Np cF run₂ run₃ B G Hp tied returns)

/-- **RestOwed.k10 at the letters**, from the maker's return and the head. -/
theorem kindTen_paid_at_the_letters (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    KindPaid (firstLetters h (first h) R.own) (said₁ h R) KindName.K10 :=
  AtFullSide.K10.kindTen_paid_at_letters h made R

end AtFullSide.Honest.OwesOne

#print axioms AtFullSide.Honest.OwesOne.typedAtRun_of_tiedYes
#print axioms AtFullSide.Honest.OwesOne.kindTwo_paid_at_letters
#print axioms AtFullSide.Honest.OwesOne.kindTwo_paid_at_tiedYes
#print axioms AtFullSide.Honest.OwesOne.kindTen_paid_at_the_letters
