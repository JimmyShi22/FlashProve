-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorAtAll.lean: `DoorStays`
(Johnson/Desc/Last/ShapeDoorFold.lean: what SH₃ at the small door still asks of the first table's
meaning and table, and of the list of rounds) AT THE COMPOSED MEANING `Sound.mgAll 𝔇
Mg` AND THE FULL SIZE'S WRITTEN LISTS: FIVE OF ITS SEVEN FIELDS ARE PAID; AND `sh₃_fold_X` APPLIED
THERE. Statements with their proofs; no definition.

The premise "the base
meaning's list of extra tests is empty" IS NOT ASKED (Johnson/Desc/Last/ShapeDoorMore.lean's
`laid_open_any`); the application is `sh₃_at_mgAll`.

Main names (namespace `VerifiableInference.Desc.Last`).
  `mgAll_laid`: `(mgAll 𝔇 Mg).pub .evalLaid a = K13.Law.evalLaidB 𝔇.pubD.P13 a.2`: by `mgAll_pub`
    (MgAll.lean) and `pubAll_evalLaid` (PubAllAt.lean); that the test with code `K13.evalLaidC` is
    `evalLaidB` closes here by rfl (the lemma `K13.Law.evalLaidC_eq`, FillK13Laws.lean, says the
    same; its file is not imported).
  **`doorStays_mgAll`**: `DoorStays N₁ (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true)
    𝔇.pubD.P13 V`: ITS PREMISES: V.index = N₁.index · V.w = N₁.w · V.indexShape.answers = 1 ·
    V.wShape.answers = 1. held: `mgAll_held` (Johnson/Desc/Sound/MgAll.lean); indexIn, wIn:
    Johnson/Desc/Last/ShapeDoorClosed.lean.
  **`sh₃_at_mgAll`**: `sh₃_fold_X` at that meaning, these lists and that `DoorStays`: SH₃'s
    conclusion and X, under NINE premises: these four, hR (the four fold facts at Rc) and
    `sh₃_fold_X`'s own hZ, hg, hb and hs.

WHAT STAYS A PREMISE: the two counts of answers: numbers of the list of rounds. As reported,
both ran as named tests at the full size off the public files and said 1: A RUN IS NO
PAYER: no theorem in scope says so. THAT ONE V MEETS THE FOUR PREMISES AND hR's `ownSitsB V`
TOGETHER IS SHOWN BY NOBODY: no member.
Limits. N₁, V, 𝔇, Mg are letters. The closed constant (P5J.mgAtAll, MgAtAll.lean) has its list of
places as `At.ps` (Johnson/P5J/LettersAt.lean), another term (`flatPlacesOf fullLinks true`):
the join is a lemma in other files, not called here. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorFold
import Johnson.Desc.Last.ShapeDoorClosed
import Johnson.Desc.Last.ShapeDoorMore
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.K13.Law.Bools

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open OnBytes

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets flatPlacesOf pubAll_evalLaid)
open _root_.Desc.K14 (St)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Xp : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR Xp) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The composed meaning's test at the table's own item "evalLaid". -/
theorem mgAll_laid (a : P × First.S) :
    (mgAll 𝔇 Mg).pub .evalLaid a = K13.Law.evalLaidB 𝔇.pubD.P13 a.2 := by
  rw [mgAll_pub, pubAll_evalLaid]
  rfl

/-- **`DoorStays` AT THE COMPOSED MEANING AND THE FULL SIZE's WRITTEN LISTS.** -/
theorem doorStays_mgAll (N₁ : Numbers) (V : OwnSeats)
    (hi : V.index = N₁.index) (hw : V.w = N₁.w) (h6 : V.indexShape.answers = 1)
    (h7 : V.wShape.answers = 1) :
    DoorStays N₁ (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) 𝔇.pubD.P13 V where
  laid := mgAll_laid 𝔇 Mg
  held := fun j t a => by rw [mgAll_held]
  laidOpen := laid_open_any _
  indexIn := hi ▸ index_sampled_full N₁
  wIn := hw ▸ w_sampled_full N₁
  oneIndex := h6
  oneW := h7

/-- **SH₃'s CONCLUSION AND X, AT THE COMPOSED MEANING AND THE FULL SIZE's WRITTEN LISTS**:
`sh₃_fold_X` applied. -/
theorem sh₃_at_mgAll {C : CK} {D : WholeD} {all : List LeftT} {Y X₁ X₂ Cl Wt : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm₀ : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (V : OwnSeats)
    (hi : V.index = N₁.index) (hw : V.w = N₁.w) (h6 : V.indexShape.answers = 1)
    (h7 : V.wShape.answers = 1)
    (Rc : ProofFile.InstPub × First.S → Prop)
    (hR : ∀ q, Rc q → (g q).2.failed = none → FourFacts V (g q).2) (X : St → Bool)
    (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃)
    (hb : onQ₂ N (besideP Pm₀ fun k d => doorX (ProofFile.pAt Z) (1 + T.l₂.length) k d &&
        (k != 1 + T.l₂.length || X d))
      (fun q y => ocEnd g N₁ (mgAll 𝔇 Mg) linksFull (flatPlacesOf linksFull true) q y ∧ Rc q)
      split T.p₂ T.l₂ (1 + T.l₂.length) b)
    (hs : ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s) :
    (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true ∧
      X b.1.2 = true :=
  sh₃_fold_X o pol lay KL Z hZ Np c R g hg T N Pm₀ split N₁ (mgAll 𝔇 Mg) linksFull
    (flatPlacesOf linksFull true) 𝔇.pubD.P13 V (doorStays_mgAll 𝔇 Mg N₁ V hi hw h6 h7) Rc hR X b s
    hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.mgAll_laid
#print axioms VerifiableInference.Desc.Last.doorStays_mgAll
#print axioms VerifiableInference.Desc.Last.sh₃_at_mgAll
