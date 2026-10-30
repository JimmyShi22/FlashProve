-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/TheThree.lean: the three rows of pieces at which the laws of the kinds of
sub-protocol are called for the proof file, as one named term, and four facts on it.

A law of a kind ends at the pieces of some T : `ThreeAt (ckP .two) D all F X₁ X₂ W` and takes four
premises on T. Here T is named, and the four are lemmas at it.
  `threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd`: `piecesAt`
    (Johnson/Desc/Sound/PaidAtDesc.lean) at `ckP .two`, with `restCap e₁`, `restCap e₂` and
    `restCap e₃` (Johnson/Desc/Sound/BoundsAtCap.lean): every piece's error bound is `Err.cap 128`.
  `theThree Z F₀ …`: `threeCap` at the proof file's data in `dataAtFiles flashProveData Z`, `(dpZ Z).at aF`.
The four, under `F.data file = .ok D`, `F.planOk = true` and the three flat lists' heads:
  `threeCap_ofDesc`   the pieces hold F's own sub-protocols (`OfDesc`); beside it `threeCap_fits`
                      and `threeCap_rowFit`. By `paidAtDesc` and `sealLast_of_planOk`
                      (Johnson/Flat/Dec/PlanOkForFree.lean).
  `threeCap_cut`      the three rows are the maker's cut of D's rounds (`Three.IsCut`), at the held
                      sub-protocols and the sealing round; `threeCap_cut₁`: the first row's equation
                      written out. By definition. No premise.
  `threeCap_cap₁`, `₂`, `₃`   the error bound at every number and stretch is `Err.cap 128`. By
                      definition. No premise.
  `written_of_data`   D is `dataOf F.tableDepth R₁ R₂ R₃` for three lists of written rounds, and
                      each is F's declared rounds, written (`WrittenAs`). By `data_ok`
                      and `written_as` (Johnson/Desc/Sound/TilesDataProofs.lean).
  `four_together`     the four at one term whose data are written as `dataOf …`, in the form in
                      which a law of a kind takes them.

Limits. The term is not closed. F, the six letters for its flat lists, the type W of witnesses, the
three families of extractors e₁ e₂ e₃ and the two witnesses d, wEnd are parameters. Nothing here
says that a description returns data or that its test on the list of rounds accepts: these are
premises. No law of a kind is called here. `theThree` stands at F₀; the theorem at the name
(`proofFileAt_of_descB`, Johnson/Goal/Skeleton/ProofAtName.lean) takes its T at `F₀.pull instP`.
No example is given. This file only combines other files' statements: it shows nothing on soundness.

-/
import Johnson.Goal.Skeleton.ProofAtName
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.BoundsAtCap
import Johnson.Desc.Sound.TilesMaker
import Johnson.Desc.Sound.TilesDataProofs
import Johnson.Flat.Dec.PlanOkForFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)

variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
    _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
  (e₂ : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁) × F.S₂) × (frameAt D (allOf D) D.key₂ 0).E.Str →
    _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
  (e₃ : (i : ℕ) → (ds : List RDT) →
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str →
    _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
  (d wEnd : W)

/-- **The three rows of pieces, with the cap at every piece.** -/
abbrev threeCap : ThreeAt (ckP .two) D (allOf D) F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W :=
  piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd

section Paid
variable {F D b₁ l₁ b₂ l₂ b₃ l₃} {file : String} (h : F.data file = .ok D)
  (hp : F.planOk = true) (q₁ : F.first.blocksInOrder = b₁ :: l₁) (q₂ : F.shared.blocksInOrder = b₂ :: l₂)
  (q₃ : F.second.blocksInOrder = b₃ :: l₃)
include h hp q₁ q₂ q₃

/-- **The first of the four: the pieces hold the description's own sub-protocols.** -/
theorem threeCap_ofDesc : OfDesc F (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd) :=
  (paidAtDesc Xi W F file D h (sealLast_of_planOk F hp) (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃
    (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).1

theorem threeCap_fits : (atDesc F (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd)).Fits :=
  (paidAtDesc Xi W F file D h (sealLast_of_planOk F hp) (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃
    (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).2.1

end Paid

theorem threeCap_rowFit {F : FileDescription Xi} {D : WholeD} {file : String} (h : F.data file = .ok D) :
    RowFit D (allOf D) (allOf D) := rowFitOfData Xi F file D h

/-- **The second: the three rows are the maker's cut of the data's rounds.** -/
theorem threeCap_cut :
    (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).IsCut (held b₁) (l₁.map held) (held b₂)
      (l₂.map held) (held b₃) (l₃.map held) (restCap e₁) (restCap e₂) (restCap e₃) sealRound :=
  ⟨rfl, rfl, rfl⟩

/-- The first row's equation, written out. -/
theorem threeCap_cut₁ :
    ((threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).p₁,
      (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).l₁) =
      cutRow (restCap e₁) [sealRound] 0 0 D.ds₁ (held b₁) (l₁.map held) := rfl

/-- **The third: the cap at every piece**, chain by chain. -/
theorem threeCap_cap₁ (i : ℕ) (ds : List RDT) :
    (restCap e₁ i ds).err = Err.cap 128 (uLT (ckP .two) ds) := rfl

theorem threeCap_cap₂ (i : ℕ) (ds : List RDT) :
    (restCap e₂ i ds).err = Err.cap 128 (uLT (ckP .two) ds) := rfl

theorem threeCap_cap₃ (i : ℕ) (ds : List RDT) :
    (restCap e₃ i ds).err = Err.cap 128 (uLT (ckP .two) ds) := rfl

/-- **The fourth: the data are those of three lists of written rounds, and these are the
description's declared rounds, written.** -/
theorem written_of_data {F : FileDescription Xi} {D : WholeD} {file : String} (h : F.data file = .ok D) :
    ∃ R₁ R₂ R₃ : OnBytes.Params.Rounds, D = dataOf F.tableDepth R₁ R₂ R₃ ∧
      WrittenAs [] (F.first.blocksInOrder.flatMap (·.rounds)) R₁ ∧
      WrittenAs [] (F.shared.blocksInOrder.flatMap (·.rounds)) R₂ ∧
      ∃ e, WrittenAs e (F.second.blocksInOrder.flatMap (·.rounds)) R₃ := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, -, hD⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  exact ⟨R₁, R₂, R₃, hD, w₁, w₂, _, w₃⟩

/-- **The four together, at one term whose data are written as `dataOf …`**: the form in which a
law of a kind takes them, at the first chain's row. -/
theorem four_together {F : FileDescription Xi} {D : WholeD} {file : String} (h : F.data file = .ok D)
    (hp : F.planOk = true) {b₁ : Block F.S₁ F.Cl} {l₁ : List (Block F.S₁ F.Cl)}
    {b₂ : Block F.S₂ F.Cl} {l₂ : List (Block F.S₂ F.Cl)} {b₃ : Block F.S₃ F.Cl}
    {l₃ : List (Block F.S₃ F.Cl)} (q₁ : F.first.blocksInOrder = b₁ :: l₁) (q₂ : F.shared.blocksInOrder = b₂ :: l₂)
    (q₃ : F.second.blocksInOrder = b₃ :: l₃) :
    ∃ R₁ R₂ R₃ : OnBytes.Params.Rounds, D = dataOf F.tableDepth R₁ R₂ R₃ ∧
      WrittenAs [] (F.first.blocksInOrder.flatMap (·.rounds)) R₁ ∧
      ∀ e₁ e₂ e₃ (d wEnd : W),
        OfDesc F (threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd) ∧
        ((threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).p₁,
          (threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).l₁) =
          cutRow (restCap e₁) [sealRound] 0 0 (dataOf F.tableDepth R₁ R₂ R₃).ds₁ (held b₁)
            (l₁.map held) ∧
        ∀ i ds, (restCap e₁ i ds).err = Err.cap 128 (uLT (ckP .two) ds) := by
  obtain ⟨R₁, R₂, R₃, hD, w₁, -, -⟩ := written_of_data h
  subst hD
  exact ⟨R₁, R₂, R₃, rfl, w₁, fun e₁ e₂ e₃ d wEnd =>
    ⟨threeCap_ofDesc e₁ e₂ e₃ d wEnd h hp q₁ q₂ q₃, rfl, fun _ _ => rfl⟩⟩

end VerifiableInference.Desc.Sound

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open _root_.Run (ckP)

/-- **The three rows of pieces at the name**: `threeCap` at the proof file's data in
`dataAtFiles flashProveData Z`. -/
abbrev theThree (Z : PublicFiles) {XiP W : Type} (F₀ : FileDescription XiP)
    (b₁ : Block F₀.S₁ F₀.Cl) (l₁ : List (Block F₀.S₁ F₀.Cl)) (b₂ : Block F₀.S₂ F₀.Cl)
    (l₂ : List (Block F₀.S₂ F₀.Cl)) (b₃ : Block F₀.S₃ F₀.Cl) (l₃ : List (Block F₀.S₃ F₀.Cl)) :=
  threeCap (W := W) F₀ ((dpZ Z).at aF) b₁ l₁ b₂ l₂ b₃ l₃

end VerifierAndGoals.AtTheName

#print axioms VerifiableInference.Desc.Sound.threeCap_ofDesc
#print axioms VerifiableInference.Desc.Sound.threeCap_fits
#print axioms VerifiableInference.Desc.Sound.threeCap_rowFit
#print axioms VerifiableInference.Desc.Sound.threeCap_cut
#print axioms VerifiableInference.Desc.Sound.threeCap_cut₁
#print axioms VerifiableInference.Desc.Sound.threeCap_cap₁
#print axioms VerifiableInference.Desc.Sound.written_of_data
#print axioms VerifiableInference.Desc.Sound.four_together
