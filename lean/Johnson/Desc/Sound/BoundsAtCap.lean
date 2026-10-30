-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BoundsAtCap.lean: THE THREE BOUNDS ON A FILE's CHAINS' ERRORS ARE THEOREMS WHERE
EVERY PIECE's ERRORS ARE THE CAP.

The choice. The maker of the pieces gives the block number i, at the stretch ds, the errors
`(rest i ds).err`: a letter. Here it is named: the cap, `Err.cap 128` (Iop/ErrCap.lean): at each
written round the whole number (the number of the round's challenges) / 2^128. `AtCap rest` says
that.

Then, at every description F, all data D and every bound εs of at least 2⁻¹ ^ 128:
  `eachBelow_atCap₁ | ₂ | ₃`   every piece of the chain has its errors at most εs (`EachBelow`);
  `below_atCap₁ | ₂ | ₃`       the chain's own list of errors is at most εs
                              (`Err.Below (errOwn …) εs`).
`restCap e`: the letter made of a family of extractors e and the cap; `atCap_restCap`.

What this does NOT pay. The cap prices nothing. A block's law is owed AT the cap: its kind's files
show the law at its own count e of bad challenges and `Err.Below e (2⁻¹ ^ 128)` at its own stretch,
and come to the cap by `Err.le_cap_of_below_inv` and the law's monotony in the errors. So "every
round's count is at most 2^-128 of its challenges" is owed as before, kind by kind; it has only
moved from the file's debt into each law's last step. The cap is taken against ALL written
challenges of a round, its bits of work among them. Book-keeping: no round is evaluated and no block
of the protocol is named.
-/
import Johnson.Desc.Sound.BelowAtCuts
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {C : CK} {F' : Frame} {S W : Type}

/-- Every piece's errors are the cap. -/
def AtCap (rest : (i : ℕ) → (ds : List RDT) → Rest C F' S W ds) : Prop :=
  ∀ i ds, (rest i ds).err = Err.cap 128 (uLT C ds)

/-- Then they are at most every bound of at least 2⁻¹ ^ 128, at all numbers and stretches. -/
theorem AtCap.below {rest : (i : ℕ) → (ds : List RDT) → Rest C F' S W ds} (hc : AtCap rest)
    {εs : ℝ≥0∞} (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) : ∀ i ds, Err.Below (rest i ds).err εs :=
  fun i ds => by
    rw [hc i ds]
    exact Err.Below.mono_bound hε (Err.cap_below_inv 128 _)

/-- The letter, of a family of extractors and the cap. -/
def restCap (e : (i : ℕ) → (ds : List RDT) → S × F'.E.Str → Iop.Tr (uLT C ds) → W → W) :
    (i : ℕ) → (ds : List RDT) → Rest C F' S W ds :=
  fun i ds => ⟨e i ds, Err.cap 128 (uLT C ds)⟩

theorem atCap_restCap (e : (i : ℕ) → (ds : List RDT) → S × F'.E.Str → Iop.Tr (uLT C ds) → W → W) :
    AtCap (restCap e) := fun _ _ => rfl

variable {Xi : Type}

/-- The first chain's bound, as a file's debt asks it block by block. -/
theorem eachBelow_atCap₁ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₁) :
    EachBelow εs ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₁ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₁) :=
  eachBelow_pieces₁ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs (hc.below hε)

/-- The same, of the chain's own list of errors. -/
theorem below_atCap₁ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₁)
    (h : (rowIOR (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₁
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₁).shape =
        uLT C D.ds₁) :
    Err.Below (errOwn (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₁
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₁ D.ds₁ h) εs :=
  ownBelow _ _ _ _ _ εs _ _ _ h
    (eachBelow_atCap₁ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs hε hc)

/-- The shared chain's bound, as a file's debt asks it block by block. -/
theorem eachBelow_atCap₂ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₂) :
    EachBelow εs ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂) :=
  eachBelow_pieces₂ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs (hc.below hε)

/-- The same, of the chain's own list of errors. -/
theorem below_atCap₂ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₂)
    (h : (rowIOR (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂).shape =
        uLT C D.ds₂) :
    Err.Below (errOwn (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂ D.ds₂ h) εs :=
  ownBelow _ _ _ _ _ εs _ _ _ h
    (eachBelow_atCap₂ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs hε hc)

/-- The last chain's bound, as a file's debt asks it block by block. -/
theorem eachBelow_atCap₃ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₃) :
    EachBelow εs ((atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₃ ::
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₃) :=
  eachBelow_pieces₃ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs (hc.below hε)

/-- The same, of the chain's own list of errors. -/
theorem below_atCap₃ (F : FileDescription Xi) (D : WholeD)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs)
    (hc : AtCap rest₃)
    (h : (rowIOR (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₃
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₃).shape =
        uLT C D.ds₃) :
    Err.Below (errOwn (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₃
      (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₃ D.ds₃ h) εs :=
  ownBelow _ _ _ _ _ εs _ _ _ h
    (eachBelow_atCap₃ F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd εs hε hc)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachBelow_atCap₁
#print axioms VerifiableInference.Desc.Sound.below_atCap₁
#print axioms VerifiableInference.Desc.Sound.below_atCap₂
#print axioms VerifiableInference.Desc.Sound.below_atCap₃
