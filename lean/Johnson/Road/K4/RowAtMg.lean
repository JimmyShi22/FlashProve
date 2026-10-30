-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowAtMg.lean: THE FIRST CHAIN's ROW AND THE TABLE's ONE EXTRACTOR, AT THE TERMS IN
WHICH A KIND's LAW IS TO END (`AtMg.Kind`, Johnson/P5J/RowsAtMg.lean): that `h.row` is the maker's
own row; that the premises which a law asks of its row hold there; and that `h.ex` lays nothing at
the kind K4's twelve numbers. Five theorems. A joining: each is one call.
Why. `AtMg.Kind h D0 L K` ends in `h.ex L` and `h.row L`. A law that ends in letters E and T,
under premises on them, can be called there only if these premises are shown at just these two
terms.
  `links_same`: the two definitions of the segments' sorts at the full size have one text.
  `AtMg.row_is`: `h.row L` is `T.p₁ :: T.l₁` at T := the maker's `piecesAt ...`: `atDesc`
  (Johnson/Desc/Sound/DescThree.lean) turns the six functions between the chains, no member of a
  row.
  `AtMg.pieces`, `AtMg.rows`: `pieces_at_make` and `rows_at_make`
  (Johnson/Road/K4/PiecesAtMake.lean) AT THAT T. These two are general in the data D; the row
  stands at `D.at frS.P.T.a` (D with the committed table's depth overwritten), which in scope is D
  itself: `LaidAt.atDepth` (Johnson/P5J/FourAtMg.lean): used as `AtMg.ofDesc` uses it.
  `AtMg.ex_quiet`: `k04_hE` (Johnson/Road/K4/ExtAtK4.lean), which is general in every letter but
  the segments' sorts and the places, at `h.ex L`.
Limits. A JOINING: IT PAYS NO LAW. PREMISES THAT STAY: q₁, q₂, q₃: the three lists' heads, as
`rows_at_mg` has them. Whether `AtMg` can be met at the release's own files is not shown. The full
size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtMg
import Johnson.Road.K4.PiecesAtMake
import Johnson.Road.K4.ExtAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.K4 OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain KindName)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.Sound
open _root_.Iop (Err)
open _root_.Run _root_.Run.PQ

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The two definitions of the segments' sorts at the full size have one text. -/
theorem links_same : fullLinks = linksFull := rfl

variable (h : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)

set_option quotPrecheck false in
/-- The maker's three rows, as `rowF` has them. -/
local notation "TT" => (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
  𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)

/-- **The row in which a kind's law is to end is the maker's own row.** -/
theorem AtMg.row_is : h.row 𝔏 = (TT).p₁ :: (TT).l₁ := rfl

variable (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)

include h q₁ q₂ q₃

/-- **The three premises on the rows, at that term.** -/
theorem AtMg.pieces :
    OfDesc (F0T o Zp Np cF) TT ∧
      (TT).IsCut (held 𝔏.c₁) (𝔏.k₁.map held) (held 𝔏.c₂) (𝔏.k₂.map held) (held 𝔏.c₃)
        (𝔏.k₃.map held) (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) sealRound ∧
      AtCap (restCap 𝔏.e₁) :=
  pieces_at_make (F0T o Zp Np cF) "proof file" (D.at frS.P.T.a)
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (F0T o Zp Np cF) h.laid.planOk) (ckP .two) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃
    q₁ q₂ q₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd

/-- **All the lines on the first row, at that term.** -/
theorem AtMg.rows :
    Tiled (TT).p₁ (TT).l₁ ∧ rowData (TT).p₁ (TT).l₁ = (D.at frS.P.T.a).ds₁ ∧ (TT).p₁.base = 0 ∧
      ∀ q ∈ (TT).p₁ :: (TT).l₁, q.err = Err.cap 128 (uLT (ckP .two) q.ds) :=
  rows_at_make (F0T o Zp Np cF) "proof file" (D.at frS.P.T.a)
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    (sealLast_of_planOk (F0T o Zp Np cF) h.laid.planOk) (ckP .two) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃
    q₁ q₂ q₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd

omit q₁ q₂ q₃

/-- **The table's one extractor, at the term in which a law ends, lays nothing at K4's numbers.** -/
theorem AtMg.ex_quiet (g : ℕ) (hg : g < 12) : ∀ a b w, h.ex 𝔏 (28 * g + 4) a b w = w := by
  intro a b w
  first
    | (unfold AtMg.ex exF At.ps
       rw [links_same]
       exact k04_hE _ _ _ _ _ _ _ _ _ _ g hg a b w)
    | (unfold AtMg.ex exF
       exact k04_hE _ _ _ _ _ _ _ _ _ _ g hg a b w)
    | (show extQAt _ _ _ _ _ _ _ _ _ fullLinks At.ps _ (28 * g + 4) a b w = w
       exact k04_hE _ _ _ _ _ _ _ _ _ _ g hg a b w)

end P5J

#print axioms P5J.links_same
#print axioms P5J.AtMg.row_is
#print axioms P5J.AtMg.pieces
#print axioms P5J.AtMg.rows
#print axioms P5J.AtMg.ex_quiet
