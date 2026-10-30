-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroPays.lean: ONE SET: the last chain on one page (eachOwn_last,
Johnson/Flat/Last/LastOnePage.lean) WITH ROW 0's DEBT RowZeroOwed FILLED BY rowZero
(Johnson/Desc/Third/Law/Row0AtTable.lean). A joining of these two files: two theorems, each one
call.

OBJECT   rowZero's.
USER     eachOwn_last's caller (eachOwn_last_arm, Johnson/Flat/Last/LastAtArm.lean
         [not in this library], takes
         RowZeroOwed at ML := rowsOpen: rowZeroOwed_of_left is general in ML).
LETTERS  rowZero's, at the kit of challenges ckP .two and the witness's type Wit Cells Tok MsgT.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through EachOwn.

  rowZeroOwed_of_left   RowZeroLeft gives RowZeroOwed: the two are one term.
  eachOwn_last_of_left  EachOwn of the chain's four blocks from: what is left at row 0 ·
                        RowOneOwed · RowTwoAtTable · RowThreeOwed.
What is not claimed. NOTHING IS PAID HERE. NO MEMBER of the four debts together. No soundness.

-/
import Johnson.Flat.Last.LastOnePage
import Johnson.Desc.Third.Law.Row0AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
open Johnson.Pack
open Iop Prob _root_.Run
open OnBytes.Means (Words)
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (S₃ P₁₄)
open VerifiableInference.Desc.Third.Law (RowZeroLeft rowZero)

variable {P S₁ S₂ Cells Tok Cl Cl₀ : Type} {Fr : Frame} {K : Type} [Field K] {ρ : Model.Reading K}
  {N : NumbersS} {Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)}
  {ML : MeaningL S₃ (Wit Cells Tok MsgT)} {Pm : PromMeaning S₂}
  {PL : PromMeaningL S₂ S₃ (P × S₁)} {Oc : P × S₁ → Strs → Prop}
  {p : P₁₄} {lo : ℕ} {Ok : P × S₁ × S₂ → S₃ → S₃ → Prop}
  {words : P × S₁ × S₂ → S₃ → Wit Cells Tok MsgT → Words K}
  {omW wv : P × S₁ × S₂ → Wit Cells Tok MsgT → Nat → K}

/-- **What is left at row 0 gives row 0's debt of the one page.** -/
theorem rowZeroOwed_of_left
    {x : Piece (ckP .two) Fr ((P × S₁ × S₂) × S₃) Cl (Wit Cells Tok MsgT)}
    (h : RowZeroLeft ρ N Mg ML Pm PL Oc Cl₀ p x lo Ok words omW wv) :
    RowZeroOwed N Mg ML Pm PL Oc x := rowZero h

/-- **The last chain on one page, row 0 from what is left of it.** -/
theorem eachOwn_last_of_left {cs : OnBytes.Codes} {Xi : Type} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
    {smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    (decT : (ℕ → Option (ℕ × List UInt64)) → ((P × S₁ × S₂) × S₃) → Option Cells) (c₀ : Cells)
    {π : P12} {base : ℕ} {dB : RDT} {dt : List RDT} {e₀ : ℕ} {εt : Err (uLT (ckP .two) dt)}
    {enter : S₃ → Except String T12} {leave : S₃ → T12 → Except String S₃} {mine : List Mem}
    {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (x₀ x₁ x₃ : Piece (ckP .two) Fr ((P × S₁ × S₂) × S₃) Cl (Wit Cells Tok MsgT))
    (h₀ : RowZeroLeft ρ N Mg ML Pm PL Oc Cl₀ p x₀ lo Ok words omW wv)
    (h₁ : RowOneOwed N Mg ML Pm PL Oc x₁)
    (T : RowTwoAtTable (Fr := Fr) N Mg ML Pm PL Oc cs G arr smp π base dB dt e₀ εt enter leave mine
      num no L mC mS mW rad rd)
    (h₃ : RowThreeOwed N Mg Pm PL Oc x₃) :
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      [x₀, x₁, pieceTwoT cs G arr smp decT c₀ π base dB dt e₀ εt enter leave mine, x₃] :=
  eachOwn_last decT c₀ x₀ x₁ x₃ (rowZeroOwed_of_left h₀) h₁ T h₃

end VerifiableInference.OnPublicFiles.Last
