-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/LastOnePage.lean: THE LAST CHAIN ON ONE PAGE: EachOwn (Johnson/Desc/Sound/Spine.lean) AT THE TABLE OF THE LAST CHAIN's JOINTS (Johnson/Desc/Last/BordersLast.lean · Johnson/Desc/Sound/BordersLastQ.lean), OF ITS FOUR BLOCKS, FROM THE NAMED DEBTS
OF ALL FOUR ROWS. A joining: every arrow that it calls is proved elsewhere; nothing of the debts is paid here.

  x₂ = pieceTwoT: block 2's piece: the kind K12's block at a seat, "below the prime" in front, laid at the pair (pieceTwoX, RowTwoCand.lean), WITH THE ROW's OWN EXTRACTOR (extAt … mine [] …, World.lean: the members' components are set to what they decode to).
  RowTwoAtTable: WHAT IS OWED AT ROW 2, AT THE TABLE's OWN LETTERS:
    debt     RowTwoOwes (RowTwoCand.lean: place · opens · NH | bat · seam · behind, each with the files that are to pay it; RowTwoDebt.owes gives it from the form split into cand | rows) at on | on' := the table's promise at borders 2 | 3 and ins := the item "rows" (ML.rows of the chain's own record);
    nodup    no two of mine have one number · seats  the members' seats fit · fence  they lie in trees sent in front of the block: tests on the plan;
    prom     the table's promise at border 2 gives the promise in front of the block (held, shown, no collision, for each of mine): left to the table's files;
    pins     "each of mine is pinned" (PinAt) is what the table's three items pinV | pinI | pinO say at border 2: left to the table's files (the table's tied meaning).
  **rowTwo_own**: so Piece.Own at row 2: by rowTwo_goodIn. With frames_rowTwo (RowTwoOwn.lean: nothing rides past block 2) that is row 2's clause of EachOwn.
  RowZeroOwed x₀: row 0's two conjuncts, as they are: THE CONCLUSION OF row0_each (Johnson/Desc/Third/Law/Row0Frames.lean: not imported here) at the table's letters: a premise.
  RowOneOwed, RowThreeOwed: rows 1 and 3 (QuietRows.lean).
  **eachOwn_last**: RowZeroOwed x₀ → RowOneOwed x₁ → RowTwoAtTable → RowThreeOwed x₃ → EachOwn … 0 [x₀, x₁, pieceTwoT …, x₃]: by eachOwn_of_rows (QuietRows.lean): called, not typed anew.

Silly members. mine := []: pins then asks the three items of every witness inside the promise: unpayable unless they are empty: so a table with real pins forces mine. ML.rows := fun _ _ => True: the second half of debt.seam's conclusion is for nothing, and the item on which the claim on the weights hangs says nothing
(the table's own head warns of it: PromMeaningL.shape).
Every "there is", walked: no statement of this file has one.
Cl, the type of claims, is a letter: all four pieces stand at one Cl, the description's. C, the kit of challenges, is ckP .two: the kind's law's own.
Limits. A JOINING. NO MEMBER OF THE FOUR DEBTS TOGETHER IS SHOWN. The weight lies in debt.bat | seam (row 2) and in row 0's law. What EachOwn is spent for (LastJoin | LastJoinPlain) is left to the table's files. Nothing on soundness of its own; nothing on hiding.

-/
import Johnson.Flat.Last.RowTwoCand
import Johnson.Flat.Last.RowTwoOwn
import Johnson.Desc.Sound.QuietRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last

section
variable {P S₁ S₂ S₃ Cells Tok Cl : Type} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)
  (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : ((P × S₁ × S₂) × S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → ((P × S₁ × S₂) × S₃) → Option Cells) (c₀ : Cells)
  (π : P12) (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (enter : S₃ → Except String T12) (leave : S₃ → T12 → Except String S₃) (mine : List Mem)

/-- **Block 2's piece, with the row's own extractor.** -/
def pieceTwoT : Piece (ckP .two) Fr ((P × S₁ × S₂) × S₃) Cl (Wit Cells Tok MsgT) :=
  pieceTwoX Fr π base dB dt e₀ εt enter leave
    fun a _ w => extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w

/-- **What is owed at row 2, at the table's own letters.** -/
structure RowTwoAtTable (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) where
  debt : RowTwoOwes cs G arr smp Fr π base dB dt e₀ εt enter leave mine (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3)
    (fun a w => ML.rows a.1.2 w) num no L mC mS mW rad rd
  nodup : (mine.map (numOf arr)).Nodup
  seats : SeatsFit cs G mine
  fence : Fenced base mine
  prom : ∀ a : ((P × S₁ × S₂) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 2 a → Promised cs G smp mine a.1 (strsOf Fr a.2)
  pins : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 2 a → Pinned cs G arr smp mine a.1 (strsOf Fr a.2) w →
    meansQ₃ N Mg ML .pinV a w ∧ meansQ₃ N Mg ML .pinI a w ∧ meansQ₃ N Mg ML .pinO a w

variable {N Mg ML Pm PL Oc cs G arr smp π base dB dt e₀ εt enter leave mine}

/-- **ROW 2's OWN LAW AT THE TABLE.** -/
theorem rowTwo_own {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (T : RowTwoAtTable (Fr := Fr) N Mg ML Pm PL Oc cs G arr smp π base dB dt e₀ εt enter leave mine num no L mC mS mW rad rd) :
    (pieceTwoT (Cl := Cl) (Fr := Fr) cs G arr smp decT c₀ π base dB dt e₀ εt enter leave mine).Own (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3)
      (meansQ₃ N Mg ML) (insQ₃ 2) (outsQ₃ 2) := by
  intro a ha
  refine Doomed.mono _ _ ?_
    (rowTwo_goodIn T.debt decT c₀ (relAt (meansQ₃ N Mg ML) (outsQ₃ 2)) T.nodup T.seats T.fence a ⟨ha, T.prom a ha⟩)
  intro τ hτ b hb
  refine ⟨(hτ b hb).1, fun w hw i hi => ?_⟩
  obtain ⟨hp, hr⟩ := (hτ b hb).2 w hw
  obtain ⟨pV, pI, pO⟩ := T.pins a _ ha hp
  have e' : insL₃ 2 = [.rows, .pinV, .pinI, .pinO] := by decide
  have hi' : i ∈ insL₃ 2 := hi
  rw [e'] at hi'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl
  · exact hr
  · exact pV
  · exact pI
  · exact pO

/-- Row 0's two conjuncts of EachOwn, as they are: the conclusion of row0_each at the table's letters. -/
def RowZeroOwed (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) (Wit Cells Tok MsgT)) (ML : MeaningL S₃ (Wit Cells Tok MsgT)) (Pm : PromMeaning S₂)
    (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)
    (x : Piece (ckP .two) Fr ((P × S₁ × S₂) × S₃) Cl (Wit Cells Tok MsgT)) : Prop :=
  x.Own (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (insQ₃ 0) (outsQ₃ 0) ∧
    x.Frames (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0)

/-- **THE LAST CHAIN ON ONE PAGE: EachOwn of its four blocks, from the named debts of all four rows.** -/
theorem eachOwn_last {num : Fmt.TreeSource → ℕ} {no : ℕ → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {rd : ℕ → ℕ}
    (x₀ x₁ x₃ : Piece (ckP .two) Fr ((P × S₁ × S₂) × S₃) Cl (Wit Cells Tok MsgT))
    (h₀ : RowZeroOwed N Mg ML Pm PL Oc x₀) (h₁ : RowOneOwed N Mg ML Pm PL Oc x₁)
    (T : RowTwoAtTable (Fr := Fr) N Mg ML Pm PL Oc cs G arr smp π base dB dt e₀ εt enter leave mine num no L mC mS mW rad rd)
    (h₃ : RowThreeOwed N Mg Pm PL Oc x₃) :
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      [x₀, x₁, pieceTwoT cs G arr smp decT c₀ π base dB dt e₀ εt enter leave mine, x₃] :=
  eachOwn_of_rows N Mg ML Pm PL Oc x₀ x₁ _ x₃ h₀ h₁ ⟨rowTwo_own decT c₀ T, frames_rowTwo N Mg ML Pm PL Oc _⟩ h₃

end

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.rowTwo_own
#print axioms VerifiableInference.OnPublicFiles.Last.eachOwn_last
