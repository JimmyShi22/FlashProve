-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RowZeroBForm.lean: THE FORM OF row0B: THE LAST TABLE's PREMISE ON ROW 0's PIECE
AS `own3_at_top` HAS IT (Johnson/LLT25R/LastTop.lean) FOLLOWS FROM ROW 0's DEBT IN THE FORM OF ITS
LAWS' CONCLUSION (RowZeroOwed … (besideL (fillZ (P2Third.lastPar Z) R …) X) Oc (pieceOf (heldZero
(P2Third.lastPar Z)) base ds back r)), AT EVERY M₁, G, arr, links, X, Rc. One theorem: "the four
equations", and none of the laws that end in that form (rowZeroOwed_…): so it stands over the last
table's own files, with the library's two files that define fillZ and heldZero, which it imports by
name.

  row0B_of_form   H: the debt in that form, at codes cs', at R := (c2 N).rounds, base := D.t₁ +
  D.t₂,
                  ML := ⟨rowsOpen cs' arr D.t₁ D.t₂⟩, smp₂ := smpSt cs' oNo stSh, for EVERY ds, back
                  and r whose extractor is the identity · hcs : cs' = (p14At Z).codes ⊢ row0B.
THE FOUR EQUATIONS. fillAt … (endedX X) = besideL (fillZ …) X: beside_is_fill ·
P2Third.lastPar Z = ToldDesc.p14At Z and pieceZeroAt … = pieceOf (heldZero …) …: by unfolding, at
the expected type · the codes: hcs, by substitution (cs' is a letter here).
IS IT EMPTY? H is a law's conclusion: whoever calls this theorem brings it. Nothing on soundness.

-/
import Johnson.LLT25R.LastTop
import Johnson.Desc.ProofFile.Lot.LastChainFour
import Johnson.Desc.Last.ShapeRowZero
import Johnson.Desc.Third.Law.Row0Make

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open LLT25
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)

/-- **row0B from row 0's debt in the form in which the laws rowZeroOwed_… end.** -/
theorem row0B_of_form {Cells Tok P₀ Xi' : Type} (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ) (o :
    SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) (D : WholeD) (G :
          FileDescription Xi') (arr : ℕ → ℕ → ℕ) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
                 N) N c).S₁ → P₀ × First.S) (ms₁ ms₂ : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St →
                 Option Cells) (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N
                 c).XiPub × (FL o mk Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement)
    (bookOf : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links :
    List ModelPart) (X : St → Bool) (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N
          c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option
          Cells) (c₀' : Cells) (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ →
          Prop) (cs' : OnBytes.Codes) (hcs : cs' = (p14At Z).codes) (H : ∀ (ds : List RDT) (back : List
          Fmt.RoundView) (r : Rest (ckP .two) (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber)
                 (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z
                 N) N c).S₃) (Wit Cells Tok MsgT) ds), (∀ a τ w, r.ext a τ w = w) → RowZeroOwed (tiedNumbers N₁
                 Ns) (tiedMeaning get M₁ (meaningSigS cs' G arr (smpSt cs' oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen
                 cs' arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS cs'
                 G (smpSt cs' oNo stSh) ms₂ stOf bookOf Pm₀) (besideL (fillZ (P2Third.lastPar Z) (c2 N).rounds
                 fun q => (get q).2) X) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y
                 ∧ Rc q) (pieceOf (heldZero (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N
                 c).S₁ × St) (Cl := (FL o mk Z (seatK Z N) N c).Cl) (P2Third.lastPar Z)) (D.t₁ + D.t₂) ds back
                 r)) :
    RowZeroOwed (tiedNumbers N₁ Ns) (tiedMeaning get M₁ (meaningSigS (p14At Z).codes G arr (smpSt
    (p14At Z).codes oNo stSh) ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL
    (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G (smpSt (p14At
    Z).codes oNo stSh) ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get
    q).2) (endedX X)) (fun q y => ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y ∧ Rc
    q) (pieceZeroAt (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z
    (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes (smpNamed (p14At Z).codes
    seats) (smpSt (p14At Z).codes oNo stSh) get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns)))) := by
  subst hcs
  exact (beside_is_fill (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2)
      (fun d => (_root_.Desc.K14.ended d).map sharedOfEnd) X) ▸ H _ _ _ (fun _ _ _ => rfl)

end P2Law

#print axioms P2Law.row0B_of_form
