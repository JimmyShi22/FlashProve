-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10.lean: A TRACER: THE KEY FILE's ROW 1.0 (idx.1.send: the first of the 21 rows that draw) TAKEN THE WHOLE ROAD UP TO THE FIELD r1_0 OF The35 (Johnson/Top/Fire/Code/The35.lean). EVERY UNPAID THING IS A NAMED PREMISE, GATHERED IN ONE STRUCTURE: Owed10.
OBJECT: The35.r1_0: KeepsAt On₁' Cl₁ ‹the maker's own row of chain 1› 0 · USER: the35_of_21's caller (The21.r1_0 is one of its 21 fields) · LETTERS: X N P · the maker's cut and rests · B at_ R coll.
THE ROAD: a kind's GoodIn (Johnson/Desc/Sound/GoodIn.lean) at a piece of the description's own first block, held, at a rest x of the kind's own ⟹ [sendRow_keeps_new (Johnson/Desc/Key/KeySendRow.lean), through KeyRow10.keeps_send0] Keeps at x's errors ⟹ [keepsAt_of_law₁ (PieceSame.lean): keeps_same: the errors raised to the maker's rest's] KeepsAt On₁ Cl₁ row 0 ⟹ [KeepsAt.reached (Reached.lean) · rowBlocksF₁ (RowsWoven.lean)] the history woven in: KeepsAt On₁' Cl₁ row 0.
  Owed10    WHAT IS OWED, FIELD BY FIELD, AT EVERY base ds back AT WHICH THE MAKER's ROW HOLDS A PIECE: recStays · New | hnew · yes · x | le · Sl Ra Rb | good · tie
  r1_0_of   PROVED FROM Owed10 AND q₁ (the description's first chain's flat list is the maker's c₁ :: k₁)
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.The35
import Johnson.Top.Fire.Code.RowLaw
import Johnson.RunOne.KeyRow10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open Johnson.RunOne.KeyRows1 (RecStays SendYes₀ keeps_send0 held_of)

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


/-- **WHAT ROW 1.0 OWES**, at the description's own first block b. -/
structure Owed10 (b : Block FirstState Claim) : Prop where
  /-- A CONDITION ON THE READING: the stored table's record is read off the instance alone -/
  recStays : RecStays B.h₁
  /-- at every place at which the maker may lay the piece: -/
  each : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
    ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[0]? = some (pieceOf (held b) base ds back (rest₁ 0 ds)) →
    ∃ (x : Rest (ckP .two) (fr₁ (DK.at frS.P.T.a)) (Xi × FirstState) W ds) (New : Strs → Prop)
      (Sl : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Prop) (Ra Rb : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → W → Prop),
      -- (le) THE KIND's OWN ERRORS LIE BELOW THE MAKER's REST's (keeps_same_cap, PieceSame.lean, pays it from Err.Below … 2^-128 where the maker's rest is the cap)
      Err.le x.err (rest₁ 0 ds).err ∧
      -- (hnew) A FACT OF THE PIECE ON THE STRINGS BEHIND (there: every leaf of the new tenant's word is shown)
      (∀ a τ a', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a → (pieceOf (held b) base ds back x).ior.red.out a τ = some a' → New (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)) ∧
      -- (yes) WHAT THE BLOCK's YES GIVES OF THE RECORD: the book-keeping and the promise's last letter at border 1
      SendYes₀ (Fk X N P) B.h₁ at_ (oneAt X) R coll New b ∧
      -- (good) THE SENDING KIND's OWN LAW, AT THIS PIECE, FROM THE TABLES' OWN PROMISE AT BORDER 0
      (pieceOf (held b) base ds back x).GoodIn (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0) Sl Ra Rb ∧
      -- (tie) «sealed» GIVES THE SAMPLE AND NO COLLISION AT THE TABLE's SEAT (sealed_gives_lift, Johnson/Desc/Key/KeySealTie.lean, pays it from SealReads at the letter G)
      (∀ a', Sl a' → hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2))

/-- **THE FIELD r1_0 OF The35, FROM WHAT ROW 1.0 OWES.** -/
theorem r1_0_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Owed10 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll c₁) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 :=
  KeepsAt.reached _ _ (rowBlocksF₁ q₁ 0)
    (keepsAt_of_law₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 0 fun b base ds back hb hp => by
        have eb : c₁ = b := Option.some.inj hb
        subst eb
        obtain ⟨x, New, Sl, Ra, Rb, hle, hnew, yes, good, tie⟩ := H.each base ds back hp
        exact ⟨x, keeps_send0 (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll (pieceOf (held c₁) base ds back x) c₁
          (held_of _ _ c₁ rfl) rfl H.recStays New hnew yes Sl Ra Rb good tie, hle⟩)

end

end LPFD

#print axioms LPFD.r1_0_of
