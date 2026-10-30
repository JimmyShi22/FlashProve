-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Six.lean: THE TRACER ON ROW 1.0, LEVEL 6: Left10c's (hnew) FROM Piece.ShownAll (Johnson/Desc/Sound/ShownOfData.lean), which shownOfData | cutShown of that file give at every piece of the maker's cut: what is left is Left10d.
OBJECT: The35.r1_0 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll; the family of members and seats: cs m seat.
  shown_tie    PROVED: the ShownAt of Johnson/Desc/Sound/MsgSig.lean at a member whose seat is at_ k, under that file's SeatFits, gives the tables' ShownAt (Johnson/Desc/Key/KeyTies.lean) at k (the told log-length IS aOf: SeatFits' third clause). KIN: Johnson/RunOne/KeyFillBase.lean has a section «The two ShownAt's»: typed apart; three lines.
  hnew_of      PROVED: ShownAll at a piece with base 0 and the stretch [d₁, d₂] · the stretch sends a tree number 0 · the member's seat is at_ 0 = (0, 0) ⟹ Left10c's hnew (ShownAll reads a piece's base and stretch alone: so it passes from the maker's piece to the kind's own; the strings behind are «behind …» by KeyKeeps.out_behind')
  Left10d      WHAT IS LEFT: as Left10c, with cs · m · fam · fits · i · seatIs · sh · tree · shownAll in the place of hnew
  r1_0_six     PROVED FROM q₁ AND Left10d
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10Five
import Johnson.Desc.Sound.ShownOfData

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

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)

/-- **The two ShownAt's.** -/
theorem shown_tie {XI : Type} (F : FileDescription XI) (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ)
    (hS : Sound.SeatFits F cs m fam) (at_ : Where) (k : ℕ) (i : Fin m.length) (hi : fam i = at_ k) (y : Strs)
    (h : Sound.ShownAt F cs m fam y i) : Key.ShownAt F at_ k y := by
  intro o ho x hx
  obtain ⟨o', n, ho', -, hl, -⟩ := hS i
  rw [hi] at ho'
  have e : o = o' := Option.some.inj (ho.symm.trans ho')
  subst e
  rw [hl] at hx
  have := h x hx
  rw [hi] at this
  exact this

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


/-- **WHAT IS LEFT OF ROW 1.0, (hnew) BROUGHT TO Piece.ShownAll.** -/
structure Left10d where
  d₁ : RDT
  d₂ : RDT
  data : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂]
  entry : d₁.entry = seedEntry (par10 X)
  kind : d₁.kind = .seeds
  rad : ℕ → ℕ
  cond : condPort (par10 X) rad = true
  K : ℕ
  share : shareB K (par10 X) rad = true
  below : belowB K (par10 X) = true
  cap : (rest₁ 0 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates (errPort (par10 X) rad)).ior.imp y τ) = fIn y τ.1
  /-- the family of members and seats, with its test on the plan (Sound.SeatFits) -/
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  /-- the member that sits at the table's seat of message 0 -/
  i : Fin m.length
  seatIs : fam i = at_ 0
  /-- THE DATA's: the stretch sends a tree number 0 -/
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  /-- Piece.ShownAll at the maker's own first piece (shownOfData | cutShown give it at every piece of the maker's cut) -/
  shownAll : (pieceOf (held c₁ : Block (Xi × FirstState) Claim) 0 [d₁, d₂] [] (rest₁ 0 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  sampled : (oneAt X).indexMasks.shape.answers ≠ 0
  lay : ∀ lay, OnBytes.layTrees (oneAt X).codes #[(oneAt X).indexMasks] = some lay → lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0
  seat : at_ 0 = (0, 0)
  cell : CollCell coll
  k₀ : Fin (shapesOf (par10 X)).length
  sampledAt : sampledAt (par10 X) k₀
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = 1 →
      Sealed (par10 X).codes (shapeAt (par10 X) k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val) →
      hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **Behind the kind's own piece every leaf of the seat at_ 0 is shown.** -/
theorem hnew_of (H : Left10d X N P DK c₁ rest₁ B at_ coll) (e : ℕ) (a a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (τ)
    (hx : (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 H.d₁ H.d₂ (par10 X).coordinates e).ior.red.out a τ = some a') :
    Key.ShownAt (Fk X N P) at_ 0 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) := by
  rw [out_behind' (fr₁ (DK.at frS.P.T.a)) _ a a' τ hx]
  exact shown_tie (Fk X N P) H.cs H.m H.fam H.fits at_ 0 H.i H.seatIs _
    (H.shownAll a.2 τ H.i 0 H.sh (by rw [H.seatIs, H.seat]; rfl) H.tree)

def left10c_of (H : Left10d X N P DK c₁ rest₁ B at_ coll) : Left10c X N P DK c₁ rest₁ B at_ R coll :=
  { d₁ := H.d₁, d₂ := H.d₂, data := H.data, entry := H.entry, kind := H.kind, rad := H.rad, cond := H.cond, K := H.K, share := H.share, below := H.below, cap := H.cap
    fOf := H.fOf, fIn := H.fIn, words := H.words
    hnew := fun a τ a' _ hx => hnew_of X N P DK c₁ rest₁ B at_ coll H _ a a' τ hx
    sampled := H.sampled, lay := H.lay, seat := H.seat, cell := H.cell, k₀ := H.k₀, sampledAt := H.sampledAt, tieS := H.tieS }

/-- **THE FIELD r1_0 OF The35, (hnew) BROUGHT TO Piece.ShownAll.** -/
theorem r1_0_six (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10d X N P DK c₁ rest₁ B at_ coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_five X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁ (left10c_of X N P DK c₁ rest₁ B at_ R coll H)

end

end LPFD

#print axioms LPFD.shown_tie
#print axioms LPFD.hnew_of
#print axioms LPFD.r1_0_six
