-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Seven.lean: THE TRACER ON ROW 1.0, LEVEL 7: AT THE TABLES' ONE READING AS baseK FILLS IT (B := baseK (par10 X).codes l num at_ decT recOf orc₁: RunOne/KeyFillSeed.lean): Left10d's (fOf | fIn | words) AND (tieS) ARE PAID BY words_zero (RunOne/KeyFillWords.lean) AND tieS_fam (KeyFillSeed.lean), AT ONE READER: fOf := readerOf := symsW ∘ wordOf ∘ strsOf. What is left is Left10e.
OBJECT: The35.r1_0 at B := baseK … · USER: The21's filler at that reading · LETTERS: X N P · the maker's cut and rests · at_ R coll · baseK's l num decT recOf orc₁.
  len10        PROVED by rfl: the first place sends one message
  tieS_at      PROVED: tieS_fam with the member's shape and radius named (l.get i = (s, e)): so that no cast is wanted at the call
  Left10e      WHAT IS LEFT: as Left10d, WITHOUT fOf · fIn · words · tieS; WITH: first (the first written round sends a tree) · THE FOUR TIES AT THE CALL: the codes are the place's (by the choice of cs) · memberIs : l.get j = (the place's shape at k₀, rad k₀) [SHAPE AND RADIUS] · numIs : num j = 0 · orcIs : orc₁ 0 = some 0 [THE INDEX] · and the five premises on baseK's family: inj · apart · tie · logs · mains
  left10d_of' | r1_0_seven   PROVED
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10Six
import Johnson.RunOne.KeyFillWords

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

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry Tie)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW)

/-- tieS_fam, the member's shape and radius named. -/
theorem tieS_at {Cells Rec XI Y' : Type} (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ) (F : FileDescription XI) (str : Y' → Strs)
    (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (j : Fin l.length) (o₀ : ℕ) (ho : orc₁ (num j) = some o₀) (hT : Tie cs (l.get j).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf cs (l.get j).1)
    (hm : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain cs (l.get j).1).a = Johnson.Pack.aOf cs (l.get j).1)
    (s : OnBytes.OracleShape) (e : ℕ) (hl : l.get j = (s, e)) (a : Xi × FirstState) (y : Y')
    (h : Sealed cs s e (symsW cs s e (wordOf F (str y) (at_ (num j)).1 (at_ (num j)).2)) a.2.d.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num j)).1 (at_ (num j)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₁ (at_ (num j)).1 (at_ (num j)).2 a (str y) := by
  have H := tieS_fam cs l num at_ decT recOf orc₁ F str hinj hap j o₀ ho hT hlog hm a y
  rw [hl] at H
  exact H h

section
variable {Cells Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
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
    (at_ : Where) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


variable (R : KRead Cells Fill.Tab) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

theorem len10 : (shapesOf (par10 X)).length = 1 := rfl

/-- **WHAT IS LEFT OF ROW 1.0 AT baseK's FILLING OF THE READING.** -/
structure Left10e where
  d₁ : RDT
  d₂ : RDT
  data : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂]
  entry : d₁.entry = seedEntry (par10 X)
  kind : d₁.kind = .seeds
  /-- PUBLIC, ON THE DATA: the first written round sends a tree -/
  first : 0 < d₁.trees.length
  rad : ℕ → ℕ
  cond : condPort (par10 X) rad = true
  K : ℕ
  share : shareB K (par10 X) rad = true
  below : belowB K (par10 X) = true
  cap : (rest₁ 0 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 0
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  shownAll : (pieceOf (held c₁ : Block (Xi × FirstState) Claim) 0 [d₁, d₂] [] (rest₁ 0 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  sampled : (oneAt X).indexMasks.shape.answers ≠ 0
  lay : ∀ lay, OnBytes.layTrees (oneAt X).codes #[(oneAt X).indexMasks] = some lay → lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0
  seat : at_ 0 = (0, 0)
  cell : CollCell coll
  k₀ : Fin (shapesOf (par10 X)).length
  sampledAt : sampledAt (par10 X) k₀
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (shapeAt (par10 X) k₀, rad k₀.val)
  numIs : num j = 0
  orcIs : orc₁ 0 = some 0
  /-- THE FIVE PREMISES ON baseK's FAMILY -/
  inj : Function.Injective (seatAt l num at_)
  apart : ShapesApart l
  tie : Tie (par10 X).codes (l.get j).1
  logs : ∀ o, (Fk X N P).oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf (par10 X).codes (l.get j).1
  mains : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain (par10 X).codes (l.get j).1).a = Johnson.Pack.aOf (par10 X).codes (l.get j).1

def left10d_of' (H : Left10e X N P DK c₁ rest₁ at_ coll l num orc₁) :
    Left10d X N P DK c₁ rest₁ (baseK (par10 X).codes l num at_ decT recOf orc₁) at_ coll :=
  { d₁ := H.d₁, d₂ := H.d₂, data := H.data, entry := H.entry, kind := H.kind, rad := H.rad, cond := H.cond, K := H.K, share := H.share, below := H.below, cap := H.cap
    fOf := readerOf (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par10 X).codes (shapeAt (par10 X)) (fun k => H.rad k.val) 0 (fun _ => 0) (fun _ => 0)
    fIn := readerIn (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par10 X).codes (shapeAt (par10 X)) (fun k => H.rad k.val) 0 (fun _ => 0) (fun _ => 0) H.d₁
    words := words_zero (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par10 X).codes (shapeAt (par10 X)) (fun k => H.rad k.val) 0 (fun _ => 0) _ H.d₁ H.d₂ _ _ H.first
    cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs, sh := H.sh, tree := H.tree, shownAll := H.shownAll
    sampled := H.sampled, lay := H.lay, seat := H.seat, cell := H.cell, k₀ := H.k₀, sampledAt := H.sampledAt
    tieS := fun a' h1 hS => by
      have hlt : H.k₀.val < 1 := H.k₀.isLt
      have hL := len10 X
      have hidx : a'.1.2.d.st.oracles.size - (shapesOf (par10 X)).length + H.k₀.val = 0 := by omega
      rw [hidx] at hS
      have T := tieS_at (par10 X).codes l num at_ decT recOf orc₁ (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a))) H.inj H.apart H.j 0 (by rw [H.numIs]; exact H.orcIs) H.tie H.logs H.mains
        (shapeAt (par10 X) H.k₀) (H.rad H.k₀.val) H.memberIs a'.1 a'.2
      rw [H.numIs, H.seat] at T
      rw [H.seat]
      exact T hS }

/-- **THE FIELD r1_0 OF The35 AT baseK's FILLING OF THE READING: «words» AND «tieS» PAID, AT ONE READER.** -/
theorem r1_0_seven (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10e X N P DK c₁ rest₁ at_ coll l num orc₁) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK (par10 X).codes l num at_ decT recOf orc₁) at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK (par10 X).codes l num at_ decT recOf orc₁) at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_six X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (baseK (par10 X).codes l num at_ decT recOf orc₁) at_ R coll q₁ (left10d_of' X N P DK c₁ rest₁ at_ coll l num decT recOf orc₁ H)

end

end LPFD

#print axioms LPFD.tieS_at
#print axioms LPFD.r1_0_seven
