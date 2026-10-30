-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117Seven.lean: THE KEY FILE's ROW 1.17 AT THE TABLES' ONE READING AS baseK FILLS IT (B := baseK (oneAt X).codes l num at_ decT recOf orc₁): Left117b's (fOf | fIn | words) · (tieS) · (smpOwn) ARE PAID BY CALLS: words_zero (Johnson/RunOne/KeyFillWords.lean) | tieS_fam (through tieS_at, Row10Seven.lean) | smGroupsK (both in Johnson/RunOne/KeyFillSeed.lean), and smpOwn_base (Johnson/RunOne/KeySmpOwn.lean). BY ROWS 1.0 | 1.1's LEVEL 7 (Row11Seven.lean), STEP FOR STEP. What is left is Left117e.
OBJECT: The35.r1_17 at B := baseK … · USER: The21's filler at that reading · LETTERS: X N P · the maker's cut and rests · at_ R coll · bw · ρ · the filling's l num decT recOf orc₁.
  codes17      PROVED by rfl: the place's codes are (oneAt X).codes: SO ROWS 1.0 · 1.1 · 1.17 STAND AT ONE READING B
  Left117e     WHAT IS LEFT: as Left117b, WITHOUT fOf · fIn · words · tieS · smpOwn; WITH: first (the first written round sends a tree) · two | kIs (the place sends two messages; the sampled one is the first) · memberIs | numIs | orcIs (THE TIES AT THE CALL) · arr · the five premises on baseK's family
  r1_17_seven  PROVED
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row117Paid
import Johnson.Top.Fire.Code.Row11Seven

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

open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry Tie)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt smGroupsK)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW)

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
  (bw b₁₇ : Block FirstState Claim) {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)


theorem codes17 (n₁ n₂ : OnBytes.OracleNotice) : (par17 X n₁ n₂).codes = (oneAt X).codes := rfl

/-- **WHAT IS LEFT OF ROW 1.17 AT THE FILLING OF THE READING (baseK).** -/
structure Left117e (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) (d₁ d₂ : RDT) where
  first : 0 < d₁.trees.length
  radW : ℕ → ℕ
  cond : condPort (par17 X Pb.n₁ Pb.n₂) radW = true
  K : ℕ
  share : shareB K (par17 X Pb.n₁ Pb.n₂) radW = true
  below : belowB K (par17 X Pb.n₁ Pb.n₂) = true
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 2
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  shownAll : (pieceOf (held b₁₇ : Block (Xi × FirstState) Claim) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) [d₁, d₂] [] (rest₁ 17 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  base0 : (at_ 0).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17)
  seat2 : at_ 2 = ((oneAt X).ranges.stages.length + 1, 0)
  treeAt : (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) = (oneAt X).ranges.stages.length + 1
  cell : CollCell coll
  same : R.same = fun a b => ρ.val a = ρ.val b
  k₀ : Fin (shapesOf (par17 X Pb.n₁ Pb.n₂)).length
  sampledAt : sampledAt (par17 X Pb.n₁ Pb.n₂) k₀
  /-- PUBLIC: the place sends two messages; the sampled one is the first -/
  two : (shapesOf (par17 X Pb.n₁ Pb.n₂)).length = 2
  kIs : k₀.val = 0
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (shapeAt (par17 X Pb.n₁ Pb.n₂) k₀, radW k₀.val)
  numIs : num j = 2
  orcIs : orc₁ = (plan₁ (oneAt X)).orc
  arr : ArrOk (baseK (Cells := Cells) (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁).h₁ at_ [0, 1, 2]
  /-- THE FIVE PREMISES ON baseK's FAMILY -/
  inj : Function.Injective (seatAt l num at_)
  apart : ShapesApart l
  tie : Tie (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1
  logs : ∀ o, (Fk X N P).oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1
  mains : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1).a = Johnson.Pack.aOf (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1

def left117b_of (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) (d₁ d₂ : RDT)
    (H : Left117e X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁₇ ρ Pb d₁ d₂) :
    Left117b X N P DK c₁ k₁ rest₁ (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R coll b₁₇ ρ Pb d₁ d₂ :=
  { radW := H.radW, cond := H.cond, K := H.K, share := H.share, below := H.below
    fOf := readerOf (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂)) (fun k => H.radW k.val) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) (fun _ => 0) (fun k => k.val)
    fIn := readerIn (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂)) (fun k => H.radW k.val) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) (fun _ => 0) (fun k => k.val) d₁
    words := words_zero (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂)) (fun k => H.radW k.val) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) (fun k => k.val) _ d₁ d₂ _ _ H.first
    cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs, sh := H.sh, tree := H.tree, shownAll := H.shownAll
    base0 := H.base0, seat2 := H.seat2, treeAt := H.treeAt, cell := H.cell, same := H.same
    smpOwn := smpOwn_base _ at_ (oneAt X) H.arr H.orcIs (smGroupsK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁)
    k₀ := H.k₀, sampledAt := H.sampledAt
    tieS := fun a' h3 hS => by
      have hL := H.two
      have hk := H.kIs
      have hidx : a'.1.2.d.st.oracles.size - (shapesOf (par17 X Pb.n₁ Pb.n₂)).length + H.k₀.val = Johnson.RunOne.KeyRows1.wAt (oneAt X) := by omega
      rw [hidx] at hS
      have T := tieS_at (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁ (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a))) H.inj H.apart H.j (Johnson.RunOne.KeyRows1.wAt (oneAt X)) (by rw [H.numIs, H.orcIs]; rfl) H.tie H.logs H.mains
        (shapeAt (par17 X Pb.n₁ Pb.n₂) H.k₀) (H.radW H.k₀.val) H.memberIs a'.1 a'.2
      rw [H.numIs, H.seat2] at T
      rw [H.seat2]
      refine T ?_
      have e : readerOf (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂)) (fun k => H.radW k.val) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) (fun _ => 0) (fun k => k.val) a'.2 H.k₀ =
          symsW (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂) H.k₀) (H.radW H.k₀.val) (wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) ((oneAt X).ranges.stages.length + 1) 0) := by
        have ew : wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) ((cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) + 0) H.k₀.val = wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) ((oneAt X).ranges.stages.length + 1) 0 := by rw [hk, H.treeAt]
        exact congrArg (symsW (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂) H.k₀) (H.radW H.k₀.val)) ew
      rw [← e]
      exact hS }

/-- **THE FIELD r1_17 OF The35 AT THE FILLING OF THE READING (baseK).** -/
theorem r1_17_seven (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁) (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) (hsm : Johnson.RunOne.KeyRows1.wAt (oneAt X) + 1 < noId)
    (HL : ∀ b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ →
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] →
      Left117e X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁₇ ρ Pb d₁ d₂) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 :=
  r1_17_paid X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R coll bw ρ x₀ x₁ hl hw q₁ hs hdata hcap Pb hsm
    fun b₁₇ d₁ d₂ hb hd => left117b_of X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁₇ ρ Pb d₁ d₂ (HL b₁₇ d₁ d₂ hb hd)

end

end LPFD

#print axioms LPFD.r1_17_seven
