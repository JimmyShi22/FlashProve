-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row11Seven.lean: THE KEY FILE's ROW 1.1 AT THE TABLES' ONE READING AS baseK FILLS IT (B := baseK (par11 X).codes l num at_ decT recOf orc₁): Left11's (fOf | fIn | words) · (tieS) · (smpOwn) ARE PAID: words_zero | tieS_fam (through tieS_at, Row10Seven.lean) | smGroupsK, and smpOwn_base (RunOne/KeySmpOwn.lean). By row 1.0's level 7. What is left is Left11e.
OBJECT: The35.r1_1 at B := baseK … · USER: The21's filler at that reading · LETTERS: X N P · the maker's cut and rests · at_ R coll · b₁ · ρ · baseK's l num decT recOf orc₁.
  Left11e      WHAT IS LEFT: as Left11, WITHOUT fOf · fIn · words · tieS · smpOwn; WITH: first · two (the place sends two messages) · kIs (the sampled one is the first) · memberIs | numIs | orcIs (THE TIES AT THE CALL) · arr (ArrOk at 0 | 1 | 2) · the five premises on baseK's family
  r1_1_seven   PROVED
  codes10 | codes11   PROVED by rfl: both places' codes are (oneAt X).codes: SO THE TWO ROWS STAND AT ONE READING B (The35 runs over one)
THE READER's TENANT: the place's message k sits at tenant k of the stretch's one tree (the layout's parts 0 | 1: Public11.lay): the reader is laid at t := fun k => k.val.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row11
import Johnson.Top.Fire.Code.Row10Seven
import Johnson.RunOne.KeySmpOwn

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
  (b₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)

/-- **THE TWO ROWS' READINGS ARE ONE**: both places' codes are the plan's own: so baseK (par10 X).codes … and baseK (par11 X).codes … are one term. -/
theorem codes10 : (par10 X).codes = (oneAt X).codes := rfl
theorem codes11 : (par11 X).codes = (oneAt X).codes := rfl

/-- **WHAT IS LEFT OF ROW 1.1 AT baseK's FILLING OF THE READING.** -/
structure Left11e where
  d₁ : RDT
  d₂ : RDT
  data : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 1 = [d₁, d₂]
  put : cutPut [sealRound] (k₁.map (held (P := (Fk X N P).XiPub))) 1 = []
  baseIs : cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 1 = 1
  entry : d₁.entry = seedEntry (par11 X)
  kind : d₁.kind = .seeds
  first : 0 < d₁.trees.length
  rad : ℕ → ℕ
  cond : condPort (par11 X) rad = true
  K : ℕ
  share : shareB K (par11 X) rad = true
  below : belowB K (par11 X) = true
  cap : (rest₁ 1 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 1
  sh : _root_.Fmt.Shape
  tree : treeShT [d₁, d₂] 0 = some sh
  shownAll : (pieceOf (held b₁ : Block (Xi × FirstState) Claim) 1 [d₁, d₂] [] (rest₁ 1 [d₁, d₂])).ShownAll (Fk X N P) cs m fam
  pub : Public11 (oneAt X) pieces (g11 X)
  seat0 : at_ 0 = (0, 0)
  seat1 : at_ 1 = (1, 0)
  cell : CollCell coll
  same : R.same = fun a b => ρ.val a = ρ.val b
  k₀ : Fin (shapesOf (par11 X)).length
  sampledAt : sampledAt (par11 X) k₀
  /-- PUBLIC: the place sends two messages; the sampled one is the first -/
  two : (shapesOf (par11 X)).length = 2
  kIs : k₀.val = 0
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (shapeAt (par11 X) k₀, rad k₀.val)
  numIs : num j = 1
  orcIs : orc₁ = (plan₁ (oneAt X)).orc
  arr : ArrOk (baseK (Cells := Cells) (par11 X).codes l num at_ decT recOf orc₁).h₁ at_ [0, 1, 2]
  /-- THE FIVE PREMISES ON baseK's FAMILY -/
  inj : Function.Injective (seatAt l num at_)
  apart : ShapesApart l
  tie : Tie (par11 X).codes (l.get j).1
  logs : ∀ o, (Fk X N P).oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf (par11 X).codes (l.get j).1
  mains : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain (par11 X).codes (l.get j).1).a = Johnson.Pack.aOf (par11 X).codes (l.get j).1

def left11_of (H : Left11e X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁ ρ) :
    Left11 X N P DK c₁ k₁ rest₁ (baseK (par11 X).codes l num at_ decT recOf orc₁) at_ R coll b₁ ρ :=
  { d₁ := H.d₁, d₂ := H.d₂, data := H.data, put := H.put, baseIs := H.baseIs, entry := H.entry, kind := H.kind, rad := H.rad, cond := H.cond
    K := H.K, share := H.share, below := H.below, cap := H.cap
    fOf := readerOf (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par11 X).codes (shapeAt (par11 X)) (fun k => H.rad k.val) 1 (fun _ => 0) (fun k => k.val)
    fIn := readerIn (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par11 X).codes (shapeAt (par11 X)) (fun k => H.rad k.val) 1 (fun _ => 0) (fun k => k.val) H.d₁
    words := words_zero (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par11 X).codes (shapeAt (par11 X)) (fun k => H.rad k.val) 1 (fun k => k.val) _ H.d₁ H.d₂ _ _ H.first
    cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs, sh := H.sh, tree := H.tree, shownAll := H.shownAll
    pub := H.pub, seat0 := H.seat0, seat1 := H.seat1, cell := H.cell, same := H.same
    smpOwn := smpOwn_base _ at_ (oneAt X) H.arr H.orcIs (smGroupsK (par11 X).codes l num at_ decT recOf orc₁)
    k₀ := H.k₀, sampledAt := H.sampledAt
    tieS := fun a' h3 hS => by
      have hL := H.two
      have hk := H.kIs
      have hidx : a'.1.2.d.st.oracles.size - (shapesOf (par11 X)).length + H.k₀.val = 1 := by omega
      rw [hidx] at hS
      have T := tieS_at (par11 X).codes l num at_ decT recOf orc₁ (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a))) H.inj H.apart H.j 1 (by rw [H.numIs, H.orcIs]; rfl) H.tie H.logs H.mains
        (shapeAt (par11 X) H.k₀) (H.rad H.k₀.val) H.memberIs a'.1 a'.2
      rw [H.numIs, H.seat1] at T
      rw [H.seat1]
      refine T ?_
      have e : readerOf (Fk X N P) (fr₁ (DK.at frS.P.T.a)) (par11 X).codes (shapeAt (par11 X)) (fun k => H.rad k.val) 1 (fun _ => 0) (fun k => k.val) a'.2 H.k₀ =
          symsW (par11 X).codes (shapeAt (par11 X) H.k₀) (H.rad H.k₀.val) (wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) 1 0) := by
        have ew : wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) (1 + 0) H.k₀.val = wordOf (Fk X N P) (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2) 1 0 := by rw [hk]
        exact congrArg (symsW (par11 X).codes (shapeAt (par11 X) H.k₀) (H.rad H.k₀.val)) ew
      rw [← e]
      exact hS }

/-- **THE FIELD r1_1 OF The35 AT baseK's FILLING OF THE READING.** -/
theorem r1_1_seven (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) (H : Left11e X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁ ρ) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK (par11 X).codes l num at_ decT recOf orc₁) at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK (par11 X).codes l num at_ decT recOf orc₁) at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1 :=
  r1_1_at X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (baseK (par11 X).codes l num at_ decT recOf orc₁) at_ R coll b₁ ρ q₁ hb (left11_of X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁ ρ H)

end

end LPFD

#print axioms LPFD.r1_1_seven
