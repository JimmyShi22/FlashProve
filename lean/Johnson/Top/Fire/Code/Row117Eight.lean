-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117Eight.lean: THE KEY FILE's ROW 1.17, ONE LEVEL ON: OF Left117e (Row117Seven.lean) FIVE FIELDS ARE PAID FROM Public117 AND THE DATA: two · k₀ · kIs · sampledAt (the place sends two messages; the sampled one is the first: by the two notices) · first (the first written round sends a tree: by the data's own round and «the place has a tree»). What is left is Left117f.
OBJECT: The35.r1_17 at B := baseK … · USER: The21's filler at that reading · LETTERS: as Row117Seven.lean's.
  two17 | sampled17   PROVED · k17: a definition
  data17_more   PROVED: data17_of, and: the first round's data hold as many trees as the place has
  Left117f      WHAT IS LEFT
  r1_17_eight   PROVED
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row117Seven

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


theorem two17 (n₁ n₂ : OnBytes.OracleNotice) : (shapesOf (par17 X n₁ n₂)).length = 2 := rfl

/-- The first of the place's two messages. -/
def k17 (n₁ n₂ : OnBytes.OracleNotice) : Fin (shapesOf (par17 X n₁ n₂)).length := ⟨0, by rw [two17]; decide⟩

theorem shape17 (n₁ n₂ : OnBytes.OracleNotice) : shapeAt (par17 X n₁ n₂) (k17 X n₁ n₂) = n₁.shape := rfl

theorem sampled17 (n₁ n₂ : OnBytes.OracleNotice) (h : n₁.shape.answers ≠ 0) : sampledAt (par17 X n₁ n₂) (k17 X n₁ n₂) := h

/-- **The stretch at block 17, with the trees' number.** -/
theorem data17_more (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (n₁ n₂ : OnBytes.OracleNotice) (hm : linMessageW (oneAt X).lin = some #[n₁, n₂]) (b₁₇ : Block FirstState Claim) (d₁ d₂ : RDT) (hb : (c₁ :: k₁)[17]? = some b₁₇)
    (hd : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂]) :
    d₁.trees.length = (par17 X n₁ n₂).trees.length := by
  have hlong := long17 X N P c₁ k₁ bw x₀ x₁ hl hw q₁
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal (Fk X N P) hs c₁ k₁ q₁) 17 hlong b₁₇ hb
  rw [rounds17 X N P c₁ k₁ bw b₁₇ x₀ x₁ hl hw q₁ hb n₁ n₂ hm, ← cutDs_held (Pb := (Fk X N P).XiPub) k₁ 17 _ c₁, hd] at has
  have has' : List.Forall₂ RoundAsG [d₁, d₂] [{ entry := seedEntry (par17 X n₁ n₂) }, { entry := K1.answerEntry (par17 X n₁ n₂) }] := has
  obtain ⟨h1, -⟩ := List.forall₂_cons.1 has'
  exact h1.2.2.2.1

/-- **WHAT IS LEFT OF ROW 1.17.** -/
structure Left117f (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) (d₁ d₂ : RDT) where
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
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (Pb.n₁.shape, radW 0)
  numIs : num j = 2
  orcIs : orc₁ = (plan₁ (oneAt X)).orc
  arr : ArrOk (baseK (Cells := Cells) (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁).h₁ at_ [0, 1, 2]
  /-- THE FIVE PREMISES ON baseK's FAMILY -/
  inj : Function.Injective (seatAt l num at_)
  apart : ShapesApart l
  tie : Tie (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1
  logs : ∀ o, (Fk X N P).oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1
  mains : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1).a = Johnson.Pack.aOf (par17 X Pb.n₁ Pb.n₂).codes (l.get j).1

/-- **THE FIELD r1_17 OF The35 AT THE FILLING OF THE READING (baseK), FIVE FIELDS FEWER.** htrees: PUBLIC: the place has a tree. -/
theorem r1_17_eight (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁) (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) (hsm : Johnson.RunOne.KeyRows1.wAt (oneAt X) + 1 < noId)
    (htrees : 0 < (par17 X Pb.n₁ Pb.n₂).trees.length)
    (HL : ∀ b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ →
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] →
      Left117f X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁₇ ρ Pb d₁ d₂) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK (par17 X Pb.n₁ Pb.n₂).codes l num at_ decT recOf orc₁) at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 :=
  r1_17_seven X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd at_ coll R l num decT recOf orc₁ bw ρ x₀ x₁ hl hw q₁ hs hdata hcap Pb hsm
    fun b₁₇ d₁ d₂ hb hd =>
      let H := HL b₁₇ d₁ d₂ hb hd
      { first := by rw [data17_more X N P DK c₁ k₁ bw x₀ x₁ hl hw q₁ hs hdata Pb.n₁ Pb.n₂ Pb.two b₁₇ d₁ d₂ hb hd]; exact htrees
        radW := H.radW, cond := H.cond, K := H.K, share := H.share, below := H.below, cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs
        sh := H.sh, tree := H.tree, shownAll := H.shownAll, base0 := H.base0, seat2 := H.seat2, treeAt := H.treeAt, cell := H.cell, same := H.same
        k₀ := k17 X Pb.n₁ Pb.n₂, sampledAt := sampled17 X Pb.n₁ Pb.n₂ Pb.sampled, two := two17 X Pb.n₁ Pb.n₂, kIs := rfl
        j := H.j, memberIs := H.memberIs, numIs := H.numIs, orcIs := H.orcIs, arr := H.arr, inj := H.inj, apart := H.apart, tie := H.tie, logs := H.logs, mains := H.mains }

end

end LPFD

#print axioms LPFD.data17_more
#print axioms LPFD.r1_17_eight
