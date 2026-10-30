-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117Paid.lean: THE KEY FILE's ROW 1.17 (w.1.send): WHAT OF Row117.lean's PREMISES IS A THEOREM AT EVERY X N P, AND THE FIT.
  long17          PAID: 17 < k₁.length (19 blocks: flat_length, Johnson/RunOne/KeyTenAt.lean)
  data17_of       PAID, NO TEST, NO EVALUATION: the maker's stretch at block 17 is two rounds' data [d₁, d₂]; the first bears the place's own entry of the seeds and the kind «seeds»: by stretch_of_data₁ (RowStretch.lean, over roundsOfData) · rounds17 · seed_kind
  Left117b        WHAT IS LEFT: Left117 without entry | kind | cap
  r1_17_paid      THE FIELD r1_17 FROM: q₁ · hl · hw (The35's own) · sealLast · hdata (The21AtSeat hands both) · AtCap rest₁ (capRest, KeyPublicAtSeat.lean: rfl) · Left117b at the data's own two rounds
  the21_with_17   THE FIT: r1_17_paid's conclusion IS The21's field r1_17, by Lean's own check of types
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row117
import Johnson.Top.Fire.Code.RowStretch
import Johnson.Desc.Sound.BoundsAtCap

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

open Johnson.RunOne.KeyRows1 (RecStays Public117 SmpOwn parW' wAt)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece send_goodIn Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry seeds_one seed_draws)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB below_send)

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



variable (bw b₁₇ : Block FirstState Claim)

theorem long17 (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : 17 < k₁.length := by
  have h : (Fk X N P).first.blocksInOrder.length = 19 := Johnson.RunOne.KeyRows1.flat_length (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw
  rw [q₁] at h
  simp only [List.length_cons] at h
  omega

/-- **The stretch at block 17, from the description's own data.** -/
theorem data17_of (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (n₁ n₂ : OnBytes.OracleNotice) (hm : linMessageW (oneAt X).lin = some #[n₁, n₂]) :
    ∃ b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ ∧
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] ∧
      d₁.entry = seedEntry (par17 X n₁ n₂) ∧ d₁.kind = .seeds := by
  have hlong := long17 X N P c₁ k₁ bw x₀ x₁ hl hw q₁
  obtain ⟨bn, hbn⟩ : ∃ bn, (c₁ :: k₁)[17]? = some bn := ⟨_, List.getElem?_eq_getElem (by simp only [List.length_cons]; omega)⟩
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal (Fk X N P) hs c₁ k₁ q₁) 17 hlong bn hbn
  rw [rounds17 X N P c₁ k₁ bw bn x₀ x₁ hl hw q₁ hbn n₁ n₂ hm] at has
  have has' : List.Forall₂ RoundAsG (cutDs (DK.at frS.P.T.a).ds₁ c₁ k₁ 17) [{ entry := seedEntry (par17 X n₁ n₂) }, { entry := K1.answerEntry (par17 X n₁ n₂) }] := has
  obtain ⟨d₁, l₁, h1, t1, e1⟩ := List.forall₂_cons_right_iff.1 has'
  obtain ⟨d₂, l₂, _, t2, e2⟩ := List.forall₂_cons_right_iff.1 t1
  obtain rfl := List.forall₂_nil_right_iff.1 t2
  subst e2
  refine ⟨bn, d₁, d₂, hbn, (cutDs_held k₁ 17 _ c₁).trans e1, h1.1, ?_⟩
  exact (Option.some.inj ((Johnson.RunOne.KeySendGood.seed_kind (par17 X n₁ n₂)).symm.trans h1.2.1)).symm

variable {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)

/-- **WHAT IS LEFT OF ROW 1.17**, the public premises on the plan apart, at the block and the two rounds' data that the maker lays. -/
structure Left117b (Pb : Public117 (oneAt X) pieces (g17 X)) (d₁ d₂ : RDT) where
  radW : ℕ → ℕ
  cond : condPort (par17 X Pb.n₁ Pb.n₂) radW = true
  K : ℕ
  share : shareB K (par17 X Pb.n₁ Pb.n₂) radW = true
  below : belowB K (par17 X Pb.n₁ Pb.n₂) = true
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂) k) (radW k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂) k) (radW k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held b₁₇ : Block (Xi × FirstState) Claim) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17) d₁ d₂ (par17 X Pb.n₁ Pb.n₂).coordinates (errPort (par17 X Pb.n₁ Pb.n₂) radW)).ior.imp y τ) = fIn y τ.1
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
  smpOwn : SmpOwn B.h₁ at_ (oneAt X)
  k₀ : Fin (shapesOf (par17 X Pb.n₁ Pb.n₂)).length
  sampledAt : sampledAt (par17 X Pb.n₁ Pb.n₂) k₀
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = wAt (oneAt X) + 2 →
      Sealed (par17 X Pb.n₁ Pb.n₂).codes (shapeAt (par17 X Pb.n₁ Pb.n₂) k₀) (radW k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par17 X Pb.n₁ Pb.n₂)).length + k₀.val) →
      hasSmp B.h₁ (at_ 2).1 (at_ 2).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 2).1 (at_ 2).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **THE FIELD r1_17, WITH THE DATA's FOUR AND THE CAP PAID.** -/
theorem r1_17_paid (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁) (Pb : Public117 (oneAt X) pieces (g17 X)) (hsm : wAt (oneAt X) + 1 < noId)
    (HL : ∀ b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ →
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] →
      Left117b X N P DK c₁ k₁ rest₁ B at_ R coll b₁₇ ρ Pb d₁ d₂) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 := by
  obtain ⟨b₁₇, d₁, d₂, hb, hd, he, hk⟩ := data17_of X N P DK c₁ k₁ bw x₀ x₁ hl hw q₁ hs hdata Pb.n₁ Pb.n₂ Pb.two
  have H := HL b₁₇ d₁ d₂ hb hd
  exact r1_17_at X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll bw b₁₇ ρ x₀ x₁ hl hw q₁ hb d₁ d₂ hd
    (cutPut_inner _ _ 17 (by simpa using long17 X N P c₁ k₁ bw x₀ x₁ hl hw q₁))
    { pub := Pb, small := hsm, entry := he, kind := hk, radW := H.radW, cond := H.cond, K := H.K, share := H.share, below := H.below, cap := hcap 17 [d₁, d₂]
      fOf := H.fOf, fIn := H.fIn, words := H.words, cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs, sh := H.sh, tree := H.tree
      shownAll := H.shownAll, base0 := H.base0, seat2 := H.seat2, treeAt := H.treeAt, cell := H.cell, same := H.same, smpOwn := H.smpOwn, k₀ := H.k₀, sampledAt := H.sampledAt, tieS := H.tieS }

/-- **THE FIT**: by Lean's own check of types. -/
theorem the21_with_17 (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁) (Pb : Public117 (oneAt X) pieces (g17 X)) (hsm : wAt (oneAt X) + 1 < noId)
    (HL : ∀ b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ →
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] →
      Left117b X N P DK c₁ k₁ rest₁ B at_ R coll b₁₇ ρ Pb d₁ d₂)
    (T : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  { T with r1_17 := r1_17_paid X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll bw ρ x₀ x₁ hl hw q₁ hs hdata hcap Pb hsm HL }

end

end LPFD

#print axioms LPFD.r1_17_paid
#print axioms LPFD.the21_with_17
#print axioms LPFD.long17
#print axioms LPFD.data17_of
