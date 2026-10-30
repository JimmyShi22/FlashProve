-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Eight.lean (cond · sampled · lay · the two blocksOk are
  cond10_in_scope · public10_in_scope · first_blocksOk | shared_blocksOk, called): THE KEY
  FILE's ROW 1.0, LEVEL 8: IN THE GOALS' SCOPE, OVER LEVEL 7 (Row10Seven.lean, no byte
  turned): EVERY PUBLIC PREMISE OF Left10e FOR WHICH A PAYER LIES IS PAID BY A CALL. What is left is
  Left10f.
OBJECT: The35.r1_0 at B := baseK csKey l num at_ decT recOf orc₁ · USER: The21AtBase's
  filler · LETTERS: level 7's; the scope's Zp · X₀ · cfg · m. R IS A LETTER HERE (at row 1.1's level
  8 it is fixed).
  data10_of    PAID: the maker's stretch at block 0 is two rounds' data, each standing in RoundAsG
    to the place's own declared round: stretch_of_data₁ (over roundsOfData) ·
    last_of_seal · first_is | second_is · rounds_idx
  shown10_of   PAID: shownAll: cutShown at the maker's own first piece, with
    oraclesAreOk · shape_own₁ · sentFit_of_planOk
  Left10f      WHAT IS LEFT: Sound.SeatFits and its seat (cs m fam fits i seatIs) · seat · cell
    · THE TIES AT THE CALL: j · memberIs (l.get j = (shIdx, 6130): closed) · numIs · orcIs ·
    the five premises on baseK's family, at csKey
  r1_0_eight   PROVED: from q₁ · the five in scope · hdata · AtCap rest₁ · Left10f
  member10_six the tie memberIs AT six, j := 0: by rfl
STRUCK AGAINST Left10e: d₁ d₂ data entry kind first · rad cond K share below (
  asks_in_scope; cond10_in_scope) · cap (AtCap rest₁: the library's name; capRest is an
  instance by rfl) · sh tree (treeShT_some_of_lt) · shownAll · sampled lay (
  public10_in_scope) · k₀ sampledAt.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowScope

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
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
    seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt
    errPort seedMaps seedEntry Tie planOkOwn)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW six)
open Johnson.RunOne.KeySendGood (SendAsks asks_in_scope cond_of parIdx parMsg fullIdx fullMsg idx_at
    msg_at idx_pays msg_pays pays_bare rounds_idx rounds_msg seed_kind)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Lk6.AtPlan (keyFull)

section
variable {Cells Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N
          P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N
          P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N
          P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (at_ : Where) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

variable (R : KRead Cells Fill.Tab) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ →
      Option ℕ)

/-- **The stretch at block 0, from the description's own data.** -/
theorem data10_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata :
             (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    ∃ d₁ d₂, (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂] ∧ RoundAsG d₁
        { entry := seedEntry (par10 X) } ∧ RoundAsG d₂ { entry := K1.answerEntry (par10 X) } := by
  obtain ⟨c, l', hk⟩ := second_is X N P c₁ k₁ q₁
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal
      (Fk X N P) hs c₁ k₁ q₁) 0 (by rw [hk]; exact Nat.succ_pos _) c₁ rfl
  have e0 : cutDs (DK.at frS.P.T.a).ds₁ c₁ k₁ 0 = (DK.at frS.P.T.a).ds₁.take c₁.rounds.length :=
      by rw [hk]; rfl
  have hr : c₁.rounds = K1.rounds (par10 X) := by rw [first_is X N P c₁ k₁ q₁]; exact rounds_idx X
  rw [e0] at has
  have has' : List.Forall₂ RoundAsG ((DK.at frS.P.T.a).ds₁.take c₁.rounds.length)
      [{ entry := seedEntry (par10 X) }, { entry := K1.answerEntry (par10 X) }] := hr ▸ has
  obtain ⟨d₁, l₁, h1, t1, e1⟩ := List.forall₂_cons_right_iff.1 has'
  obtain ⟨d₂, l₂, h2, t2, e2⟩ := List.forall₂_cons_right_iff.1 t1
  obtain rfl := List.forall₂_nil_right_iff.1 t2
  subst e2
  exact ⟨d₁, d₂, e1, h1, h2⟩

/-- **shownAll at the maker's first piece.** -/
theorem shown10_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hp : (Fk X N P).planOk = true) (hdata :
             (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ) (fits :
        Sound.SeatFits (Fk X N P) cs m fam)
    (ds' : List RDT) (e : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = ds') :
    (pieceOf (held c₁ : Block (Xi × FirstState) Claim) 0 ds' [] (rest₁ 0 ds')).ShownAll (Fk X N P)
        cs m fam := by
  obtain ⟨c, l', hk⟩ := second_is X N P c₁ k₁ q₁
  subst e
  have b1 := first_blocksOk X N P hp
  have b2 := shared_blocksOk X N P hp
  exact cutShown (ckP .two) _ _ _ _ rest₁ [] (DK.at frS.P.T.a) ((c :: l').map held) (held c₁) 0 0
      (DK.at frS.P.T.a).ds₁ rfl (shape_own₁ _) _ (Fk X N P) cs m fam fits
    (oraclesAreOk _ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata (sentFit_of_planOk _ hp) b1 b2) _
        List.mem_cons_self

/-- **WHAT IS LEFT OF ROW 1.0 IN SCOPE.** -/
structure Left10f where
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 0
  seat : at_ 0 = (0, 0)
  cell : CollCell coll
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (Johnson.Top.H.shIdx, 6130)
  numIs : num j = 0
  orcIs : orc₁ 0 = some 0
  /-- THE FIVE PREMISES ON baseK's FAMILY, AT THE LIBRARY's TYPED CODES -/
  inj : Function.Injective (seatAt l num at_)
  apart : ShapesApart l
  tie : Tie Johnson.Top.H.csKey (l.get j).1
  logs : ∀ o, (Fk X N P).oracleAt (seatAt l num at_ j).1 = some o → o.logLength = Johnson.Pack.aOf
      Johnson.Top.H.csKey (l.get j).1
  mains : (l.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain Johnson.Top.H.csKey (l.get j).1).a =
      Johnson.Pack.aOf Johnson.Top.H.csKey (l.get j).1

variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}

/-- **THE FIELD r1_0 OF The35, IN SCOPE, AT THE LIBRARY's TYPED CODES.** R is a letter. -/
theorem r1_0_eight (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁)
    (H : Left10f X N P at_ coll l num orc₁) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey l num at_ decT recOf orc₁) at_
        R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey l num at_ decT recOf orc₁)
        at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃
        k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 := by
  have hc : (par10 X).codes = Johnson.Top.H.csKey := codes_key hZ hP hm hX hp
  obtain ⟨d₁, d₂, hd, h1, _⟩ := data10_of X N P DK c₁ k₁ q₁ (sealLast_of_planOk _ hp) hdata
  have hfirst : 0 < d₁.trees.length := by
    rw [h1.2.2.2.1]
    show 0 < (par10 X).trees.length
    rw [trees10 hZ hP hm hX hp]
    exact Nat.one_pos
  obtain ⟨sh, hsh⟩ := treeShT_some_of_lt [d₁, d₂] 0 (by rw [nTrees_cons]; omega)
  have a := asks10 hZ hP hm hX hp
  have k₀ : Fin (shapesOf (par10 X)).length := ⟨0, (len10 X).symm ▸ Nat.one_pos⟩
  have hk0 : k₀ = ⟨0, (len10 X).symm ▸ Nat.one_pos⟩ := Fin.ext
      (by have := k₀.isLt; have := len10 X; omega)
  have hshape : shapeAt (par10 X) k₀ = Johnson.Top.H.shIdx :=
      by rw [hk0]; exact shape10 hZ hP hm hX hp
  have T := r1_0_seven X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd at_ coll R l num decT
      recOf orc₁ q₁
    { d₁ := d₁, d₂ := d₂, data := hd, entry := h1.1
      kind := (Option.some.inj ((seed_kind (par10 X)).symm.trans h1.2.1)).symm
      first := hfirst, rad := fun _ => 6130, cond := cond10_in_scope hZ hP hm hX hp c₁ k₁ q₁,
      K := 129, share := a.share, below := a.below
      cap := hcap 0 [d₁, d₂], cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i,
      seatIs := H.seatIs, sh := sh, tree := hsh
      shownAll := shown10_of X N P DK c₁ k₁ rest₁ q₁ hp hdata H.cs H.m H.fam H.fits [d₁, d₂] hd
      sampled := (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁).sampled,
      lay := (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁).lay, seat := H.seat, cell := H.cell,
      k₀ := k₀
      sampledAt := by rw [hk0]; exact (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁).sampled
      j := H.j, memberIs := by rw [hshape]; exact H.memberIs
      numIs := H.numIs, orcIs := H.orcIs, inj := H.inj, apart := H.apart
      tie := by rw [hc]; exact H.tie
      logs := by rw [hc]; exact H.logs
      mains := by rw [hc]; exact H.mains }
  rw [hc] at T
  exact T

/-- **memberIs at six** (Johnson/Desc/Key/KeyFillAtSizes.lean): the first of the
six IS (shIdx, 6130): the numeral of asks_in_scope, in this file's head, is six's. -/
theorem member10_six : six.get ⟨0, by decide⟩ = (Johnson.Top.H.shIdx, 6130) := rfl

end

end LPFD

#print axioms LPFD.data10_of
#print axioms LPFD.shown10_of
#print axioms LPFD.r1_0_eight
#print axioms LPFD.member10_six
