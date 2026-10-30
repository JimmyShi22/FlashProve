-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row11Eight.lean (the two blocksOk are first_blocksOk |
  shared_blocksOk, called; so is msg_shape_full, of Johnson/RunOne/KeySeatScope.lean): THE
  KEY FILE's ROW 1.1, LEVEL 8: IN THE GOALS' SCOPE, OVER LEVEL 7 (Row11Seven.lean, no byte
  turned): EVERY PUBLIC PREMISE OF Left11e FOR WHICH A PAYER LIES IS PAID BY A CALL. By row 1.0's
  level 8 (Row10Eight.lean). What is left is Left11f.
OBJECT: The35.r1_1 at B := baseK csKey l num at_ decT recOf orc₁ AND AT R := kreadFam csKey
  l num at_ tab · USER: The21AtBase's filler · LETTERS: level 7's without R and ρ; tab; the
  scope's Zp · X₀ · cfg · m.
R IS FIXED HERE (kreadFam: so that «same» is kreadFam_same, by rfl, at the library's
  reading Reading.gl); at row 1.0's level 8 it is a letter: The35 runs over one R: 1.0 is
  instantiated.
  CLOSED, BY THE KERNEL, at the written key: mMsg's two notices: answers 1 | 0 · masks ride · a
    stage · the layout (layB) is made and is one tree, parts 0 | 1 · shMul is sampled · THE
    PLANT: m0_answers_no
  public11_full  THERE IS a Public11 where the source's ranges and codes are keyFull's and the
    place's own test on the plan holds (after public117_full, Row117PubFull.lean)
  shapes_of      a place with one part sends that part's shapes
  long1          PAID: the chain has a third block (flat_eq, Johnson/RunOne/KeySendFlat.lean)
  data11_of      PAID: as data10_of, at block 1, over the held blocks (cutDs_held)
  base11_of      PAID: the piece's base is 1: cutBase_eq; the first stretch sends one tree
    (data10_of · trees10)
  shown11_of     PAID: shownAll at the maker's second piece (cutShown)
  Left11f        WHAT IS LEFT: cs m fam fits i seatIs · seat0 · seat1 · cell · j · memberIs (l.get
    j = (shMul, 3131959): closed) · numIs · orcIs · arr · the five on baseK's family, at csKey
  r1_1_eight     PROVED · member11_six: memberIs at six, j := 1: by rfl
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10Eight
import Johnson.Top.Fire.Code.Row117PubFull

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
open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open Johnson.RunOne.KeyRows23 (smGroupsK kreadFam kreadFam_same)

/-! ## Closed facts at the written key, by the kernel -/

def mMsg : Array OnBytes.OracleNotice := Wf.messageOf keyFull.ranges.x

theorem mMsg_size : mMsg.size = 2 := by decide +kernel
theorem m0_answers : (mMsg[0]?).map (·.shape.answers) = some 1 := by decide +kernel
theorem m0_answers_no : ¬ (mMsg[0]?).map (·.shape.answers) = some 0 := by decide +kernel
theorem m1_answers : (mMsg[1]?).map (·.shape.answers) = some 0 := by decide +kernel
theorem m_ride : keyFull.ranges.x.choice.masksRide = true := by decide +kernel
theorem m_stages : decide (1 ≤ keyFull.ranges.x.stages.length) = true := by decide +kernel
theorem m_lay : layB keyFull.codes mMsg = true := by decide +kernel
/-- The layout is made there: so m_lay is not met by the arm «none». -/
theorem m_lay_made : (OnBytes.layTrees keyFull.codes mMsg).isSome = true := by decide +kernel
theorem shMul_sampled : decide (Johnson.Top.H.shMul.answers ≠ 0) = true := by decide +kernel

/-- **There is a Public11** where the source's ranges and codes are the written key's. -/
theorem public11_full (one : OnBytes.Params.OneTime) (Np : Pieces) (groups : List (List Nat)) (h1 :
    one.ranges = keyFull.ranges.x) (h5 : one.codes = keyFull.codes)
    (hplan : planOkOwn (Johnson.RunOne.KeyRows1.parMsg' one Np groups) = true) : Nonempty (Public11
        one Np groups) := by
  obtain ⟨a, b, hab⟩ := two_of_size mMsg mMsg_size
  have hm : Wf.messageOf one.ranges = #[a, b] := by rw [h1]; exact hab
  have ha : a.shape.answers = 1 := by
    have := m0_answers
    rw [hab] at this
    exact Option.some.inj this
  have hb : b.shape.answers = 0 := by
    have := m1_answers
    rw [hab] at this
    exact Option.some.inj this
  exact ⟨{ n₁ := a, n₂ := b, two := hm, plan := hplan, sampled := by rw [ha]; decide, bare := hb
           ride := by rw [h1]; exact m_ride, stages := by rw [h1]; exact of_decide_eq_true m_stages
           lay := fun lay hl => by
             have h := m_lay
             unfold layB at h
             rw [hab, ← h5, hl] at h
             simp only [Bool.and_eq_true, beq_iff_eq] at h
             exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩ }⟩

/-- A place with one part sends that part's shapes. -/
theorem shapes_of (Q : Par) (what : String) (msg : Array OnBytes.OracleNotice) (h : Q.parts =
    [(what, msg)]) : shapesOf Q = msg.toList.map (·.shape) := by
  unfold shapesOf Par.sent
  rw [h]
  simp

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

variable (tab : Cells → ℕ → ℕ → OnBytes.F) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length
    → ℕ)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ →
      Option ℕ)
  (b₁ : Block (Fk X N P).S₁ (Fk X N P).Cl)

/-- The chain has a third block. -/
theorem long1 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : 1 < k₁.length := by
  have h := congrArg List.length q₁
  rw [Johnson.RunOne.KeySendGood.flat_eq] at h
  simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] at h
  have hf : 0 < (Fk X N P).first.front.length := (List.getElem?_eq_some_iff.1 (show (Fk X N
      P).first.front[0]? = some (send11 X) from rfl)).1
  omega

/-- **The stretch at block 1, from the description's own data.** -/
theorem data11_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) (hs : (Fk
             X N P).sealLast = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    ∃ d₁ d₂, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N
        P).Cl) (k₁.map held) 1 = [d₁, d₂] ∧
      RoundAsG d₁ { entry := seedEntry (par11 X) } ∧ RoundAsG d₂
          { entry := K1.answerEntry (par11 X) } := by
  have has := stretch_of_data₁ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₁ k₁ q₁ (last_of_seal
      (Fk X N P) hs c₁ k₁ q₁) 1 (long1 X N P c₁ k₁ q₁) b₁ hb
  have hr : b₁.rounds = K1.rounds (par11 X) :=
      by rw [second_block X N P c₁ k₁ b₁ q₁ hb]; exact rounds_msg X
  rw [hr] at has
  have has' : List.Forall₂ RoundAsG (cutDs (DK.at frS.P.T.a).ds₁ c₁ k₁ 1)
      [{ entry := seedEntry (par11 X) }, { entry := K1.answerEntry (par11 X) }] := has
  obtain ⟨d₁, l₁, h1, t1, e1⟩ := List.forall₂_cons_right_iff.1 has'
  obtain ⟨d₂, l₂, h2, t2, e2⟩ := List.forall₂_cons_right_iff.1 t1
  obtain rfl := List.forall₂_nil_right_iff.1 t2
  subst e2
  exact ⟨d₁, d₂, (cutDs_held k₁ 1 _ c₁).trans e1, h1, h2⟩

/-- **The second piece's base is 1**, where the first place has one tree. -/
theorem base11_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata :
             (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (ht : (par10 X).trees.length = 1) :
    cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N
        P).Cl) (k₁.map held) 1 = 1 := by
  obtain ⟨e₁, e₂, he, g1, g2⟩ := data10_of X N P DK c₁ k₁ q₁ hs hdata
  obtain ⟨c, l', hk⟩ := second_is X N P c₁ k₁ q₁
  rw [cutBase_eq _ 1 0 _ _ (by rw [hk]; simp)]
  have eb : before (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held)
      1 = c₁.rounds.length := by
    rw [hk]
    cases l' <;> rfl
  rw [eb, he, nTrees_cons, nTrees_cons, g1.2.2.2.1, g2.2.2.2.1]
  show 0 + ((par10 X).trees.length + (0 + Sound.nTrees [])) = 1
  rw [ht]
  rfl

/-- **shownAll at the maker's second piece.** -/
theorem shown11_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁) (hp : (Fk
             X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ) (fits :
        Sound.SeatFits (Fk X N P) cs m fam)
    (base' : ℕ) (ds' : List RDT)
    (eb : cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X
        N P).Cl) (k₁.map held) 1 = base')
    (e : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N
        P).Cl) (k₁.map held) 1 = ds') :
    (pieceOf (held b₁ : Block (Xi × FirstState) Claim) base' ds' [] (rest₁ 1 ds')).ShownAll (Fk X N
        P) cs m fam := by
  have hl := long1 X N P c₁ k₁ q₁
  obtain ⟨c, c', l'', rfl⟩ : ∃ c c' l'', k₁ = c :: c' :: l'' := by
    match k₁, hl with
    | c :: c' :: l'', _ => exact ⟨c, c', l'', rfl⟩
  obtain rfl : c = b₁ := Option.some.inj hb
  subst eb e
  have b1 := first_blocksOk X N P hp
  have b2 := shared_blocksOk X N P hp
  exact cutShown (ckP .two) _ _ _ _ rest₁ [] (DK.at frS.P.T.a) ((c :: c' :: l'').map held) (held c₁)
      0 0 (DK.at frS.P.T.a).ds₁ rfl (shape_own₁ _) _ (Fk X N P) cs m fam fits
    (oraclesAreOk _ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata (sentFit_of_planOk _ hp) b1 b2) _
        (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **WHAT IS LEFT OF ROW 1.1 IN SCOPE.** -/
structure Left11f where
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = at_ 1
  seat0 : at_ 0 = (0, 0)
  seat1 : at_ 1 = (1, 0)
  cell : CollCell coll
  /-- THE TIES AT THE CALL -/
  j : Fin l.length
  memberIs : l.get j = (Johnson.Top.H.shMul, 3131959)
  numIs : num j = 1
  orcIs : orc₁ = (plan₁ (oneAt X)).orc
  arr : ArrOk (baseK (Cells := Cells) Johnson.Top.H.csKey l num at_ decT recOf orc₁).h₁ at_ [0, 1,
      2]
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

/-- **THE FIELD r1_1 OF The35, IN SCOPE, AT THE LIBRARY's TYPED CODES AND AT THE READER OF THE
WITNESS.** R is fixed: kreadFam. -/
theorem r1_1_eight (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁)
    (H : Left11f X N P at_ coll l num decT recOf orc₁) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey l num at_ decT recOf orc₁) at_
        (kreadFam Johnson.Top.H.csKey l num at_ tab) coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK
        Johnson.Top.H.csKey l num at_ decT recOf orc₁) at_ (kreadFam Johnson.Top.H.csKey l num at_
        tab)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃
        k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1 := by
  have hc : (par11 X).codes = Johnson.Top.H.csKey := codes_key hZ hP hm hX hp
  have hs := sealLast_of_planOk _ hp
  obtain ⟨-, hr, -, -, h5⟩ := five_in_scope hZ hP hm hX hp
  obtain ⟨d₁, d₂, hd, h1, _⟩ := data11_of X N P DK c₁ k₁ b₁ q₁ hb hs hdata
  have hfirst : 0 < d₁.trees.length := by
    rw [h1.2.2.2.1]
    show 0 < (par11 X).trees.length
    rw [trees11 hZ hP hm hX hp]
    exact Nat.one_pos
  obtain ⟨sh, hsh⟩ := treeShT_some_of_lt [d₁, d₂] 0 (by rw [nTrees_cons]; omega)
  have a := asks11 hZ hP hm hX hp
  obtain ⟨pub⟩ := public11_full (oneAt X) pieces (g11 X) hr h5 (plan11_of hp)
  have hbase := base11_of X N P DK c₁ k₁ q₁ hs hdata (trees10 hZ hP hm hX hp)
  have hsh2 : shapesOf (par11 X) = mMsg.toList.map (·.shape) := by
    rw [shapes_of (par11 X) _ (Wf.messageOf X.Y.k.oneTime.ranges) rfl, hr]
    rfl
  have htwo : (shapesOf (par11 X)).length = 2 :=
      by rw [hsh2, List.length_map, Array.length_toList]; exact mMsg_size
  obtain ⟨k₀, hk0⟩ : ∃ k : Fin (shapesOf (par11 X)).length, k.val = 0 := ⟨⟨0, by rw [htwo]; decide⟩,
      rfl⟩
  have hget : (shapesOf (par11 X))[k₀.val]? = some Johnson.Top.H.shMul := by
    rw [hk0, hsh2, List.getElem?_map, Array.getElem?_toList]
    exact Johnson.RunOne.KeyLetters.msg_shape_full
  have hshape : shapeAt (par11 X) k₀ = Johnson.Top.H.shMul := by
    obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 hget
    exact e
  have T := r1_1_seven X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd at_ coll (kreadFam
      Johnson.Top.H.csKey l num at_ tab) l num decT recOf orc₁ b₁ OnBytes.Model.Reading.gl q₁ hb
    { d₁ := d₁, d₂ := d₂, data := hd
      put := cutPut_inner [sealRound] _ 1 (by rw [List.length_map]; exact long1 X N P c₁ k₁ q₁)
      baseIs := hbase, entry := h1.1
      kind := (Option.some.inj ((seed_kind (par11 X)).symm.trans h1.2.1)).symm
      first := hfirst, rad := fun _ => 3131959, cond := cond11 hZ hP hm hX hp, K := 129,
      share := a.share, below := a.below
      cap := hcap 1 [d₁, d₂], cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i,
      seatIs := H.seatIs, sh := sh, tree := hsh
      shownAll := shown11_of X N P DK c₁ k₁ rest₁ b₁ q₁ hb hp hdata H.cs H.m H.fam H.fits 1 [d₁, d₂]
          hbase hd
      pub := pub, seat0 := H.seat0, seat1 := H.seat1, cell := H.cell
      same := (kreadFam_same Johnson.Top.H.csKey l num at_ tab).trans sameGl_eq
      k₀ := k₀
      sampledAt := by
        show (shapeAt (par11 X) k₀).answers ≠ 0
        rw [hshape]
        exact of_decide_eq_true shMul_sampled
      two := htwo, kIs := hk0
      j := H.j, memberIs := by rw [hshape]; exact H.memberIs
      numIs := H.numIs, orcIs := H.orcIs
      arr := by rw [hc]; exact H.arr
      inj := H.inj, apart := H.apart
      tie := by rw [hc]; exact H.tie
      logs := by rw [hc]; exact H.logs
      mains := by rw [hc]; exact H.mains }
  rw [hc] at T
  exact T

theorem member11_six : six.get ⟨1, by decide⟩ = (Johnson.Top.H.shMul, 3131959) := rfl

end

end LPFD

#print axioms LPFD.mMsg_size
#print axioms LPFD.m0_answers
#print axioms LPFD.m0_answers_no
#print axioms LPFD.m1_answers
#print axioms LPFD.m_ride
#print axioms LPFD.m_stages
#print axioms LPFD.m_lay
#print axioms LPFD.m_lay_made
#print axioms LPFD.shMul_sampled
#print axioms LPFD.public11_full
#print axioms LPFD.shapes_of
#print axioms LPFD.long1
#print axioms LPFD.data11_of
#print axioms LPFD.base11_of
#print axioms LPFD.shown11_of
#print axioms LPFD.r1_1_eight
#print axioms LPFD.member11_six
