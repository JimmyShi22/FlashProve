-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117Nine.lean: THE KEY FILE's ROW 1.17 (w.1.send), IN THE GOALS' SCOPE, AT THE FILLING's OWN LETTERS (the six written seats): **NO STRUCTURE OF DEBTS IS LEFT**: EVERY FIELD OF Left117f IS PAID BY A CALL. BY LEVEL 9 FOR ROWS 1.0 | 1.1 (RowsNine.lean), STEP FOR STEP.
OBJECT: The35.r1_17 at B := baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc · R := kreadFam csKey six numSix atSix tab · USER: The21AtBase | The21AtName's filler · LETTERS: X N P · the maker's cut and rests · tab · coll · decT recOf · Zp X₀ cfg m.
  w_shape_full    BY THE KERNEL: the written shape's message with W: its first notice has the library's shape shW · w_shape_no: A CONTROL: not shMul
  member17_six    rfl: six (Johnson/Desc/Key/KeyFillAtSizes.lean) has (shW, 3138896) at 2: the radius at W's place: ONE NUMERAL
  noFault2        the library's test on a seat finds no fault at (shW, tree 5, tenant 0) of F_K's own description: n2_scope (Johnson/RunOne/KeySeatScopeW2.lean), called
  left117f_six    Left117f AT THE SIX, AT EVERY Public117 AND AT THE DATA's OWN TWO ROUNDS
  r1_17_nine      **THE FIELD r1_17** FROM q₁ AND TEN PREMISES: the eight of RowsNine.lean's level 9 (hZ · hP · hm · hX · hp · hdata · hcap · hc) AND TWO MORE, handed by the seat or held in scope: hwant (the description's test wantedOk: The21AtSeat hands it) · hDK («the record's data are the written data»: pin_at_seat, Johnson/Goal/Conditions/KeyAtTheSeat.lean)
WHICH CALL PAYS WHICH FIELD: radW := fun _ => 3138896 · K := 129 · share | below | (cond's) meets: asks_in_scope (Johnson/RunOne/KeySendScope.lean) at W · cond: cond_of (Johnson/RunOne/KeySendGood.lean) at planOwn_w (Johnson/RunOne/KeySamples.lean) and lengths_key (RowScope.lean) · cs m fam | fits | i | seatIs: fits_one (RowsNine.lean) at noFault2 · sh | tree: treeShT_some_of_lt at data17_more | trees117_full · shownAll: shown_inner₁ (RowShownAt.lean) · treeAt: treeAt_full (RowBaseFull.lean) · base0: from treeAt · seat2: stages_full (Johnson/RunOne/KeyScopeNums.lean) · cell: from CellOnly · same: kreadFam_same, sameGl_eq · memberIs: member17_six at w_shape_full · numIs | orcIs: rfl · arr | inj | apart | tie: arrOk_six₁ | seat_inj_six | shapesApart_six | tie_six · logs: logs_of (RowsNine.lean) at noFault2 · mains: mains_six (RowsEightSix.lean) · hl | hw: hl_in_scope | hw_in_scope (KeyPublicAtSeat.lean) · hL: rounds_in_scope (KeyRoundsAtSeat.lean).
NO MEMBER OF THE ROW's GUARD (On₁' … 17) IS SHOWN: r1_17_nine MAY BE TRUE AND EMPTY. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row117Plan
import Johnson.Top.Fire.Code.RowShownAt
import Johnson.Top.Fire.Code.RowBaseFull
import Johnson.Top.Fire.Code.RowsNine
import Johnson.Top.Fire.Code.KeyRoundsAtSeat

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

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry Tie planOkOwn)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW six)
open Johnson.RunOne.KeySendGood (SendAsks asks_in_scope cond_of parIdx parMsg fullIdx fullMsg idx_at msg_at idx_pays msg_pays pays_bare rounds_idx rounds_msg seed_kind)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open Johnson.RunOne.KeyRows23 (smGroupsK kreadFam kreadFam_same numSix atSix seatFits_iff fitsAt_of_noFault)
open Johnson.RunOne.KeyLetters (n01_scope)

open Johnson.RunOne.KeyRows23 (seat_inj_six shapesApart_six arrOk_six₁ tie_six)
open Johnson.RunOne.KeyRows1 (Public117)
open Johnson.G (writtenKFull)

theorem w_shape_full : (wMsg[0]?).map (·.shape) = some Johnson.Top.H.shW := by decide +kernel
/-- A control. -/
theorem w_shape_no : ¬ (wMsg[0]?).map (·.shape) = some Johnson.Top.H.shMul := by decide +kernel

theorem member17_six : six.get ⟨2, by decide⟩ = (Johnson.Top.H.shW, 3138896) := rfl

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
    (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

variable (R : KRead Cells Fill.Tab) (tab : Cells → ℕ → ℕ → OnBytes.F)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (bw b₁₇ : Block FirstState Claim)


variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}


theorem noFault2 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hD : (Fk X N P).data "key file" = .ok writtenKFull) :
    seatFaultAt (Fk X N P) Johnson.Top.H.csKey "row 1.17" Johnson.Top.H.shW 5 0 = none :=
  Johnson.RunOne.KeyLetters.n2_scope X N P (codes_key hZ hP hm hX hp) (five_in_scope hZ hP hm hX hp).2.2.1 hp hD (rounds_in_scope hZ hP hm hX hp hwant).1 "row 1.17"

/-- W's notice has the library's shape, in scope. -/
theorem shapeW_scope (hlin : (oneAt X).lin = keyFull.once.shape) (Pb : Public117 (oneAt X) pieces (g17 X)) : Pb.n₁.shape = Johnson.Top.H.shW := by
  have e : #[Pb.n₁, Pb.n₂] = wMsg := Option.some.inj (Pb.two.symm.trans (hlin ▸ wMsg_some))
  have h := w_shape_full
  rw [← e] at h
  exact Option.some.inj h

/-- **Left117f at the six.** -/
def left117f_six (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull) (hc : CellOnly coll)
    (Pb : Public117 (oneAt X) pieces (g17 X)) (d₁ d₂ : RDT) (hb : (c₁ :: k₁)[17]? = some b₁₇)
    (hd : cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂]) :
    Left117f X N P DK c₁ k₁ rest₁ atSix coll (kreadFam Johnson.Top.H.csKey six numSix atSix tab) six numSix decT recOf (plan₁ (oneAt X)).orc b₁₇ OnBytes.Model.Reading.gl Pb d₁ d₂ :=
  have hck : (par17 X Pb.n₁ Pb.n₂).codes = Johnson.Top.H.csKey := codes_key hZ hP hm hX hp
  have h5s := five_in_scope hZ hP hm hX hp
  have a := (asks_in_scope hZ hP hm hX hp).2.2 #[Pb.n₁, Pb.n₂] Pb.two
  have nf := noFault2 X N P hZ hP hm hX hp hwant (hDK ▸ hdata)
  have htree := treeAt_full X N P DK c₁ k₁ q₁ (rounds_in_scope hZ hP hm hX hp hwant).1 hDK h5s.2.1
  have hfirst : 0 < d₁.trees.length := by
    rw [data17_more X N P DK c₁ k₁ bw x₀ x₁ hl hw q₁ (sealLast_of_planOk _ hp) hdata Pb.n₁ Pb.n₂ Pb.two b₁₇ d₁ d₂ hb hd]
    exact trees117_full (oneAt X) pieces (g17 X) h5s.2.2.1 h5s.2.2.2.2 Pb
  have hsh := treeShT_some_of_lt [d₁, d₂] 0 (by rw [nTrees_cons]; omega)
  { radW := fun _ => 3138896
    cond := cond_of _ _ (Johnson.RunOne.KeySendGood.planOwn_w hp Pb.two) (lengths_key hZ hP hm hX hp) a.meets
    K := 129, share := a.share, below := a.below
    cs := Johnson.Top.H.csKey, m := [(Johnson.Top.H.shW, 3138896)], fam := fun _ => (5, 0)
    fits := fits_one _ _ _ _ _ _ _ nf, i := ⟨0, Nat.one_pos⟩, seatIs := rfl
    sh := Classical.choose hsh, tree := Classical.choose_spec hsh
    shownAll := shown_inner₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ rest₁ "key file" hp hdata _ _ _ (fits_one _ _ _ _ _ _ _ nf) 17
      (long17 X N P c₁ k₁ bw x₀ x₁ hl hw q₁) b₁₇ hb _ _ rfl hd
    base0 := by rw [htree]; exact Nat.succ_pos _
    seat2 := by rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]; rfl
    treeAt := htree
    cell := fun y y' r e => (hc y y' r e).1
    same := (kreadFam_same Johnson.Top.H.csKey six numSix atSix tab).trans sameGl_eq
    j := ⟨2, by decide⟩
    memberIs := by rw [shapeW_scope X h5s.2.2.1 Pb]; exact member17_six
    numIs := rfl, orcIs := rfl
    arr := by rw [hck]; exact arrOk_six₁ _ decT recOf _
    inj := seat_inj_six, apart := shapesApart_six
    tie := by rw [hck]; exact tie_six _
    logs := by rw [hck]; exact logs_of _ _ _ _ _ _ nf
    mains := by rw [hck]; exact mains_six _ }

/-- **THE FIELD r1_17 OF The35, IN SCOPE, AT THE SIX: NO STRUCTURE OF DEBTS IS LEFT.** R is fixed: kreadFam. -/
theorem r1_17_nine (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (hcap : AtCap rest₁) (hc : CellOnly coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (sent17 X) (g17 X)
  have h5s := five_in_scope hZ hP hm hX hp
  have T := r1_17_scope2 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix coll (kreadFam Johnson.Top.H.csKey six numSix atSix tab) six numSix decT recOf (plan₁ (oneAt X)).orc bw OnBytes.Model.Reading.gl
    x₀ x₁ hl hw q₁ hp hdata hcap h5s.2.1 h5s.2.2.1 h5s.2.2.2.2
    (fun Pb b₁₇ d₁ d₂ hb hd => left117f_six X N P DK c₁ k₁ rest₁ coll tab decT recOf bw b₁₇ x₀ x₁ hl hw q₁ hZ hP hm hX hp hwant hdata hDK hc Pb d₁ d₂ hb hd)
  rw [codes_key hZ hP hm hX hp] at T
  exact T

end

end LPFD

#print axioms LPFD.w_shape_full
#print axioms LPFD.w_shape_no
#print axioms LPFD.member17_six
#print axioms LPFD.noFault2
#print axioms LPFD.shapeW_scope
#print axioms LPFD.left117f_six
#print axioms LPFD.r1_17_nine
