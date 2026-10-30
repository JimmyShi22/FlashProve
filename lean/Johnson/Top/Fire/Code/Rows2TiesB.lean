-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2TiesB.lean: THE KEY FILE, THE SHARED CHAIN: ROW 2.1's TWO TIES ON LETTERS PAID AT The21Off's OWN LETTERS; AND ROWS 2.1 · 2.4 · 2.7 AT A WRITTEN ENCODER AND RADIUS, WITH NOTHING IN FRONT BUT WHAT THE SEAT HANDS. Behind Rows2AtNameB.lean.
OBJECT. CollTie | DecTie (Johnson/RunOne/KeyGood21.lean) at Fk X N P · fr₂ · (baseAt X decN recBack).h₂ · atSix · (p14At X P).par · plan₁ (oneAt X) · readAt tabN · any enc · 2852142980 · collN · last₁At (oneAt X) · off₂N · any err · eM := 2852142980 · rank := rank0. Then KeepsAt (On₂' …) (Cl₂ …) ‹the maker's row of chain 2› k, k = 1 | 4 | 7, at enc := encOf (p14At X P).par.S.fold · rad := Params.recordRadius.
HOW. collTie_at | decTie_at (Johnson/RunOne/KeyTies21At.lean: the two ties at the library's decoder decRec T v eM lg s) CALLED at T v lg s := recT recV recLg recS: the name's own configuration DN IS that decoder (OnBytes/Flat/EntryRecord.lean: by rfl; Lean unifies the types). THEIR PREMISES, EACH PAID: the four equations on the index and the four public facts (the shape is the written key's: shape_full; then the kernel) · hkey: the OOD sample that recBack returns writes the instance's key (recBack_spec; keyInstanceOfOutOfDomainSample's text) · hcl | hdc: collN | decN ARE the decoder's collision and decoding at the stored table off the cells (their definitions: id, rfl) · htab: tabN reads a base-valued table's entry as that entry (rdF_baseW; the two spellings of a row's bits are one: rfl).
  recBack_spec · par_full · collTie_at_name · decTie_at_name
  r2_1_tied: row 2.1 with the two ties paid; henc is left.
  r2_7_at_enc | r2_4_at_enc | r2_1_at_enc: at the written encoder (encIs_encOf) and radius. fit_2147.
IN FRONT OF THE LAST THREE STAND: the three heads · the five in scope · wantedOk · the data · the pin on the data. NO NUMBER, NO PUBLIC FACT AND NO CONDITION ON A LETTER IS LEFT AS A PREMISE.
THE TWO LETTERS enc | rad, WHICH The21Off BINDS BY ∃, ARE PICKED HERE: whoever joins the 21 must have the other rows at the same pick.
UNTIL A MEMBER OF THE PROMISE AT THESE BORDERS IS SHOWN, each of the three may be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls alone: no new law. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2AtNameB
import Johnson.RunOne.KeyTies21At

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
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- The OOD sample that recBack returns writes the instance. -/
theorem recBack_spec (x : Xi) (r : RecFull) (h : recBack x = some r) : VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r = x := by
  unfold recBack at h
  split at h
  · rename_i hx
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hx
  · cases h

theorem par_full (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) : (p14At X P).par.S = keyFull.once.shape := shape_full hZ hP hm hX hp

/-- **CollTie, at the name's own letters.** -/
theorem collTie_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (err : ℕ) (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    Johnson.RunOne.KeyRows23.CollTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 (_root_.Desc.K14.Law.rank0 (p14At X P).par.S.fold) := by
  have e := par_full X N P hZ hP hm hX hp
  refine Johnson.RunOne.KeyRows23.collTie_at (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (p14At X P).par err 2852142980 OnBytes.Slice.recT OnBytes.Slice.recV OnBytes.Slice.recLg OnBytes.Slice.recS
    (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel)
    (baseAt X decN recBack).h₂ atSix _ (readAt tabN) enc 2852142980 _ collN _ off₂N
    (fun z r h => (congrArg (·.key) (recBack_spec z.1.1 r h)).symm) (fun y r h => h)

/-- **DecTie, at the name's own letters.** -/
theorem decTie_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (err : ℕ) (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    Johnson.RunOne.KeyRows23.DecTie (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack).h₂ atSix (p14At X P).par (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc 2852142980 (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N err 2852142980 (_root_.Desc.K14.Law.rank0 (p14At X P).par.S.fold) := by
  have e := par_full X N P hZ hP hm hX hp
  refine Johnson.RunOne.KeyRows23.decTie_at (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (p14At X P).par err 2852142980 OnBytes.Slice.recT OnBytes.Slice.recV OnBytes.Slice.recLg OnBytes.Slice.recS
    (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel)
    (baseAt X decN recBack).h₂ atSix _ (readAt tabN) enc 2852142980 _ collN _ off₂N
    (fun z r h => (congrArg (·.key) (recBack_spec z.1.1 r h)).symm) (fun _ _ => rfl) ?_
    (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel) (by rw [e]; decide +kernel)
  intro c r k hk hb hr
  show rdF (tabN c r k) = _
  have hk' : k < DN.T.l := hk
  unfold tabN
  rw [dif_pos hk', rdF_baseW _ (hb _)]
  rfl

/-- **The21's FIELD r2_1 AT The21Off's TERMS, IN SCOPE, THE TWO TIES PAID**: at rad := Params.recordRadius and every enc that is the code's encoder. -/
theorem r2_1_tied (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (henc : Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold enc) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 1 :=
  r2_1_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK henc 0 (_root_.Desc.K14.Law.rank0 (p14At X P).par.S.fold)
    (collTie_at_name X N P DK enc 0 hZ hP hm hX hp) (decTie_at_name X N P DK enc 0 hZ hP hm hX hp)

/-- **ROW 2.7 AT THE WRITTEN ENCODER AND RADIUS.** -/
theorem r2_7_at_enc (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 7 :=
  r2_7_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ _ _ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK

/-- **ROW 2.4 AT THE WRITTEN ENCODER AND RADIUS.** -/
theorem r2_4_at_enc (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 4 :=
  r2_4_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ _ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK (Johnson.RunOne.KeyRows23.encIs_encOf _ _)

/-- **ROW 2.1 AT THE WRITTEN ENCODER AND RADIUS.** -/
theorem r2_1_at_enc (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 1 :=
  r2_1_tied X N P DK c₁ k₁ c₂ k₂ c₃ k₃ _ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK (Johnson.RunOne.KeyRows23.encIs_encOf _ _)

/-- **THE FIT**: the three conclusions ARE The21's fields r2_1 · r2_4 · r2_7 at The21Off's terms, at enc := the written encoder, rad := Params.recordRadius: by Lean's own check of types. -/
def fit_2147 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) (Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold) OnBytes.Params.recordRadius collN off₂N off₃N :=
  { H with
    r2_1 := r2_1_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
    r2_4 := r2_4_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
    r2_7 := r2_7_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK }

end

end LPFD

#print axioms LPFD.recBack_spec
#print axioms LPFD.par_full
#print axioms LPFD.collTie_at_name
#print axioms LPFD.decTie_at_name
#print axioms LPFD.r2_1_tied
#print axioms LPFD.r2_7_at_enc
#print axioms LPFD.r2_4_at_enc
#print axioms LPFD.r2_1_at_enc
#print axioms LPFD.fit_2147
