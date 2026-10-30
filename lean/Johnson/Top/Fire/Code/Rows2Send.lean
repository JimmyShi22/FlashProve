-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2Send.lean: THE KEY FILE, THE SHARED CHAIN: THE CALLS OF ROWS 2.2
  ("send o_u") AND 2.5 ("send o_omega"): The21's fields r2_2 · r2_5 AT The21Off's WRITTEN TERMS, IN
  THE GOALS' SCOPE, FROM ONE PREMISE EACH: "behind the piece every leaf is shown at the new pins".
OBJECT. KeepsAt (On₂' …) (Cl₂ …) ‹the maker's row of chain 2› 2 | 5 at capRest ×3 · () () · baseAt X
  decN recBack · atSix · readAt tabN · collN · off₂N; any enc rad.
HOW. The law at the seat (keeps₂_send2_seat | keeps₂_send5_seat,
  Johnson/RunOne/KeyRowsBackAtSeat.lean) CALLED at the maker's own piece (keepsAt_of_law₂) and
  lifted over the history (KeepsAt.reached), at Q := p14Key (beforeSharedPoint P) (RunOne's files'
  way: the eight sub-protocols' equation rewritten by p14At_key), so that the closed facts at the
  typed key fit by rfl (withU_key · len2 | len5 · smp2 | smp50 | smp51 · tieS2 | tieS50 | tieS51).
  two_rounds₂   HERE: the maker's piece number n has two written rounds, nothing put behind, and the
      base that the cut says.
  PAID BY CALLS: the piece's base 6 | 7, its first round's entry, kind and count of trees 1 | 2
      (base22 | base25 · seed22_key | seed25_key) · condPort and the written errors at
      or below 2^-128 at the six's own radii 8342420 | 3138896 · 6130 (cond_u_key |
      cond_omega_key · below_u_key | below_omega_key, KeyBelowTwo.lean) · the frame's own reading
      of the oracle messages (readerOf | readerIn · words_zero | words_fam) · the bases against
      the open pins (bases_of_all) · "yes" (yes22_seat | yes25_seat, their public
      premises as in two₂_made) · the ties (tie3_scope | tie4_scope | tie5_scope).
  New22 | New25   THE ONE PREMISE THAT IS LEFT OF EACH ROW, as a proposition: other files
      hold it (the statements new22 | new25, Johnson/RunOne/KeyNewAtSend2.lean).
  r2_2_new | r2_5_new   PROVED from it.
UNTIL A MEMBER OF THE PROMISE AT THESE BORDERS IS SHOWN, each may be true and empty at the real
  protocol, and counts as closing nothing.
Limits. Calls, and one lemma on the maker's cut: no new law. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2AtNameB
import Johnson.Top.Fire.Code.Rows2Public
import Johnson.Top.Fire.Code.KeyASide2All
import Johnson.Top.Fire.Code.Rows2SeedRound
import Johnson.RunOne.KeyRowsBackAtSeat
import Johnson.RunOne.KeyRow22AtSeat
import Johnson.RunOne.KeyOn2Scope
import Johnson.RunOne.KeyFillSeed2At
import Johnson.RunOne.KeyFillWords
import Johnson.RunOne.KeyBelowTwo

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
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁ plan₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open VerifiableInference.Desc.Key.Fill (six OmAt symsW)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)
open Johnson.RunOne.KeyRows23 (p14Key p14At_key key_of_scope sentUKey withU_key len2 len5 smp2 smp50
    smp51 tieS2 tieS50 tieS51 readerOf readerIn words_zero words_fam last₁At shared_2 shared_5
    yes22_seat yes25_seat keeps₂_send2_seat keeps₂_send5_seat tie3_scope tie4_scope tie5_scope)
open Johnson.RunOne.KeyMsg (cond_u_key cond_omega_key below_u_key below_omega_key)
open VerifiableInference.Desc.K1 (condPort sendPiece Sealed shapeAt shapesOf sampledAt errPort
    seedMaps seedEntry seeds_one seed_draws)
open _root_.Desc.K14 (parK1 withU withOmega)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m :
            Johnson.G.OfPlan.Made}

/-- **The maker's piece number n of the shared chain has two written rounds, nothing put behind, and
  the base that the cut says**, where the n-th sub-protocol declares two rounds and is not the last.
  -/
theorem two_rounds₂ (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (q₂ : (Fk X N
    P).shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (hn : n < k₂.length)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
        (hb : (c₂ :: k₂)[n]? = some b) (hl : b.rounds.length = 2)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[n]? = some (pieceOf
        (held b) base ds back (capRest n ds))) :
    ∃ d₁ d₂, cutDs (DK.at frS.P.T.a).ds₂ c₂ k₂ n = [d₁, d₂] ∧ ds = [d₁, d₂] ∧ back = [] ∧
      base = cutBase (DK.at frS.P.T.a).t₁ (DK.at frS.P.T.a).ds₂ (held c₂ : Block (((Fk X N P).XiPub
          × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) (k₂.map held) n := by
  obtain ⟨b', -, e⟩ := rowAt₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
      capRest capRest () () n _ hrow
  obtain ⟨d₁, d₂, hd⟩ := List.length_eq_two.1 ((stretch_len₂ (Fk X N P) "key file" (DK.at frS.P.T.a)
      hdata c₂ k₂ q₂ n b hb).trans hl)
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₂ (held c₂ : Block (((Fk X N P).XiPub × (Fk X N P).S₁) ×
      (Fk X N P).S₂) (Fk X N P).Cl) (k₂.map held) n := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₂.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁)))) n := congrArg
      (·.back) e
  exact ⟨d₁, d₂, hd, e1.trans ((cutDs_held k₂ n _ c₂).trans hd), e2.trans (cutPut_inner [] _ n (by
      rw [List.length_map]; exact hn)), congrArg (·.base) e⟩

/-- The sending kind's parameters at "send o_u" | "send o_omega", at the typed key. -/
abbrev par22 : VerifiableInference.Desc.K1.Par := parK1 (p14Key (beforeSharedPoint P)) 2
    "o_u and the first mask" sentUKey
abbrev par25 : VerifiableInference.Desc.K1.Par := parK1 (p14Key (beforeSharedPoint P)) 5
    "o_omega and o_sp" (withOmega keyFull.once.shape)

/-- The radii: the six's own. -/
abbrev rad22 : ℕ → ℕ := fun _ => 8342420
abbrev rad25 : ℕ → ℕ := fun k => if k = 0 then 3138896 else 6130

/-- **WHAT IS LEFT OF ROW 2.2**: behind the maker's piece every leaf is shown at the new pin. -/
def New22 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) : Prop :=
  ∀ (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT),
    ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[2]? = some (pieceOf (held
        b) base [d₁, d₂] [] (capRest 2 [d₁, d₂])) → base = 6 → d₁.trees.length = 1 →
    ∀ x τ x', On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N 2 x →
      (sendPiece (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X
          N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ (par22 P).coordinates (errPort (par22
          P) rad22)).ior.red.out x τ = some x' →
      ShownAt (Fk X N P) atSix 3 (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2)

/-- **WHAT IS LEFT OF ROW 2.5.** -/
def New25 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) : Prop :=
  ∀ (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (d₁ d₂ : RDT),
    ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[5]? = some (pieceOf (held
        b) base [d₁, d₂] [] (capRest 5 [d₁, d₂])) → base = 7 → d₁.trees.length = 2 →
    ∀ x τ x', On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N 5 x →
      (sendPiece (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X
          N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) base d₁ d₂ (par25 P).coordinates (errPort (par25
          P) rad25)).ior.red.out x τ = some x' →
      ∀ j ∈ [4, 5], ShownAt (Fk X N P) atSix j (strsOf (fr₂ (DK.at frS.P.T.a)) x'.2)

/-- **The21's FIELD r2_2 AT The21Off's TERMS, IN SCOPE, FROM New22.** -/
theorem r2_2_new (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁
    :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : New22 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 2 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have hkey : X.chains.made.sized.key = keyFull := key_of_scope hZ hP hm hX
  have h8k := h8
  rw [p14At_key hkey P] at h8k
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix
      (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  have eS : (p14At X P).S = keyFull.once.shape := shape_full hZ hP hm hX hp
  have eC := codes14_in_scope X N P hZ hP hm hX hp
  have ea : (oneAt X).given.plan.samples = 1 := Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm
      hX hp
  have hM : (p14At X P).S.masksAhead = true := Johnson.RunOne.KeyRows23.masks_of_form _
      (Johnson.RunOne.KeyRows23.form_of_fileOk X N P (fileOk_of_planOk' _ hp))
  have p2 : b2.planOk = true := plan_at X N P hp 2 b2 (shared_2 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8)
  have hC : condPort (par22 P) rad22 = true := cond_u_key (beforeSharedPoint P)
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 2) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad
      collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
      capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 2
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
      capRest () () _ _ 2 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[2]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant 2 b hb
  have hl : b.rounds.length = 2 := (Option.some.inj hr).symm
  obtain ⟨d₁, d₂, hd, rfl, rfl, ebase⟩ := two_rounds₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ hdata q₂ 2 (by
      omega) b base ds back hb hl hrow
  obtain rfl : base = 6 := ebase.trans (base22 c₂ k₂ hZ hP hm hX hp hwant hDK q₂)
  obtain ⟨he₁, hk₁, htr, -⟩ := seed22_key X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hkey hdata hp q₂
      d₁ d₂ hd
  have hbelow := below_u_key (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (beforeSharedPoint P) (held b
      : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) 6 d₁ d₂ he₁ hk₁
  have ebs : b = seat b2 := Option.some.inj (hb'.symm.trans (shared_2 X N P b1 b2 b3 b4 b5 b6 b7 b8
      h8))
  have h1 := seeds_one (par22 P) rad22 hC
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws (par22 P) h1 d₁ he₁ hk₁
  have K := keeps₂_send2_seat (W := Unit) (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack)
      atSix (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 h8k b
    (Johnson.RunOne.KeyRows23.shapeAt X) (plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt
        X).given.plan.samples collN (last₁At (oneAt X)) off₂N
    (by rw [ebs]; rfl) sentUKey withU_key (par22 P) rfl 6 d₁ d₂ rad22 hC h1 a1 a2 a3 a4 a5 (errPort
        (par22 P) rad22) (Nat.le_refl _)
    (readerOf (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par22 P).codes (shapeAt (par22 P)) (fun k => rad22
        k.val) 6 (fun _ => 0) (fun k => k.val))
    (readerIn (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par22 P).codes (shapeAt (par22 P)) (fun k => rad22
        k.val) 6 (fun _ => 0) (fun k => k.val) d₁)
    (words_zero (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par22 P).codes (shapeAt (par22 P)) (fun k =>
        rad22 k.val) 6 (fun k => k.val) _ d₁ d₂ _ _ (by omega))
    (hB 2 _ hrow) (ShownAt (Fk X N P) atSix 3) (H b 6 d₁ d₂ hrow rfl htr)
    (yes22_seat X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN
        recBack) atSix (plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN
        (last₁At (oneAt X)) off₂N hM p2
      (fun sentU hU => by
        rw [eS] at hU ⊢
        rw [eC, ea]
        have h := plan22_full
        rw [hU] at h
        exact h) rfl cellOnly_collN
      (sendPiece (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X
          N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) 6 d₁ d₂ (par22 P).coordinates (errPort (par22 P)
          rad22)) b hb' rfl)
    len2 ⟨0, by have h : (shapesOf (par22 P)).length = 2 := len2; omega⟩ smp2 rfl
    (fun x' _ hS => tie3_scope (X := X) (N := N) (P := P) (decT := decN) (recOf := recBack) (Fr₂ :=
        fr₂ (DK.at frS.P.T.a)) hZ hP hm hX hp hwant DK hdata hDK x' (by
      have e := tieS2
      exact e ▸ hS))
  exact ⟨⟨fun _ _ w => w, (seedMaps d₁ d₂ (par22 P).coordinates).err ((errPort (par22 P) rad22, ())
      : ℕ × Unit)⟩, K, Err.le_cap_of_below_inv 128 _ hbelow⟩

/-- **The21's FIELD r2_5 AT The21Off's TERMS, IN SCOPE, FROM New25.** -/
theorem r2_5_new (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁
    :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : New25 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 5 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have hkey : X.chains.made.sized.key = keyFull := key_of_scope hZ hP hm hX
  have h8k := h8
  rw [p14At_key hkey P] at h8k
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix
      (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  have eS : (p14At X P).S = keyFull.once.shape := shape_full hZ hP hm hX hp
  have eC := codes14_in_scope X N P hZ hP hm hX hp
  have ea : (oneAt X).given.plan.samples = 1 := Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm
      hX hp
  have p5 : b5.planOk = true := plan_at X N P hp 5 b5 (shared_5 X N P b1 b2 b3 b4 b5 b6 b7 b8 h8)
  have hC : condPort (par25 P) rad25 = true := cond_omega_key (beforeSharedPoint P)
  have hL5 : (shapesOf (par25 P)).length = 2 := len5
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 5) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad
      collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
      capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 5
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
      capRest () () _ _ 5 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[5]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant 5 b hb
  have hl : b.rounds.length = 2 := (Option.some.inj hr).symm
  obtain ⟨d₁, d₂, hd, rfl, rfl, ebase⟩ := two_rounds₂ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ hdata q₂ 5 (by
      omega) b base ds back hb hl hrow
  obtain rfl : base = 7 := ebase.trans (base25 c₂ k₂ hZ hP hm hX hp hwant hDK q₂)
  obtain ⟨he₁, hk₁, htr, -⟩ := seed25_key X N P "key file" (DK.at frS.P.T.a) c₂ k₂ hkey hdata hp q₂
      d₁ d₂ hd
  have hbelow := below_omega_key (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (beforeSharedPoint P)
      (held b : Block (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) 7 d₁ d₂
      he₁ hk₁
  have ebs : b = seat b5 := Option.some.inj (hb'.symm.trans (shared_5 X N P b1 b2 b3 b4 b5 b6 b7 b8
      h8))
  have h1 := seeds_one (par25 P) rad25 hC
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws (par25 P) h1 d₁ he₁ hk₁
  have K := keeps₂_send5_seat (W := Unit) (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack)
      atSix (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 h8k b
    (Johnson.RunOne.KeyRows23.shapeAt X) (plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt
        X).given.plan.samples collN (last₁At (oneAt X)) off₂N
    OnBytes.Model.Reading.gl (fun _ _ => Iff.rfl)
    (by rw [ebs]; rfl) (par25 P) rfl 7 d₁ d₂ rad25 hC h1 a1 a2 a3 a4 a5 (errPort (par25 P) rad25)
        (Nat.le_refl _)
    (readerOf (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par25 P).codes (shapeAt (par25 P)) (fun k => rad25
        k.val) 7 (fun k => k.val) (fun _ => 0))
    (readerIn (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par25 P).codes (shapeAt (par25 P)) (fun k => rad25
        k.val) 7 (fun k => k.val) (fun _ => 0) d₁)
    (words_fam (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (par25 P).codes (shapeAt (par25 P)) (fun k =>
        rad25 k.val) 7 (fun k => k.val) (fun _ => 0) _ d₁ d₂ _ _ (fun k => by
      have := k.isLt
      show k.val < d₁.trees.length
      omega))
    (hB 5 _ hrow) (fun y => ∀ j ∈ [4, 5], ShownAt (Fk X N P) atSix j y) (H b 7 d₁ d₂ hrow rfl htr)
    (yes25_seat X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN
        recBack) atSix (plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN
        (last₁At (oneAt X)) off₂N p5
      (by rw [eS, eC, ea]; exact plan25_full) rfl rfl cellOnly_collN
      (sendPiece (W := Unit) (F := fr₂ (DK.at frS.P.T.a)) (held b : Block (((Fk X N P).XiPub × (Fk X
          N P).S₁) × (Fk X N P).S₂) (Fk X N P).Cl) 7 d₁ d₂ (par25 P).coordinates (errPort (par25 P)
          rad25)) b hb' rfl)
    len5 ⟨0, by omega⟩ ⟨1, by omega⟩ smp50 smp51 rfl rfl
    (fun x' _ hS => tie4_scope (X := X) (N := N) (P := P) (decT := decN) (recOf := recBack) (Fr₂ :=
        fr₂ (DK.at frS.P.T.a)) hZ hP hm hX hp hwant DK hdata hDK x' (by
      have e := tieS50
      exact e ▸ hS))
    (fun x' _ hS => tie5_scope (X := X) (N := N) (P := P) (decT := decN) (recOf := recBack) (Fr₂ :=
        fr₂ (DK.at frS.P.T.a)) hZ hP hm hX hp hwant DK hdata hDK x' (by
      have e := tieS51
      exact e ▸ hS))
  exact ⟨⟨fun _ _ w => w, (seedMaps d₁ d₂ (par25 P).coordinates).err ((errPort (par25 P) rad25, ())
      : ℕ × Unit)⟩, K, Err.le_cap_of_below_inv 128 _ hbelow⟩

end

end LPFD

#print axioms LPFD.two_rounds₂
#print axioms LPFD.r2_2_new
#print axioms LPFD.r2_5_new
