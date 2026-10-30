-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandNineFull.lean: `stand_nine` (E2E/KeyStandNineAt.lean) at the library's three written full-size public
files, at the terms of E2E/KeyStandFull.lean, general in `tt`, `Kp`, `Said` and the start's field `o`; laid at the frame's `play`
in E2E/KeyStandPlayed.lean.

Main names.
  `stand_nine_full`: at `VerifierAndGoals.storedPublicFiles`, at every index, committer's coins, seed, `tt`, `Kp` with its two
    premises, `Said` and `o`, some lists of challenges fit at the six members with rounds; and at every
    run's coins and every such lists, where `Said` holds at the start and `SaidNext` at the first nine
    members, the shared thread stands at border 9 with `Said`, the stand has heard
    these lists, the seven items hold of the witness's words, o_u, o_omega, o_sp each has a sample row,
    and G_u and G_omega have the rows named.

What it is worth. As at `stand_full`: the seven items are said of the honest words; no `run`; the
halves of the proximity tests have no part, and by the text of `chainSteps` the next member would
refuse them; `pubKey Z₀` is made up. This end says nothing on tables: `stand_full`'s clause is of its own
`E`, at border 3. It fires nothing behind `Thr` at borders 12 or 19.

NOT IN FRONT OF A LAW OVER COINS: `stand_nine_full` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: as at `stand_nine`, which it calls, with `Vd` the true
one, keeping its letters: index, coins, seed and `k` are universally bound here. None: the bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandFull
import E2E.KeyStandNineAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyStandNineFull
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleTk idleRest kFull idleNm_tenant)
open AtPublicFiles.KeyStandNine (HasRow)
open AtPublicFiles.KeyStandNineAt (SaysNine stand_nine lists_nine)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open AtPublicFiles.KeyFiveFields (pubKey)
open Bind.ForProver (shapeOf oodSh Seed)
open AtPublicFiles.KeyFile (keyProver)

/-- **THE STATEMENT.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stand_nine_full (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub),
      KeySourced VerifierAndGoals.storedPublicFiles Xs Nr Pl ∧ fullPub = some K₀ ∧
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
        (tt : Nat → Coins (keyBook K₀) → Common Weights (ℕ → TableRand) TableKey → List Fmt.Drawn →
          Place × Table) (Kp : Nat → St → St → Prop)
        (Said : Nat → Coins (keyBook K₀) → Mid (Common Weights (ℕ → TableRand) TableKey) Unit → Prop)
        (o : Option (List VerifiableInference.Desc.OpenedColumn)),
        (∀ b ∈ [0, 11], ∀ s, Kp b s s) → (∀ s s', Kp 0 s s' → s' = s) →
        (∃ ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn,
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true)) ∧
        ∀ (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn),
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true) →
        Said 0 k (startAt (kFull Z₀ Xs Pl fc) o
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) →
        (∀ b, b < 9 → SaidNext (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) Said b) →
        ∃ (s : St) (m : Mid (Common Weights (ℕ → TableRand) TableKey) Unit) (E : Env),
          ThrS (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩))
            Said 9 k s m E ∧
          m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ∧
          SaysNine Xs Pl WitLens.words s ((threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).wit k m.st.input m.st.heard) ∧
          HasRow (num .oU) s ∧ HasRow (num .oOmega) s ∧ HasRow (num .oSp) s ∧
          (_root_.Desc.K14.Law.rowsOn s s.loc.gU).length = (parKey Xs Pl).par.S.fold.index.answers +
            (parKey Xs Pl).par.S.fold.columns + 1 ∧
          (_root_.Desc.K14.Law.rowsOn s s.loc.gOmega).length = 1 ∧
          0 < (parKey Xs Pl).par.S.fold.index.answers ∧ 0 < (parKey Xs Pl).par.S.fold.columns := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := full_made
  refine ⟨Xs, Nr, Pl, K₀, hs, hK₀, fun fc w₀ rc sd tt Kp Said o hKp hE =>
    ⟨?_, fun k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ h₁ h₂ h₄ h₅ h₇ h₈ hS hSN => ?_⟩⟩
  · exact lists_nine Xs Nr Pl K₀ (fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm
      (fun _ => idleMg) idleTk tt idleRest Kp (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl rfl rfl
  · obtain ⟨qr, qU, qO, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
      (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
    exact stand_nine Xs Nr Pl K₀ (fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm
      (fun _ => idleMg) idleTk tt idleRest Kp (fun _ => True) Said o id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full hK₀ sd rfl idleNm_tenant
      (fun _ _ _ _ => trivial) hKp hE trivial qr qU qO qw rfl rfl k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ h₁ h₂ h₄ h₅ h₇ h₈ hS hSN

end AtPublicFiles.KeyStandNineFull

#print axioms AtPublicFiles.KeyStandNineFull.stand_nine_full
