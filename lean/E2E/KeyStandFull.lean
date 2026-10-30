-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandFull.lean: `stand_three` (E2E/KeyStandMember.lean) at the library's three written full-size public
files, general in the table's letter `tt`, in `Kp`, in the letter `Said` and in the start's field `o`: the premises
left are on `Kp` and `Said`, and the value `Z₀`. E2E/KeyStandPlayed.lean lays `Said` at the frame's `play` and
`o` at none, where no premise is left. `pub_exists` shows a value of that type.

Why. Every premise but those on these letters is met at a term, so that the statement is about
something. What each term is worth matters more than that the statement closes: see below.

Main names.
  `idleNm`, `idleMg`, `idleTk`, `idleRest`: letters that say nothing of what this file is about: the
    item on the stored table and every item that the K14 maker does not lay are true; `kFull`: the
    prover: the table, index, coins and the two sendings real, `fixedKeyParts` for the rest.
  `pub_exists`: a value of `ProofFile.Pub`.
  `stand_full`: THE STATEMENT: at `VerifierAndGoals.storedPublicFiles`, at every index, committer's coins and seed, and at `tt`, `Kp`
    with its two premises, `Said` and `o`, some list of challenges fits; and at every run's coins and EVERY
    list that fits, where `Said` holds at the start and `SaidNext` at the first three members, the
    shared thread stands at border 3 with `Said`, at a stand which has heard that list; the state holds o_u's
    sample constraints, at least one, and they hold of the witness's words; and at the step of «send o_u» the first round that the step returned shows `treeTables` of
    `rowsU`. IT IS NO RUN OF THE FRAME (see E2E/KeyStandPlayed.lean).

What each term is worth. The sending «send o_u» and the quiet half at «LIN point» are the kind's own. THE
HALVES OF THE PROXIMITY TESTS HAVE NO PART, AND THE FIRST CHAIN'S SEND NOTHING: they are never reached
here: by the text of `chainSteps`, at these halves `run` and `ready` would refuse at a later member.
`VerifierAndGoals.storedPublicFiles` is three terms written in the library, at the second hash function, by a side library; no Lean
code ties them to files in a folder. `pubKey Z₀` is a made-up value. The witness's words are the honest words:
no item ties them to the tree that the half sent. Nothing of the first chain, W, the door, the last chain; no proximity
test. It fires none of the statements that stand behind `Thr` at the borders 12 or 19.

NOT IN FRONT OF A LAW OVER COINS: `stand_full` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: as at `stand_three`, which it calls, with `Vd` the true
one, keeping its letters: the index, the committer's coins, the seed and `k` are universally bound here; that a bound
letter is or is not the committer's term is not this file's to say. None: the bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyPartsIdle
import E2E.KeyPublic
import AtFullSide.Top.LiveAtFull
import AtFullSide.Top.HeadMemberAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyStandFull
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (SmpOwn)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (startAt inK)
open AtPublicFiles.KeyStandMember (keyOf stand_three)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open AtPublicFiles.KeyFiveFields (pubKey)
open Bind.ForProver (shapeOf oodSh Seed)

/-- **A value of the public part's type.** -/
theorem pub_exists : Nonempty ProofFile.Pub := by
  obtain ⟨-, -, Zp, -, -, -, -⟩ := AtFullSide.Top.headMember_zFull
  exact ⟨Zp⟩

/-- The table's numbers that say nothing. -/
def idleNm : NumbersS := ⟨0, fun m => (0, num m), (0, 0), (0, 0)⟩

theorem idleNm_tenant : Function.Injective idleNm.tenant := by
  intro a b h
  have h2 : num a = num b := congrArg Prod.snd h
  cases a <;> cases b <;> first | rfl | cases h2

/-- Meanings that say nothing. -/
def idleMg : MeaningS St Unit (Words Cb.Gl.E) :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ => True, fun _ _ _ _ _ => True,
    fun _ _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True,
    fun _ _ _ _ => True, fun _ _ _ => True, fun _ => True⟩

def idleTk {Bk : ProverCoinCounts} : Nat → Nat → Coins Bk → Common Weights (ℕ → TableRand) TableKey →
    List Fmt.Drawn → Place × Table :=
  fun _ _ _ _ _ => (⟨2, none, 0, .K14⟩, ⟨0, 0, fun _ i => i.elim0⟩)

def idleRest {Bk : ProverCoinCounts} : Coins Bk → Common Weights (ℕ → TableRand) TableKey → List Fmt.Drawn →
    Words Cb.Gl.E :=
  fun _ _ _ _ _ _ => 0

/-- The prover: the table, the index and the coins real, the two sendings the kind's own. -/
def kFull (Z₀ : ProofFile.Pub) (Xs : Source) (Pl : LaterPlaces) (fc : VerifiableInference.Desc.K3.Face) :
    KeyParts Weights (ℕ → TableRand) Unit Unit Unit :=
  keyOf (pubKey Z₀ Xs.chains) Xs Pl (fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () ()) id id

/-- **THE STATEMENT.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stand_full (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub),
      KeySourced VerifierAndGoals.storedPublicFiles Xs Nr Pl ∧ fullPub = some K₀ ∧
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
        (tt : Nat → Coins (keyBook K₀) → Common Weights (ℕ → TableRand) TableKey → List Fmt.Drawn →
          Place × Table) (Kp : Nat → St → St → Prop)
        (Said : Nat → Coins (keyBook K₀) → Mid (Common Weights (ℕ → TableRand) TableKey) Unit → Prop)
        (o : Option (List VerifiableInference.Desc.OpenedColumn)),
        (∀ b ∈ [0, 11], ∀ s, Kp b s s) → (∀ s s', Kp 0 s s' → s' = s) →
        (∃ ds₁ ds₂ : List Fmt.Drawn,
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
          (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true)) ∧
        ∀ (k : Coins (keyBook K₀)) (ds₁ ds₂ : List Fmt.Drawn),
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) →
        (∀ blk, (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true) →
        Said 0 k (startAt (kFull Z₀ Xs Pl fc) o
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) →
        (∀ b, b < 3 → SaidNext (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) Said b) →
        ∃ (s : St) (m : Mid (Common Weights (ℕ → TableRand) TableKey) Unit) (E : Env),
          ThrS (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩))
            Said 3 k s m E ∧
          m.st.heard = ds₁ ++ ds₂ ∧
          SmpOwn (num .oU) s ((threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
          (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).wit k m.st.input m.st.heard) ∧
          (∃ y, s.st.oracles[num .oU]? = some y ∧ 0 < y.sampleRows.size) ∧
          AtPublicFiles.KeyStandThree.PlayedSends (threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
                    (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
                    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)) Said k ds₂ m E (fun ps =>
                      AtPublicFiles.KeyStandThree.TieU (AtPublicFiles.KeySharedThread.parKey Xs Pl) (AtPublicFiles.KeySharedThread.sentKey Xs Pl)
                        WitLens.words
                        (holds2 (AtPublicFiles.KeySharedThread.parKey Xs Pl) (kFull Z₀ Xs Pl fc).weights
                          (AtPublicFiles.KeySharedThread.randKey (kFull Z₀ Xs Pl fc)) k
                          (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩))
                        (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩).key
                        (firstRv m.st.heard) ps
                        ((threadKey Xs Nr Pl (kFull Z₀ Xs Pl fc) WitLens.words idleNm (fun _ => idleMg)
                    (tableKey Xs Pl K₀ (kFull Z₀ Xs Pl fc) idleTk tt) idleRest Kp (fun _ => True)
                    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩)).wit k m.st.input m.st.heard)) := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := full_made
  refine ⟨Xs, Nr, Pl, K₀, hs, hK₀, fun fc w₀ rc sd tt Kp Said o hKp hE => ⟨?_, fun k ds₁ ds₂ h₁ h₂ hS hSN => ?_⟩⟩
  · exact AtPublicFiles.KeyStandMember.lists_key Xs Nr Pl K₀ (fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () ())
      WitLens.words idleNm (fun _ => idleMg) idleTk tt idleRest Kp (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl
      rfl rfl
  · obtain ⟨qr, qU, qO, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
      (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
    exact stand_three Xs Nr Pl K₀ (fixedKeyParts fc idleWhere ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm
      (fun _ => idleMg) idleTk tt idleRest Kp (fun _ => True) Said o id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full hK₀ sd rfl idleNm_tenant
      (fun _ _ _ _ => trivial) hKp hE trivial qr qU qO qw rfl rfl k ds₁ ds₂ h₁ h₂ hS hSN

end AtPublicFiles.KeyStandFull

#print axioms AtPublicFiles.KeyStandFull.pub_exists
#print axioms AtPublicFiles.KeyStandFull.idleNm_tenant
#print axioms AtPublicFiles.KeyStandFull.stand_full
