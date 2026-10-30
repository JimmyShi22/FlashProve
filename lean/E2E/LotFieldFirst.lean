-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFieldFirst.lean: THE FIELD AND ONE STATE AT THE LAST BORDER OF THE KEY FILE's FIRST CHAIN: what the last
chain's door asks of the first chain (DoorAsks, E2E/LotFieldFirstLaw.lean), at the thread Th (E2E/FirstHSeat.lean) and
the letter walkedFirst (E2E/LotBegunFirst.lean), n = 19. The statements are ours to type, by the lot.

  LotOneStateFirst, lotOneStateFirst   OneState Th walkedFirst 19. NO PREMISE ON ANY MEMBER.
  LotFieldFirst, lotFieldFirst         at every state with the letter at border 19 and EVERY set of tables with Th.Hand 19:
                                       Th.Field [] 19 m E. Premises: LotOpensFirst's four; no part of the first chain stops, and
                                       PlaysS at the members 0 to 18, the members' own debt.
  LotDoorAsksFirst, lotDoorAsksFirst   DoorAsks, the four fields (one · state · field · next), and the letter at the walk's start,
                                       under the same.
  doorAsks_laid, field_at_length       THE SPENDERS' FORMS: the same at laid₁ … written out (door_pairs_key's, KeyLastTerm's), and
                                       the field at the border «(keyFileDescription Xs N Pl).first.blocksInOrder.length» (said_door's L₁).
  …AtValue                             the three at the offline prover's own senders and the index's reader: FirstPublic and
                                       «no part stops» are paid there; PlaysS stays.

By what. fits: fits₁ (E2E/KeyThreadFits.lean). opens, depths, «no own name is taken over»: lot_opens_first. The chain
begins at one state: by the thread's text. Begun is one-valued and its field is some []: the letter's text.

WHAT IT DOES NOT SAY. (1) hTrees is not paid: it is drawn from PlaysS at ALL nineteen members, which is a premise here; sixteen of
them are paid and 4, 10 (the lookups) and 15 (the ranges' test) are left: E2E/LotFieldFirstMeets.lean. (2) No stand of Th at border 19 is shown: where there is
none, OneState and the field are empty. (3) Q, w₀, rc, x stay letters, and at letters K, f too. (4) KeySourced needs protocolDataWellFormed.
(5) Nothing on the shared chain's twin (border 12). Nothing on soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotFieldFirstLaw
import E2E.LotOpensFirst
import E2E.LotBegunFirst
import E2E.LotFirstPublicAtValue
import E2E.KeyThreadFits
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Stops (NoStop)
open AtPublicFiles.LotField (DoorAsks doorAsks_walked enter_walked oneState_walked walked_field_plays)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **One state.** -/
def LotOneStateFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f →
    OneState (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19

/-- **The field.** -/
def LotFieldFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f → NoStop (keyProver K).first →
    (∀ b, b < 19 → PlaysS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b) →
    ∀ k m, walkedFirst Xs N Pl K f Q w₀ rc x 19 k m →
      ∀ E, (Th Xs N Pl K f Q w₀ rc x).Hand 19 k m E → (Th Xs N Pl K f Q w₀ rc x).Field [] 19 m E

/-- **What the door asks of the first chain.** -/
def LotDoorAsksFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f → NoStop (keyProver K).first →
    (∀ b, b < 19 → PlaysS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b) →
    DoorAsks (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19 ∧
      ∀ k, walkedFirst Xs N Pl K f Q w₀ rc x 0 k (startFirst K (some []) (inFirst w₀ rc x))

variable {K₀ Xs N Pl K f Q w₀ rc x}

/-- In scope the thread passes the tests with code, at its last border. -/
theorem fits_first19 {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (Th Xs N Pl K f Q w₀ rc x).fits 19 = true := by
  have h := AtPublicFiles.KeyThread.fits₁ (keyProver K) scope hs.named
    (AtPublicFiles.KeyThread.rest₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x)
  rw [(AtPublicFiles.KeyThread.lengths scope hs.named).1] at h
  exact h

/-- The chain begins at one state. -/
theorem begun_fun : ∀ k w hd s₀ s₁, (Th Xs N Pl K f Q w₀ rc x).begun k w hd s₀ →
    (Th Xs N Pl K f Q w₀ rc x).begun k w hd s₁ → s₀ = s₁ :=
  fun _ _ _ _ _ h h' => Eq.trans h (Eq.symm h')

variable (K₀ Xs N Pl K f Q w₀ rc x)

theorem lotOneStateFirst : LotOneStateFirst K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope hK hp
  obtain ⟨hO, hD, hT⟩ := lot_opens_first K₀ Xs N Pl K f Q w₀ rc x hs scope hK hp
  exact oneState_walked hT (fun b hb => hO b (by omega)) hD begun_fun
    fun _ m m' h h' _ _ => begun_one K w₀ rc x m m' h h'

theorem lotFieldFirst : LotFieldFirst K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope hK hp hstop hP k m hw E hE
  obtain ⟨hO, hD, -⟩ := lot_opens_first K₀ Xs N Pl K f Q w₀ rc x hs scope hK hp
  exact walked_field_plays (fits_first19 hs scope) (fun b hb => hO b (by omega)) hD hstop hP
    (fun _ m h => begun_field K w₀ rc x m h) (Nat.le_refl 19) hw E hE

theorem lotDoorAsksFirst : LotDoorAsksFirst K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hs scope hK hp hstop hP
  obtain ⟨hO, hD, hT⟩ := lot_opens_first K₀ Xs N Pl K f Q w₀ rc x hs scope hK hp
  exact ⟨doorAsks_walked (fits_first19 hs scope) hT (fun b hb => hO b (by omega)) hD begun_fun hstop
    hP rfl, fun k => enter_walked _ _ k⟩

variable {K₀ Xs N Pl K f Q w₀ rc x}

/-- **The spenders' form of the thread**: Th is laid₁ at the filling, the prover's own halves and the tables tbH, by unfolding. -/
theorem doorAsks_laid
    (D : DoorAsks (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19) :
    DoorAsks (AtPublicFiles.KeyThread.laid₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x (keyProver K).first
      (tbH Xs N Pl K f Q)) (walkedFirst Xs N Pl K f Q w₀ rc x) 19 := D

/-- **The spenders' form of the border**: the number of the first chain's members. -/
theorem field_at_length {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (D : DoorAsks (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) 19) :
    ∀ k e m E, ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x)
        (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl).first.blocksInOrder.length k e m E →
      (Th Xs N Pl K f Q w₀ rc x).Field [] (AtPublicFiles.AtFiles.keyFileDescription Xs N Pl).first.blocksInOrder.length m E := by
  rw [(AtPublicFiles.KeyThread.lengths scope hs.named).1]
  exact D.field

end

/-! ## At the real value -/

/-- **One state, at the offline prover's own senders and the index's reader.** -/
def LotOneStateFirstAtValue : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    OneState (Th d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x)
      (walkedFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc
        x) 19

theorem oneStateFirst_atValue : LotOneStateFirstAtValue := fun d Q w₀ rc x hs scope hK =>
  lotOneStateFirst _ d.source d.numbers d.later _ matrixReader Q w₀ rc x hs scope hK
    (firstPublic_atValue hs scope)

/-- **What the door asks of the first chain, there**: PlaysS at the nineteen members is what is left. -/
def LotDoorAsksFirstAtValue : Prop :=
  ∀ {Z files : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
    (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles files).EncodingRandomness) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles files).EncodingRandomness) (x : Xi),
    KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
    (∀ b, b < 19 →
      PlaysS (Th d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x)
        (walkedFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀
          rc x) b) →
    DoorAsks (Th d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc x)
      (walkedFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀ rc
        x) 19 ∧
      ∀ k, walkedFirst d.source d.numbers d.later (offlineValue (files := files) d) matrixReader Q w₀
        rc x 0 k (startFirst (offlineValue (files := files) d) (some []) (inFirst w₀ rc x))

theorem doorAsksFirst_atValue : LotDoorAsksFirstAtValue := fun d Q w₀ rc x hs scope hK hP =>
  lotDoorAsksFirst _ d.source d.numbers d.later _ matrixReader Q w₀ rc x hs scope hK
    (firstPublic_atValue hs scope) (AtPublicFiles.KeyValueHolds.noStop_value _ _ _ _ _ _ _ _ _ _ _ _ _).1 hP

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.fits_first19
#print axioms AtPublicFiles.FirstH.Lots.begun_fun
#print axioms AtPublicFiles.FirstH.Lots.lotOneStateFirst
#print axioms AtPublicFiles.FirstH.Lots.lotFieldFirst
#print axioms AtPublicFiles.FirstH.Lots.lotDoorAsksFirst
#print axioms AtPublicFiles.FirstH.Lots.doorAsks_laid
#print axioms AtPublicFiles.FirstH.Lots.field_at_length
#print axioms AtPublicFiles.FirstH.Lots.oneStateFirst_atValue
#print axioms AtPublicFiles.FirstH.Lots.doorAsksFirst_atValue
