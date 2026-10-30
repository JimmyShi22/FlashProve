-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnJoinAtValue.lean: THE TIE OF THE WORDS AT THE LAST THREAD (LotOwnJoinTie.lean) AT THE PARTS THAT THE
OFFLINE PROVER's TEXT LAYS: `AtPublicFiles.KeyLay.withTests` (E2E/TheHonestProver.lean) over `withStoredColumnsAndPlan` over `withSendingsAndLookups`
(E2E/KeyArgumentsAt.lean, E2E/KeyFifteen.lean): NO PREMISE ON THE PARTS IS LEFT.

  `plans_alike_with_tests`, `senders_read_in_front_with_tests`   laying the four tests leaves the two sendings and the shared data
  `job_with_tests`                  the own test's job at the parts with the tests laid is the job at the parts
  `tie_at_last_thread_at_value`     THE TIE, behind `ThrS` at any letter and the lending

THE PREMISES, BY NAME: hs, scope, hK₀ (public) · hfit, hd (`third_shaped`'s; `last_done` has both) · hw: the thread's input is the
filling's instance. GONE against LotOwnJoinTie.lean: `SendersPlansAlike`, `SendersReadInFront`, the two places (LotOwnReadsAtValue.lean).

Limits. LotOwnJoinTie.lean's, all of them. The value's letters K', g, inR, dflt, weights, coins, the tests' letters pU, pO, entry, groups, first
and the filling's f, Q are free: nothing ties g to f or to weights here. NOT IN FRONT OF A LAW OVER COINS. That a stand is reached is not
said. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnJoinTie
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnReadsAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open OnBytes.Means (Words tableSize layoutOf)
open OnBytes.Slice (GE GF begun)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi FirstState descriptionFromSource)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Own (keyFits)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.AtFiles.HonestTerm (withStoredColumnsAndPlan)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyLastChain (wordsKey val₁Key mlKey threadOwn)
open AtPublicFiles.FirstH (fillH LaterFill HCells HTab)
open ProofFile.Honest.K14 (WitLens)
open ProofFile.Honest.K12.Light (plainMany)

section Tests
variable {W₀ Rc X₀ X Wk : Type} {K : KeyParts W₀ Rc X₀ X Wk} (Xs : Source) (Nr : H2U.PlaceNums)
  (Pl : LaterPlaces) (pU pO : P12) (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → GF)
  (groups : List (List ℕ)) (first : ℕ)

/-- Laying the four tests leaves the two sendings' plans and rides and the shared plan. -/
theorem plans_alike_with_tests (h : SendersPlansAlike K) :
    SendersPlansAlike (AtPublicFiles.KeyLay.withTests K Xs Nr Pl pU pO entry groups first) :=
  ⟨h.indexMasksNotices, h.indexMasksCodes, h.indexMasksRide, h.vectorWNotices, h.vectorWCodes,
    h.vectorWRide, h.sharedPlan⟩

/-- It leaves the two sendings' data and the point's round. -/
theorem senders_read_in_front_with_tests {N : OwnTestNumbers} (h : SendersReadInFront K N) :
    SendersReadInFront (AtPublicFiles.KeyLay.withTests K Xs Nr Pl pU pO entry groups first) N :=
  ⟨h.indexMasks, h.vectorW, h.point⟩

/-- The own test's job at the parts with the tests laid is the job at the parts. -/
theorem job_with_tests (K : KeyParts W₀ Rc X₀ X Wk) :
    jobAtKeyOwnTest (AtPublicFiles.KeyLay.withTests K Xs Nr Pl pU pO entry groups first) Xs Nr Pl =
      jobAtKeyOwnTest K Xs Nr Pl := rfl

end Tests

variable {W₀ Rc P₂ Wt₂ : Type} {K₀ : KeyPub} {Z : VerifierAndGoals.PublicFiles}
  (K' : KeyParts W₀ Rc Unit Unit WitK) (g : W₀ → Weights) (inR : W₀ → Bool) (dflt : W₀)
  (weights : W₀ → Weights) (coins : Rc → ℕ → TableRand)
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
  (pU pO : P12) (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → GF) (groups : List (List ℕ)) (first : ℕ)
  (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : ℕ → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) Unit → Prop)
  (Said₂ : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) Unit → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit HCells Unit HTab × Words Cb.Gl.E))
  (n₁ n₂ : ℕ) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) Unit)

local notation "KT" => AtPublicFiles.KeyLay.withTests
  (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl pU pO entry groups first

local notation "LH" => fillH Xs Nr Pl
  (AtPublicFiles.KeyLay.withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl pU
    pO entry groups first) f Q x

local notation "TO" => threadOwn Xs Nr Pl
  (AtPublicFiles.KeyLay.withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl pU
    pO entry groups first)
  (fillH Xs Nr Pl
    (AtPublicFiles.KeyLay.withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl
      pU pO entry groups first) f Q x)
  ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt
  (mlKey (val₁Key Xs (fillH Xs Nr Pl
    (AtPublicFiles.KeyLay.withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl
      pU pO entry groups first) f Q x))) n₁ n₂ Vd w dfltT dfltM

local notation "AG" => jobAtKeyOwnTest
  (AtPublicFiles.KeyLay.withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs Nr g inR dflt) weights coins) Xs Nr Pl pU
    pO entry groups first) Xs Nr Pl

/-- **THE TIE AT THE LAST THREAD, AT THE PARTS THAT THE OFFLINE PROVER's TEXT LAYS.** The premises by name: this file's head.
NOT IN FRONT OF A LAW OVER COINS: LotOwnJoinTie.lean's head. -/
theorem tie_at_last_thread_at_value (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀)
    (hfit : ∀ v, (threadKey Xs Nr Pl KT ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂).valid v →
      keyFits v.key QK.par.S.fold.index = true)
    (hd : d.1.2.lin = none) (hw : w = ⟨w₀, rc, x, ()⟩)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) Unit → Prop) :
    ∀ k st m E (c : RowCoins [(firstPart (AG).toRun.toTest :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit), restPart (AG).toRun.toTest]),
      ThrS TO Said 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (AG).toRun.toTest.p.place
        [(firstPart (AG).toRun.toTest : Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit),
          restPart (AG).toRun.toTest] 0 = .ok c →
      ∀ G, st.st.groups[st.loc.own]? = some G →
      ∀ o ∈ G.members.toList, ∀ pt, ∀ i < tableSize st.st o pt,
        wordsKey (val₁Key Xs LH) st (Thread.wit TO k m.st.input (m.st.heard ++ [])) o pt i =
          wordsAt (begun st.st st.loc.own G) (layoutOf st.st G)
            (plainMany AG m.st.input (frontOf m) (restCoins (AG).toRun.toTest c.2.1)) o pt i :=
  tie_at_last_thread_said Xs Nr Pl KT f Q ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt n₁
    n₂ Vd w dfltT dfltM hs scope hK₀ hfit hd hw
    (plans_alike_with_tests Xs Nr Pl pU pO entry groups first
      (plans_alike_at_value K' g inR dflt weights coins hs scope))
    (senders_read_in_front_with_tests Xs Nr Pl pU pO entry groups first
      (senders_read_in_front_at_value K' g inR dflt weights coins hs scope 18851))
    (place_of_index_masks_at_value (Xs := Xs) (Nr := Nr) (Pl := Pl) K' g inR dflt weights coins)
    (place_of_vector_w_at_value K' g inR dflt weights coins hs scope) Said

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.plans_alike_with_tests
#print axioms ProofFile.Honest.K12.AtKey.senders_read_in_front_with_tests
#print axioms ProofFile.Honest.K12.AtKey.job_with_tests
#print axioms ProofFile.Honest.K12.AtKey.tie_at_last_thread_at_value
