-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UStep.lean: at a shared thread of the key file (`TU`, E2E/TableFilled.lean),
where the invariant holds at border 9 the half of the test on G_u plays, the verifier's step says yes, and the
invariant holds at border 10, at every list of challenges that fits the test; and the thread's own steps do
reach such a state. So the five sentences of UFive.lean are spent once.

  `no_stop_at_key`   no part of the thread's halves ever stops
  `returns_at_key`   at member 9 no part stops and the chain's steps return
  `step_at_key`      from border 9 to border 10: the play, the state behind it, a yes of the test on G_u
  `stand_ten_at_key`   at a key in scope, at the honest key's input, at every coin and every list that fits at
                     the seven members with rounds, at any second condition that the start meets and that is
                     carried: the invariant at 9, the play at member 9, the invariant at 10 behind that play
  `stand_ten_paid`   with no premise left: at the written key, at letters that say nothing, at the second
                     condition «the thread's own steps reach this state from the start», at SOME list that
                     fits at each member

By what. `step_pair` (E2E/KeyStandStep.lean) at `five_at_key`; `made_next` (Honest/Thread/MadeLaw.lean);
`lays_of_B` (K12/StepsReturn.lean); `stand_nine` (E2E/KeyStandNineAt.lean); `saidNext_walked` (E2E/WalkedFrom.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): statements at
  every coin; no measure is taken.
- A walk of the thread's steps, not a run of the frame: the first chain is not walked, and `WalkedFrom` binds the
  verifier's state and the tables afresh at each step.
- `stand_ten_at_key` asks that the meaning's item on the stored table holds everywhere (hPin), as `stand_nine`
  does: no real meaning meets that; a filling's own item at borders 0 and 1 is not paid here.
- Of the letter Kp it asks the clauses at members 0, 9 and 11 alone.
- `stand_ten_paid`: `VerifierAndGoals.storedPublicFiles` is three terms written in the library; `pubKey Z₀` is a made-up value; the parts
  beside the table, the index, the coins, the two sendings and the two halves say nothing.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UFive
import E2E.StandAtNine
import E2E.KeyStandStep
import E2E.WalkedFrom
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open ProofFile.Honest.K12.AtFile (keepsU)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi descriptionFromSource)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey sentKey randKey plan_key)
open AtPublicFiles.KeySharedQuiet (over_key fits_key)
open AtPublicFiles.KeyStandStep (step_pair)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandMember (keyOf)
open AtPublicFiles.KeyStandNineAt (stand_nine)
open AtPublicFiles.KeyFiveFields (pubKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyDoorNine (seat_nine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (onUOf onOmegaOf withTestsOnUAndOmega)
open AtPublicFiles.KeyPlaysAt (memsOf members_closed fresh_closed)
open AtPublicFiles.KeyDepthsAt (lays_U_at)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.HalvesAreJobs (pU pO find_U onU_is_job onOmega_is_job)
open AtPublicFiles.TableFilled (TU ttF arm_U)
open AtPublicFiles.PlaysAtNine (quiet_job)
open AtPublicFiles.StandAtNine (quiet_plain K1 K2 TS)
open AtPublicFiles.KeyStandFull (idleNm idleMg idleTk idleRest idleNm_tenant)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts idleWhere idle_quiet)
open AtPublicFiles.Stops (QuietHalf)
open Bind.ForProver (oodSh Seed)
open H2K.Member (piKUFull)

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include B in
/-- **No part of the thread's halves ever stops.** -/
theorem no_stop_at_key (hs : K₁.send = ⟨parKey Xs PF, 0⟩) :
    AtPublicFiles.Stops.NoStop (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hs := by
  have qU : QuietHalf (withTestsOnUAndOmega K₁ pU pO).onU := by
    show QuietHalf (onUOf K₁ pU)
    rw [onU_is_job Xs K₁ B hs]
    exact quiet_plain _
  have qO : QuietHalf (withTestsOnUAndOmega K₁ pU pO).onOmega := by
    show QuietHalf (onOmegaOf K₁ pU pO)
    rw [onOmega_is_job Xs K₁ B hs]
    exact quiet_job _
  exact (AtPublicFiles.KeyFile.noStopAll_keyProver
    { withTestsOnUAndOmega K₁ pU pO with
      rng := { (withTestsOnUAndOmega K₁ pU pO).rng with parts := [] }
      own := { (withTestsOnUAndOmega K₁ pU pO).own with parts := [] } }
    (fun _ hp => absurd hp List.not_mem_nil) qU qO (fun _ hp => absurd hp List.not_mem_nil)).2.1

include hK₀ B in
/-- **At member 9 no part stops and the chain's steps return.** -/
theorem returns_at_key (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (k : Coins (keyBook K₀)) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (ds : List Fmt.Drawn) :
    chainStopAt ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).φ.sees m.st.input)
        [H2K.JointK.keyGu PF] (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hs m.loc ds = none ∧
      ∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1)
        ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).φ.sees m.st.input) [H2K.JointK.keyGu PF]
        (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hs = .ok l := by
  have hseat := (seat_nine Xs Nr PF K₁ ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).2
  have hp : (JN Xs K₁ B).p = piKUFull := place_full
  have hmU : (JN Xs K₁ B).members = AtPublicFiles.KeyTest.jobFolded.members := by
    show memsOf (parKey Xs PF) = _
    rw [e]
    exact members_closed
  have hlays := lays_U_at K₀ hK₀ (JN Xs K₁ B) hp hmU fresh_closed.symm
  obtain ⟨st0, st1, st2, hst⟩ : ∃ a b r, (JN Xs K₁ B).p.nums.stages = a :: b :: r := by
    have h2 : 2 ≤ (JN Xs K₁ B).p.nums.stages.length := by
      rw [hp]
      exact AtPublicFiles.KeyPlaysAt.stages_two
    cases hh : (JN Xs K₁ B).p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a t =>
      cases t with
      | nil =>
        rw [hh] at h2
        simp only [List.length_cons, List.length_nil] at h2
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hfind : ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun q =>
      q.place == (JN Xs K₁ B).p.place) = some (proverSideOfProximityTest (JN Xs K₁ B)) := by
    rw [← hseat.place]
    exact find_U Xs K₁ B hs hsp
  obtain ⟨c, -, hsteps⟩ := lays_of_B (keyBook K₀) 1 (Or.inr rfl) (JN Xs K₁ B) st0 st1 st2
    hst hlays (H2K.JointK.keyGu PF) (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave hseat _ hfind k
    ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).φ.sees m.st.input)
  have hno := no_stop_at_key K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt hs
  exact ⟨AtPublicFiles.Stops.chainStopAt_none _ hno [_] _ _, _, hsteps⟩

include hK₀ in
/-- **From a stand at 9 to a stand at 10**, at every list that fits, with a yes of the test on G_u. -/
theorem step_at_key (hpl : (descriptionFromSource Xs Nr PF).planOk = true) (e : parKey Xs PF = QK)
    {layO : OnBytes.TreeLay} (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (hKp : ∀ s s', Kp 9 s s' ↔ keepsU pU s s') (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) = testTbl 1 (JN Xs K₁ B) own₀ 8 (fun _ _ _ => true) τ)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hN : SaidNext (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9)
    {k : Coins (keyBook K₀)} {s : St} {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : ThrS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 9 k s m E) (ds : List Fmt.Drawn)
    (hd : drawsFit (H2K.JointK.keyGu PF).rounds ds = true) :
    ∃ (s' : St) (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (cols : List VerifiableInference.Desc.OpenedColumn),
      (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).Moved (H2K.JointK.keyGu PF) k m E ds y cols ∧
        ThrS (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said 10 k s' (y.2.took cols) (E.add y.1) ∧
        (y.2.took cols).st.heard = m.st.heard ++ ds ∧ keepsU pU s s' := by
  have hblk := (seat_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w B).1
  have hfit := fits_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w hpl
  have hO := over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w
  have hM : MadeNext (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 :=
    made_next _ hfit (by rw [hO.bs]; exact (planOk_all hpl).2.1) 9
  obtain ⟨hP, hB, hX, hR, hA⟩ := five_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hQ hs hsp
    hKp own₀ htt Said (fun _ _ _ => none)
  obtain ⟨hstop, l, hsteps⟩ := returns_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e hs hsp
    k m ds
  obtain ⟨s', m', E', u', hh, hk, y, cols, hMv, rfl, rfl⟩ := step_pair (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) Said
    (fun _ _ _ => none) hfit (by omega) hblk hN hP hA hB hX hR hM u hd hstop hsteps rfl
  refine ⟨s', y, cols, hMv, u', hh, (hKp s s').1 ?_⟩
  have hk' : keepsAll (parKey Xs PF) (sentKey Xs PF) Kp 9 s s' := hk
  unfold keepsAll at hk'
  rw [if_neg (by omega)] at hk'
  exact hk'

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi) (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- **The thread stands at 9, the half of the test on G_u plays there, and behind its play the thread stands
at 10**: at a key in scope, at the honest key's input, at every coin and every list that fits at the seven
members with rounds, at any second condition that holds at the start and is carried up to member 9. -/
theorem stand_ten_at_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hKp₀ : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hKp : ∀ s s', Kp 9 s s' ↔ keepsU pU s s') (hVd : Vd (inK w₀ rc x))
    (qr : QuietHalf K'.rng) (qw : QuietHalf K'.own)
    (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (o : Option (List VerifiableInference.Desc.OpenedColumn))
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ ds₉ : List Fmt.Drawn)
    (hd₁ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[1]? = some blk →
      drawsFit blk.rounds ds₁ = true)
    (hd₂ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[2]? = some blk →
      drawsFit blk.rounds ds₂ = true)
    (hd₄ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[4]? = some blk →
      drawsFit blk.rounds ds₄ = true)
    (hd₅ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[5]? = some blk →
      drawsFit blk.rounds ds₅ = true)
    (hd₇ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[7]? = some blk →
      drawsFit blk.rounds ds₇ = true)
    (hd₈ : ∀ blk, (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).bs[8]? = some blk →
      drawsFit blk.rounds ds₈ = true)
    (hd₉ : drawsFit (H2K.JointK.keyGu PF).rounds ds₉ = true)
    (hS : Said 0 k (AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF (K2 Xs K' f g Z₀) f g) o (inK w₀ rc x)))
    (hSN : ∀ b, b < 10 → SaidNext (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) Said b) :
    ∃ (s s' : St) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀) (E : Env)
      (y : List Played × ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (cols : List VerifiableInference.Desc.OpenedColumn),
      ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) Said 9 k s m E ∧
        (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀).Moved (H2K.JointK.keyGu PF) k m E ds₉ y cols ∧
        ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) Said 10 k s' (y.2.took cols) (E.add y.1) ∧
        (y.2.took cols).st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ++ ds₉ ∧ keepsU pU s s' := by
  have hsend : (K1 Xs K' f g Z₀).send = ⟨parKey Xs PF, 0⟩ := rfl
  have qU : QuietHalf (K2 Xs K' f g Z₀).onU := by
    show QuietHalf (onUOf (K1 Xs K' f g Z₀) pU)
    rw [onU_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_plain _
  have qO : QuietHalf (K2 Xs K' f g Z₀).onOmega := by
    show QuietHalf (onOmegaOf (K1 Xs K' f g Z₀) pU pO)
    rw [onOmega_is_job Xs (K1 Xs K' f g Z₀) B hsend]
    exact quiet_job _
  obtain ⟨s, m, E, u, hh, -⟩ := stand_nine Xs Nr PF K₀ (K2 Xs K' f g Z₀) ℓ Nm Mg₀ tk
    (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀) rest Kp Vd Said o f g Z₀ w₀ rc x hs scope hK₀ sd hx hN hPin hKp₀ hE
    hVd qr qU qO qw AtPublicFiles.KeyPlaysAt.place_on AtPublicFiles.HalvesAreJobs.place_omega k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈
    hd₁ hd₂ hd₄ hd₅ hd₇ hd₈ hS (fun b hb => hSN b (by omega))
  have u9 : ThrS (TS Xs Nr K₀ K' ℓ Nm Mg₀ tk rest Kp Vd f g Z₀ w₀ rc x B own₀) Said 9 k s m E := u
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  obtain ⟨s', y, cols, hMv, u', hh', hy⟩ := step_at_key K₀ hK₀ Xs Nr (K1 Xs K' f g Z₀) ℓ Nm Mg₀ tk rest
    Kp Vd (inK w₀ rc x) B (ttF K₀ Xs (K1 Xs K' f g Z₀) B own₀) hs.named.plan (par_sourced hs scope) hQ
    rfl hQ.facts.two hKp own₀ (fun _ hτ => arm_U K₀ Xs (K1 Xs K' f g Z₀) B own₀ hτ) Said
    (hSN 9 (by omega)) u9 ds₉ hd₉
  exact ⟨s, s', m, E, y, cols, u9, hMv, u', by rw [hh', hh], hy⟩

end

/-- **No premise left.** At the written key, at parts and letters that say nothing beside the two halves, at
every index, committer's coins, seed, book's coins and first value of the field `opened`, with the second
condition «the thread's own steps reach this state from the start» (`WalkedFrom`, E2E/WalkedFrom.lean), at some
list that fits at each of the seven members with rounds: the invariant holds at border 9, the half of the test on
G_u plays there, and behind its play the invariant holds at border 10. So the statements above are about
something. -/
theorem stand_ten_paid (Z₀ : ProofFile.Pub) :
    ∃ (Xs : Source) (Nr : H2U.PlaceNums) (K₀ : KeyPub), KeySourced VerifierAndGoals.storedPublicFiles Xs Nr PF ∧
      fullPub = some K₀ ∧ ∃ B : Eight (parKey Xs PF),
      ∀ (fc : VerifiableInference.Desc.K3.Face) (w₀ : Weights) (rc : ℕ → TableRand)
        (sd : Seed (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) × ℕ) (k : Coins (keyBook K₀))
        (o : Option (List VerifiableInference.Desc.OpenedColumn)),
        let T := TS Xs Nr K₀ (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
              (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ())
            WitLens.words idleNm (fun _ => idleMg) idleTk idleRest keepsKey
            (fun _ => True) id id Z₀ w₀ rc
            ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨w₀, rc, sd⟩⟩ B ()
        let Said := WalkedFrom T fun _ m => m = AtPublicFiles.KeyStandOne.startAt (keyOf (pubKey Z₀ Xs.chains) Xs PF
                      (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc
                        idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀) id id) o
            (inK w₀ rc ⟨oodSh (Bind.ForProver.shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains)
              ⟨w₀, rc, sd⟩⟩)
        ∃ (s s' : St) (m : ProofFile.Honest.Mid (Common Weights (ℕ → TableRand) TableKey) Unit) (E : Env)
          (ds : List Fmt.Drawn)
          (y : List Played × ProofFile.Honest.Mid (Common Weights (ℕ → TableRand) TableKey) Unit)
          (cols : List VerifiableInference.Desc.OpenedColumn),
          ThrS T Said 9 k s m E ∧ T.Moved (H2K.JointK.keyGu PF) k m E ds y cols ∧
            ThrS T Said 10 k s' (y.2.took cols) (E.add y.1) ∧ keepsU pU s s' := by
  obtain ⟨Xs, Nr, Pl, hs⟩ := AtPublicFiles.AtFiles.key_sourced VerifierAndGoals.storedPublicFiles AtFullSide.Top.theLive_zFull
  obtain ⟨K₀, hK₀⟩ := AtPublicFiles.KeyBook.full_made
  have hPl : Pl = PF := AtPublicFiles.AtFiles.Full.later_sourced hs VerifierAndGoals.inScope_full
  subst hPl
  obtain ⟨layO, hQ⟩ := plan_key hs VerifierAndGoals.inScope_full
  obtain ⟨B⟩ := hQ.eight
  refine ⟨Xs, Nr, K₀, hs, hK₀, B, fun fc w₀ rc sd k o => ?_⟩
  intro T Said
  obtain ⟨qr, -, -, qw⟩ := idle_quiet (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit)
    (X := Unit) (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()
  have pa : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
      (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onU.place =
      AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
  have pb : (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit)
      (Wk := Unit) fc idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀).onOmega.place =
      AtPublicFiles.KeyBook.omegaTestPlace := AtPublicFiles.HalvesAreJobs.place_omega
  obtain ⟨ds₁, ds₂, ds₄, ds₅, ds₇, ds₈, h₁, h₂, h₄, h₅, h₇, h₈⟩ := AtPublicFiles.KeyStandNineAt.lists_nine Xs Nr PF K₀
    (K2 Xs (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc
      idleWhere ⟨fun _ _ => 0⟩ () () ()) id id Z₀) WitLens.words idleNm (fun _ => idleMg) idleTk _ idleRest
    keepsKey (fun _ => True) id id Z₀ w₀ rc _ hs VerifierAndGoals.inScope_full sd rfl pa pb
  obtain ⟨s, s', m, E, y, cols, u9, hMv, u10, -, hy⟩ := stand_ten_at_key Xs Nr K₀
    (fixedKeyParts (W₀ := Weights) (Rc := ℕ → TableRand) (X₀ := Unit) (X := Unit) (Wk := Unit) fc idleWhere
      ⟨fun _ _ => 0⟩ () () ()) WitLens.words idleNm (fun _ => idleMg) idleTk idleRest
    keepsKey (fun _ => True) id id Z₀ w₀ rc _ B () hs VerifierAndGoals.inScope_full hK₀ sd rfl
    idleNm_tenant (fun _ _ _ _ => trivial)
    keepsKey_same (fun s s' h => (keepsKey_zero s s').1 h) keepsKey_nine trivial
    qr qw Said o k ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ _ h₁ h₂ h₄ h₅ h₇ h₈ AtPublicFiles.KeyPlaysAt.fit_gu (.begun rfl)
    (fun b _ => saidNext_walked T _ b)
  exact ⟨s, s', m, E, _, y, cols, u9, hMv, u10, hy⟩

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.no_stop_at_key
#print axioms ProofFile.Honest.K12.AtKey.returns_at_key
#print axioms ProofFile.Honest.K12.AtKey.step_at_key
#print axioms ProofFile.Honest.K12.AtKey.stand_ten_at_key
#print axioms ProofFile.Honest.K12.AtKey.stand_ten_paid
