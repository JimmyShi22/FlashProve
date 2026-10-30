-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OEnd.lean: the end of the shared chain, member 11 of the filled key thread: the
five sentences there, at any letter, and the step from border 11 to border 12.

  `no_half_at_end`     no half of the prover stands at the end's place
  `five_at_eleven`     the five sentences at member 11
  `steps_at_end`       at member 11 the chain's steps return
  `step_at_eleven`     from border 11 to border 12: the play and a yes of the end

The premises, with who pays them. hsource, scope: `key_sourced` with `later_sourced`. hk: the instance's key fits the
index. hsp: as in OAccepted.lean's head. hK, hE: the letter `Kp` at members 0 and 11: `keepsKey`. hN, hno, as in OStand.lean.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `five_at_eleven`, `step_at_eleven` bear this label; the rule is at its home, the head of
  Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread's pair is a premise, the sentences the ends.
- `RidesPastS` and `ExchangeS` at 11 ask nothing that the table leaves open: no item is owed there, and no open item reads
  the strings.
- That a stand at 11 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OStand
import E2E.KeyAcceptEleven
import E2E.KeyPlaysQuiet
import E2E.KeyBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block Grows)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source descriptionFromSource Xi)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey)
open AtPublicFiles.KeySharedQuiet (over_key fits_key quiet_key owes_seal ridesPast_seal)
open AtPublicFiles.KeyThread (plays_sealed behind₂)
open AtPublicFiles.KeyAcceptEleven (accepted_eleven)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyStandStep (step_pair)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO place_omega)
open AtPublicFiles.TableFilled (TR ttF)
open AtPublicFiles.Stops (NoStop chainStopAt_none)
open Desc.K14 (St)
open Desc.K14.Honest (Eight)

section
variable {S Cl V W X : Type} {Bk : ProverCoinCounts}

/-- **Where no half stands at a member's place, the chain's steps return.** -/
theorem steps_at_end (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (v : Option V)
    {b : Block S Cl} {hs : List (Placed V W X)} (hf : (hs.find? fun g => g.place == b.place) = none)
    (hl : b.oracles.length = b.rounds.length) : ∃ l, chainSteps Bk rows look v [b] hs = .ok l := by
  simp only [chainSteps, hf, hl, bne_self_eq_false, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

end

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- **No half of the prover stands at the end's place.** -/
theorem no_half_at_end (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    ((keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.find? fun g =>
      g.place == (H2K.JointK.keySharedEnd Xs.chains PF).place) = none := by
  have pa : (withTestsOnUAndOmega K₁ pU pO).onU.place = AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
  have pb : (withTestsOnUAndOmega K₁ pU pO).onOmega.place = AtPublicFiles.KeyBook.omegaTestPlace := place_omega
  have hl : (H2K.JointK.keySharedEnd Xs.chains PF).place = ⟨2, none, 11, .frame⟩ := rfl
  rw [hl, List.find?_eq_none]
  intro g hg hb
  have hm : g.place ∈ (keyProver (withTestsOnUAndOmega K₁ pU pO)).shared.map (·.place) :=
    List.mem_map_of_mem hg
  rw [keyProver_shared (withTestsOnUAndOmega K₁ pU pO) hsp, pa, pb, beq_iff_eq.1 hb] at hm
  exact absurd hm (by decide)

/-- **The five sentences at the end of the chain.** -/
theorem five_at_eleven {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hk : keyFits x.key QK.par.S.fold.index = true)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (hK : ∀ b ∈ [0, 11], ∀ s, Kp b s s)
    (hE : ∀ s s', Kp 11 s s' → s' = s)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11 ∧
      BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11 ∧
      ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11 ∧
      RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11 ∧
      AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said fall 11 := by
  have hn := no_half_at_end Xs K₁ (X₀ := X₀) hsp
  have h11 := end_member K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀
  have hO := over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x)
  have hQ := quiet_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x) hK
  refine ⟨playsS_of _ Said (plays_sealed _ h11 rfl rfl hn),
    behindS_of _ Said (behind₂ Xs Nr PF hsource scope hO hQ 11 (by decide)), ?_,
    ridesPastS_of _ Said (ridesPast_seal Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x) hE),
    acceptedS_of _ Said (accepted_eleven Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w₀ rc x hsource
      scope hk hn fall)⟩
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  rw [owes_seal Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x)] at hi
  cases hi

/-- **From a stand at 11 to a stand at 12**, at every list that fits: the end's play and its yes. -/
theorem step_at_eleven {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true) (hk : keyFits x.key QK.par.S.fold.index = true)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) (hK : ∀ b ∈ [0, 11], ∀ s, Kp b s s)
    (hE : ∀ s s', Kp 11 s s' → s' = s)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hN : SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11)
    (hno : NoStop (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀).hs)
    {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 11 k s m E)
    (ds : List Fmt.Drawn)
    (hd : drawsFit (H2K.JointK.keySharedEnd Xs.chains PF).rounds ds = true) :
    ∃ (y : List Played × Mid (Common W₀ Rc TableKey) X₀) (cols : List VerifiableInference.Desc.OpenedColumn),
      (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀).Moved
        (H2K.JointK.keySharedEnd Xs.chains PF) k m E ds y cols ∧
      ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said 12 k s (y.2.took cols)
        (E.add y.1) ∧
      (y.2.took cols).st.heard = m.st.heard ++ ds := by
  have hblk := end_member K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀
  have hpl : (descriptionFromSource Xs Nr PF).planOk = true := hsource.named.plan
  have hfit := fits_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x) hpl
  have hO := over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd (inK w₀ rc x)
  have hM : MadeNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) 11 :=
    made_next _ hfit (by rw [hO.bs]; exact (planOk_all hpl).2.1) 11
  obtain ⟨hP, hB, hX, hR, hA⟩ := five_at_eleven K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w₀ rc x B own₀
    hsource scope hk hsp hK hE Said (fun _ _ _ => none)
  obtain ⟨l, hsteps⟩ := steps_at_end (Bk := keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1)
    ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀).φ.sees m.st.input)
    (no_half_at_end Xs K₁ (X₀ := X₀) hsp) rfl
  obtain ⟨s', m', E', u', hh, hk', y, cols, hMv, rfl, rfl⟩ :=
    step_pair (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd (inK w₀ rc x) B own₀) Said (fun _ _ _ => none) hfit
      (by omega) hblk hN hP hA hB hX hR hM u hd (chainStopAt_none _ hno [_] _ _) hsteps rfl
  have hk'' : keepsAll (parKey Xs PF) (sentKey Xs PF) Kp 11 s s' := hk'
  unfold keepsAll at hk''
  rw [if_neg (by omega)] at hk''
  obtain rfl := hE s s' hk''
  exact ⟨y, cols, hMv, u', hh⟩

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.steps_at_end
#print axioms ProofFile.Honest.K12.AtKey.no_half_at_end
#print axioms ProofFile.Honest.K12.AtKey.five_at_eleven
#print axioms ProofFile.Honest.K12.AtKey.step_at_eleven
