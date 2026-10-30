-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/UOwes.lean: what the frame's rule for a file asks of a chain's thread, at the key
file's shared chain: the five sentences of Honest/Thread/PaysS.lean at EVERY one of its twelve members, at one
thread, one letter `keeps` (`keepsKey`, UKeeps.lean) and one second condition.

  `five_at_front`     the five at member 0
  `five_in_eight`     the five at the members 1 to 8, the linear claim's own
  `five_at_member`    the five at every member
  `owes_at_key`       `OwesS`: the first four at every member
  `yes_at_key`        `YesS`: «it is accepted» at every member, at any falls

By what. Member 0: `plays_quiet₂`, `behind₂`, `exchange_of_nil`, `ridesPast_front`, `accepted_front₂` (E2E/). Members 1 to
8: `k14_asks`, `k14_behind` (Honest/K14/Asks.lean) at `asks_key` (E2E/KeyAsksKey.lean). Member 9: `five_at_key`
(UFive.lean). Member 10: `five_at_ten_key` (OStep.lean). Member 11: `five_at_eleven` (OEnd.lean).

Premises. The key is in scope (hsource, scope, hK₀). F: the linear claim's five fields at the input. hlin, hsend: the
parts' linear claim and sendings are at the thread's parameters. hN: the numbers' tenants are apart. hC: the
meaning's cells stand alone. hk: the instance's key fits the index. hfield: at border 10 the second condition
tells the field `opened`: the half of the test on G_omega plays behind a guard on it.

Limits.
- NOT IN FRONT OF A LAW OVER COINS (the rule: the head of Johnson/Bind/ForProver/FiveFieldsAt.lean): every sentence has
  the thread's pair as a premise.
- At one input, `inK w₀ rc x`; at the written key's size alone.
- That the invariant holds at any border at any run is not said here: UOStand.lean.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UFive
import Johnson.Desc.ProofFile.Honest.K12.AtKey.UKeeps
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OEnd
import E2E.KeyStandThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Xi)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey lettersKey plan_key)
open AtPublicFiles.KeySharedQuiet (CellsAlone over_key quiet_key owes_front ridesPast_front)
open AtPublicFiles.KeyStandOne (inK)
open AtPublicFiles.KeyAsksKey (asks_key)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.TableFilled (TR ttF arm_U)

variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Vd : Common W₀ Rc TableKey → Prop) (w₀ : W₀) (rc : Rc) (x : Xi)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (Said : ℕ → Coins (keyBook K₀) → ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (fall : ℕ → St → List Fmt.Drawn → Option String)

/-- The five sentences at one member. -/
abbrev FiveAt (b : ℕ) : Prop :=
  PlaysS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said b ∧
    BehindS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said b ∧
    ExchangeS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said b ∧
    RidesPastS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said b ∧
    AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said fall b

/-- **The five at member 0.** -/
theorem five_at_front {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (hC : ∀ v, CellsAlone (Mg₀ v)) :
    FiveAt K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall 0 := by
  have hO := over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)
  exact ⟨playsS_of _ Said (AtPublicFiles.KeyThread.plays_quiet₂ scope hsource.named _ hO.bs 0 (by decide)),
    behindS_of _ Said (AtPublicFiles.KeyThread.behind₂ Xs Nr PF hsource scope hO
      (quiet_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x) keepsKey_same) 0 (by decide)),
    exchangeS_of _ Said (AtPublicFiles.KeyThread.exchange_of_nil _ (owes_front Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
                (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x))),
    ridesPastS_of _ Said (ridesPast_front Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)
      (fun s s' h => (keepsKey_zero s s').1 h) hC),
    acceptedS_of _ Said (AtPublicFiles.AtFiles.accepted_front₂ Xs Nr PF _ hO.bs)⟩

include hK₀ in
/-- **The five at the members 1 to 8.** -/
theorem five_in_eight {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) {b : ℕ} (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    FiveAt K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall b := by
  have hap : [ProofFile.Honest.K14.place 1, ProofFile.Honest.K14.sendPlace 2, ProofFile.Honest.K14.place 4,
      ProofFile.Honest.K14.sendPlace 5, ProofFile.Honest.K14.place 7, ProofFile.Honest.K14.place 8,
      (withTestsOnUAndOmega K₁ pU pO).onU.place, (withTestsOnUAndOmega K₁ pU pO).onOmega.place].Nodup := by
    have pa : (withTestsOnUAndOmega K₁ pU pO).onU.place = AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
    have pb : (withTestsOnUAndOmega K₁ pU pO).onOmega.place = AtPublicFiles.KeyBook.omegaTestPlace :=
      AtPublicFiles.HalvesAreJobs.place_omega
    rw [pa, pb]
    decide
  obtain ⟨layO, h⟩ := asks_key Xs Nr PF K₀ (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ tk (ttF K₀ Xs K₁ B own₀) rest
    keepsKey Vd (inK w₀ rc x) hsource scope hK₀ F hlin hsend hap hN
  obtain ⟨hP, -, hX, hR, hAc⟩ := k14_asks h fall b h1 h8
  have hB := k14_behind h (cs := [])
    (fun _ _ _ => ⟨fun _ _ hc => absurd hc List.not_mem_nil, fun _ => trivial⟩)
    b h1 h8 (fun _ hy => absurd hy List.not_mem_nil) (fun _ hy => absurd hy List.not_mem_nil)
  exact ⟨playsS_of _ Said hP, behindS_of _ Said hB, exchangeS_of _ Said hX, ridesPastS_of _ Said hR,
    acceptedS_of _ Said hAc⟩

include hK₀ in
/-- **The five at every member of the key file's shared chain.** -/
theorem five_at_member {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀).colsTo 10 m E = .ok cols → m.opened = some cols)
    {b : ℕ} (hb : b < 12) : FiveAt K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall b := by
  have e : parKey Xs PF = QK := par_sourced hsource scope
  obtain ⟨layO, hQ⟩ := plan_key hsource scope
  have hsp : K₁.lin.S.sharedSplitNeeded = true := by
    rw [hlin]
    exact hQ.facts.two
  have hall : b = 0 ∨ (1 ≤ b ∧ b ≤ 8) ∨ b = 9 ∨ b = 10 ∨ b = 11 := by omega
  rcases hall with rfl | ⟨h1, h8⟩ | rfl | rfl | rfl
  · exact five_at_front K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall hsource scope hC
  · exact five_in_eight K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall hsource scope F hlin
      hsend hN h1 h8
  · exact five_at_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B (ttF K₀ Xs K₁ B own₀) e hQ
      hsend hsp keepsKey_nine own₀ (fun _ hτ => arm_U K₀ Xs K₁ B own₀ hτ) Said fall
  · exact five_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀ Said e hQ hsend
      hsp hfield keepsKey_ten fall
  · exact five_at_eleven K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd w₀ rc x B own₀ hsource scope hk hsp
      keepsKey_same (fun s s' h => (keepsKey_eleven s s').1 h) Said fall

include hK₀ in
/-- **What the chain's thread owes**: the first four sentences at every member. -/
theorem owes_at_key {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀).colsTo 10 m E = .ok cols → m.opened = some cols) :
    OwesS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said := by
  intro b hb
  rw [members_of_thread K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀] at hb
  obtain ⟨hP, hB, hX, hR, -⟩ := five_at_member K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said
    (fun _ _ _ => none) hsource scope F hlin hsend hN hC hk hfield hb
  exact ⟨hP, hB, hX, hR⟩

include hK₀ in
/-- **It is accepted at every member**, at any falls. -/
theorem yes_at_key {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF) (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest keepsKey Vd (inK w₀ rc x)).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = planData (parKey Xs PF)) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀).colsTo 10 m E = .ok cols → m.opened = some cols) :
    YesS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀) Said fall := by
  intro b hb
  rw [members_of_thread K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest keepsKey Vd (inK w₀ rc x) B own₀] at hb
  exact (five_at_member K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Vd w₀ rc x B own₀ Said fall hsource scope F hlin
    hsend hN hC hk hfield hb).2.2.2.2

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.five_at_front
#print axioms ProofFile.Honest.K12.AtKey.five_in_eight
#print axioms ProofFile.Honest.K12.AtKey.five_at_member
#print axioms ProofFile.Honest.K12.AtKey.owes_at_key
#print axioms ProofFile.Honest.K12.AtKey.yes_at_key
