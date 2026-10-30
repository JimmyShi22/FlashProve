-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineLotsSpent.lean: WHAT THE OFFLINE HALF OF ZERO KNOWLEDGE SPENDS OF THE OFFLINE PROVER's DEBTS ON ACCEPTANCE (`TheLots`,
E2E/OfflineJoin.lean), as a structure of its own, and a member of `ThreadsP` with the threads' own invariants from it.

  `LotsSpent`          what is spent: the threads sit; the three chains' four debts (`OwesS`) and their letters' going on
                       (`SaidNext`); and of what a run owes: `ready` returns, the plan serves, `Enters₁`, `Enters₂`, the letters at
                       the two starts, `DoorBehindS`, at every coin of the book
  `lotsSpent_of_lots`  `TheLots` gives it
  `threads_at_spent`   at every input in the key file's relation: a seed, and at every coin of the book a member of `ThreadsP` at the
                       muted rows' prover whose invariants are `ThrS` of the three threads, and the plan serves

NO FIELD OF IT SAYS YES: not that a chain, a test, the door or the last test accepts (`firstYes`, `lastYes`, `testYesU`,
`testYesOmega`, `DoorYesS`, `FinYesS`), nor the description's test on the instance. `lotsSpent_of_lots` does spend the two shared
tests' yes: the one law at hand that gives the shared chain's debts (`shared_at_tied`, E2E/OfflineSharedAtTied.lean) takes it.

Limits. lotsSpent_of_lots gives a member of `LotsSpent` from `TheLots`; theLots_at_the_laid_table (E2E/OfflineClausesAtTheFiles.lean) is a member of that. At the written book `keyBook K₀`. Nothing on any property.
-/
import E2E.OfflineThreadSeams
import E2E.OfflineThreadsOfPays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) lotsSpentPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) lotsSpentValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) lotsSpentDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {d : OfflineDescription}

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **What is spent of `TheLots`.** NAMED PREMISES. lotsSpent_of_lots gives a member from `TheLots`. -/
structure LotsSpent (d : OfflineDescription) (U₁ : FirstFamily Z d (keyBook K₀))
    (U₃ : LastFamily Z d (keyBook K₀)) (S₁ S₃ : OwnLetter Z (keyBook K₀)) : Prop where
  sits : ∀ w x, TiedAt Z d w x → (descOf d).okStart x = true →
    Sits (descOf d) (proverOf Z d) (U₁ w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (U₃ w x)
  firstOwes : ∀ w x, TiedAt Z d w x → OwesS (U₁ w x) (S₁ w x)
  lastOwes : ∀ w x, TiedAt Z d w x → OwesS (U₃ w x) (S₃ w x)
  firstNext : ∀ w x, TiedAt Z d w x → ∀ b, SaidNext (U₁ w x) (S₁ w x) b
  lastNext : ∀ w x, TiedAt Z d w x → ∀ b, SaidNext (U₃ w x) (S₃ w x) b
  sharedOwes : ∀ w x, TiedAt Z d w x → OwesS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x)
  sharedNext : ∀ w x, TiedAt Z d w x → ∀ b, SaidNext (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) b
  run : ∀ w x (k : Coins (keyBook K₀)), TiedAt Z d w x →
    ∃ R, ready (descOf d) (keyBook K₀) (proverOf Z d) w.1 w.2.1 x k = .ok R ∧
      PlanServes (proverOf Z d) w.1 w.2.1 R ∧
      Enters₁ (descOf d) (proverOf Z d) (U₁ w x) w.1 w.2.1 x k R ∧
      Enters₂ (descOf d) (proverOf Z d) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) w.1 w.2.1 x k R ∧
      S₁ w x 0 k { R.start₁ (proverOf Z d) with opened := some [] } ∧
      sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x 0 k { R.start₂ (proverOf Z d) with opened := some [] } ∧
      DoorBehindS (descOf d) (proverOf Z d) (U₁ w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x) (U₃ w x) (S₁ w x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d w x)
        (S₃ w x) x k R

/-- **`TheLots` gives what is spent.** The shared chain's debts by `shared_at_tied`, which takes the two tests' yes. -/
theorem lotsSpent_of_lots {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hN : Function.Injective Nm.tenant) (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s)
    (hE : ∀ s s', Kp 0 s s' → s' = s) (hEnd : ∀ s s', Kp 11 s s' → s' = s)
    (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁ U₃ S₁ S₃) :
    LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁ U₃ S₁ S₃ where
  sits := fun w x ht hok => by
    have h := L.sits w x ht hok
    rw [bareSides_prover] at h
    exact h
  firstOwes := L.firstOwes
  lastOwes := L.lastOwes
  firstNext := L.firstNext
  lastNext := L.lastNext
  sharedOwes := fun w x ht => (shared_at_tied hd scope live hK₀ inRange ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w x
    ht hN hKp hE hEnd hC (fallsBy [] (descOf d).shared.blocksInOrder) (L.testU w x ht) (L.testOmega w x ht)
    (L.testYesU w x ht) (L.testYesOmega w x ht)).1
  sharedNext := fun w x ht => (shared_at_tied hd scope live hK₀ inRange ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ w x
    ht hN hKp hE hEnd hC (fallsBy [] (descOf d).shared.blocksInOrder) (L.testU w x ht) (L.testOmega w x ht)
    (L.testYesU w x ht) (L.testYesOmega w x ht)).2.1
  run := fun w x k ht => by
    obtain ⟨-, R, hR, hP, a₁, a₂, e₁, e₂, a₃, -, -⟩ :=
      L.run w x (coinOf (fun _ => 0) (fun _ => 0) k) ht
    exact ⟨R, hR, hP, a₁, a₂, e₁, e₂, a₃⟩

/-- **A member of `ThreadsP` with the threads' own invariants, from what is spent**, at the quantifiers of
`OwedRest.owed`: one seed, then every coin. -/
theorem threads_at_spent {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (scope : InScope Z = true)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁ U₃ S₁ S₃) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit) :
    ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
    ∃ e, TiedAt Z d (w₀, rc, e) x ∧ ∀ k : Coins (keyBook K₀), ∃ R,
      ready (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k = .ok R ∧
      PlanServes ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc R ∧
      ∃ T : ThreadsP (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k R,
        T.I₁ = ThrS (U₁ (w₀, rc, e) x) (S₁ (w₀, rc, e) x) ∧
        T.I₂ = ThrS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) ∧
        T.I₃ = ThrS (U₃ (w₀, rc, e) x) (S₃ (w₀, rc, e) x) := by
  intro w₀ rc x hrel
  obtain ⟨e, ht⟩ := tied_of_relation hs scope hrel
  have hok := okStart_of_tied hs.named scope ht
  rw [(provers_are_one (Z := Z) (d := d) (keyBook K₀) S c).2]
  refine ⟨e, ht, fun k => ?_⟩
  obtain ⟨R, hR, hP, a₁, a₂, e₁, e₂, a₃⟩ := L.run (w₀, rc, e) x k ht
  exact ⟨R, hR, hP, threadsOfPays (L.sits _ x ht hok) hs.named.plan (L.firstOwes _ x ht)
    (L.sharedOwes _ x ht) (L.lastOwes _ x ht) (L.firstNext _ x ht) (L.sharedNext _ x ht)
    (L.lastNext _ x ht) a₁ a₂ e₁ e₂ a₃, rfl, rfl, rfl⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.lotsSpent_of_lots
#print axioms AtPublicFiles.OfflineRows.threads_at_spent
