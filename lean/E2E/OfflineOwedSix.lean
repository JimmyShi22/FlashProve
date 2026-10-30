-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOwedSix.lean: the first clause of the field `owed` of `OwedRest` (E2E/OfflineClauses.lean) at every
row of the offline file's first chain but the test on the ranges, in that clause's own text, at a run
of `runC` that has returned.

  `SixLetters`           what is asked of the rows' letters c: nothing is asked at the two lookups and
                         the batching; at the three sendings the positions' condition follows from the
                         sender's bound on queried positions
  `SendersAtPars`        the three senders' public numbers are the description's own (`keyPars`)
  `owed_first_six`       the six rows, from `SendersBudAtRun` at the run. General in the description
  `owed_first_six_sourced`   the six rows at the key file's description, in scope, at the written book:
                         no premise on `bud`: the bound is `senderBud_sourced`
                         (Johnson/M1/KeySenderBud.lean)
  `value_senders_pars`, `owed_first_six_at_value`   the same at the offline prover's own senders

Conditional on the run's return, which is the field `runs`: where no run returns these sentences are
empty, and that one returns is not shown here. `SixLetters` is a condition on the letters c that whoever
lays c has to meet together with what `good` asks of the same c: at the lookups and the batching `good`
holds at every c; at the sendings it is stated at On := "true", bud := the sender's bound, which meets
`SixLetters`. Not the ranges' row, nor any row of the shared or the last chain. Nothing on any property.
-/
import E2E.OfflineOwedRows
import E2E.OfflineLookupRowsAtValue
import E2E.KeyBookThirdNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open OnBytes.SendSim.Seat (keyPars)
open OnBytes.M1 (SenderBudAtDraws senderBud_sourced)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver first_places)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub idxPlace msgPlace lookPlace rngPlace battPlace wPlace)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Rows
variable {W₀ Rc X₀ X Wk : Type} {Fx : FileDescription KeyInst} {Bk : ProverCoinCounts} {K : KeyParts W₀ Rc X₀ X Wk}
  {S : OfflineSimulators} {c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X}
  {H : Prover W₀ Rc KeyInst TableKey Unit X₀ X} {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk}
  {ρ : Draws} {r : RunC Fx}

/-- **What is asked of the letters at the six rows.** -/
structure SixLetters (K : KeyParts W₀ Rc X₀ X Wk)
    (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X) : Prop where
  idx : (c.first idxPlace).AsksBud K.idx.P
  msg : (c.first msgPlace).AsksBud K.msg.P
  look0 : (c.first (lookPlace 0)).AsksNothing
  look1 : (c.first (lookPlace 1)).AsksNothing
  batt : (c.first battPlace).AsksNothing
  w : (c.first wPlace).AsksBud K.w.P

/-- **The six rows, from the residue at the run.** -/
theorem owed_first_six (plan : Fx.planOk = true) (book : Bk.word Fx = none) (hA : K.AtPlaces)
    (hc : SixLetters K c)
    (h : runC Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (st : List (Nat × Nat × List UInt64)) (hb : SendersBudAtRun K r.run) :
    ∀ L ∈ (offlineRows Fx Bk K S c).mute.first, L.place ≠ rngPlace →
      L.owedAt Fx.first.blocksInOrder k 0
        (fun a => orRefused (midAtW Fx Bk ((offlineRows Fx Bk K S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called := by
  have hq : ∀ p, (p = lookPlace 0 ∨ p = lookPlace 1 ∨ p = battPlace) → (c.first p).AsksNothing := by
    rintro p (rfl | rfl | rfl)
    · exact hc.look0
    · exact hc.look1
    · exact hc.batt
  intro L hL hne
  have hpl : L.place ∈ (keyProver K).first.map (·.place) := by
    obtain ⟨L', hL', e⟩ := List.mem_map.1 hL
    obtain ⟨g, hg, e'⟩ := List.mem_map.1 hL'
    subst e'
    subst e
    exact List.mem_map.2 ⟨g, hg, rfl⟩
  rw [first_places K hA] at hpl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpl
  rcases hpl with q | q | q | q | q | q | q
  · exact owed_sender_rows plan book h st hA hc.idx hc.msg hc.w hb L hL (Or.inl q)
  · exact owed_sender_rows plan book h st hA hc.idx hc.msg hc.w hb L hL (Or.inr (Or.inl q))
  · exact owed_quiet_rows plan book h st hq L hL (Or.inl q)
  · exact owed_quiet_rows plan book h st hq L hL (Or.inr (Or.inl q))
  · exact absurd q hne
  · exact owed_quiet_rows plan book h st hq L hL (Or.inr (Or.inr q))
  · exact owed_sender_rows plan book h st hA hc.idx hc.msg hc.w hb L hL (Or.inr (Or.inr q))

end Rows

section Sourced
variable {W₀ Rc X₀ X Wk : Type}

/-- **The three senders' public numbers are the description's own.** -/
structure SendersAtPars (Xs : Source) (K : KeyParts W₀ Rc X₀ X Wk) : Prop where
  idx : ∃ y ∈ keyPars Xs, K.idx.P = y.1
  msg : ∃ y ∈ keyPars Xs, K.msg.P = y.1
  w : ∃ y ∈ keyPars Xs, K.w.P = y.1

/-- **The six rows at the key file's description, in scope, at the written book, at a run that has
returned.** No premise on `bud`. -/
theorem owed_first_six_sourced {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) {K : KeyParts W₀ Rc X₀ X Wk} (hA : K.AtPlaces)
    (hP : SendersAtPars Xs K) {S : OfflineSimulators}
    {c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X} (hc : SixLetters K c)
    {H : Prover W₀ Rc KeyInst TableKey Unit X₀ X} {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk}
    {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)} (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
      ρ = .ok r)
    (st : List (Nat × Nat × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place ≠ rngPlace →
      L.owedAt (keyFileDescription Xs N Pl).first.blocksInOrder k 0
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called := by
  subst hB
  have plan := hs.named.plan
  have book := AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  obtain ⟨r1, -, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have hin : ∀ p ∈ ([idxPlace, msgPlace, wPlace] : List Place),
      p ∈ AtPublicFiles.KeyBook.fullFirst.map (·.1) := by decide
  have hside : ∀ p, (p = idxPlace ∨ p = msgPlace ∨ p = wPlace) →
      p ∈ (keyFileDescription Xs N Pl).first.blocksInOrder.map (·.place) := by
    intro p hp
    rw [places_of_rows r1]
    rcases hp with rfl | rfl | rfl
    · exact hin _ (by simp)
    · exact hin _ (by simp)
    · exact hin _ (by simp)
  obtain ⟨y1, m1, e1⟩ := hP.idx
  obtain ⟨y2, m2, e2⟩ := hP.msg
  obtain ⟨y3, m3, e3⟩ := hP.w
  exact owed_first_six plan book hA hc h st
    (senders_bud_at_run plan book h hρ hA hside (e1 ▸ senderBud_sourced hs scope m1)
      (e2 ▸ senderBud_sourced hs scope m2) (e3 ▸ senderBud_sourced hs scope m3))

end Sourced

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- In scope the value's three senders are at the description's own numbers. -/
theorem value_senders_pars {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    SendersAtPars Xs (valueAt K' Xs N Pl f g inR d pU pO ent groups first) := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  obtain ⟨w, hw⟩ : ∃ w, OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape = some w :=
    Option.isSome_iff_exists.1 (by decide +kernel)
  have hl : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some w := by rw [el]; exact hw
  refine ⟨⟨_, List.mem_append_left _ List.mem_cons_self, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩, ?_⟩
  obtain ⟨a, b, y, hk, hy⟩ : ∃ a b y, keyPars Xs = [a, b, y] ∧
      (valueAt K' Xs N Pl f g inR d pU pO ent groups first).w.P = y.1 := by
    simp only [keyPars, hl]
    exact ⟨_, _, _, rfl, by
      show (AtPublicFiles.KeyValues.batchedRowsSending f Xs N).P = _
      have hl' : OnBytes.linMessageW (AtPublicFiles.KeyValues.oneOf Xs).lin = some w := hl
      unfold AtPublicFiles.KeyValues.batchedRowsSending AtPublicFiles.Key.wJob
      rw [hl']
      rfl⟩
  exact ⟨y, by rw [hk]; simp, hy⟩

/-- **The six rows at the offline prover's own senders.** -/
theorem owed_first_six_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    {S : OfflineSimulators}
    {c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit}
    (hc : SixLetters (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c)
    {H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit} {w₀ : W₀} {rc : Rc} {x : KeyInst}
    {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                 (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (st : List (Nat × Nat × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.first, L.place ≠ rngPlace →
      L.owedAt (keyFileDescription Xs N Pl).first.blocksInOrder k 0
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                     (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H) w₀ rc x k ρ a))
        r.run st r.called :=
  owed_first_six_sourced hs scope hK hB
    (value_atPlaces K' Xs N Pl f g inR d pU pO ent groups first hs scope)
    (value_senders_pars K' Xs N Pl f g inR d pU pO ent groups first hs scope) hc hρ h st

end Value

end AtPublicFiles.OfflineRows

#print axioms OnBytes.M1.senderBud_sourced
#print axioms AtPublicFiles.OfflineRows.owed_first_six
#print axioms AtPublicFiles.OfflineRows.owed_first_six_sourced
#print axioms AtPublicFiles.OfflineRows.value_senders_pars
#print axioms AtPublicFiles.OfflineRows.owed_first_six_at_value
