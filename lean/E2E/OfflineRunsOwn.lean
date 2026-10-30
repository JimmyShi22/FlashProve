-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsOwn.lean: WHAT ONE SUB-PROTOCOL OWES for "every run returns" (`BlockPlays`, E2E/OfflineRunsForm.lean) AT THE KEY
FILE's OWN PROXIMITY TEST, place ⟨3, –, 2, K12⟩ of the last chain: from every state of the prover's run to which
columns have been handed (the field `opened` is some), at challenges that the test's rounds can draw, where the book
has lent, `play` returns. In scope, at the written book. The prover's side is the pair behind the guard (`proverSideOfGuardedSending`,
E2E/KeyProverSideOfOwnTest.lean).

  `stages_own`            the written place has two stages or more, and k = h + g at the first: kernel lines
  `number_own`            a sub-protocol of the last chain's flat list at that place is number 2
  `own_plays`             at every list hs with `proverSideOfGuardedSending …` at the place, the job's five letters free, Pre a letter that
                          gives the field
  `find_own`              the search at the place in `keyProver K`'s last list
  `own_plays_at_parts`    at `keyProver K`, K a letter with K.own that pair
  `own_plays_at_value`    at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean), Pre a letter
  `own_plays_form`        the same at the form `MidForm (startThird F) (roundsIn F.second.blocksInOrder j) own`: what
                          `BlocksPlay.second` asks at this place

By `blockPlays_k12_guarded` (E2E/OfflineRunsK12.lean). The seat: `seat_own`, `places_last` (E2E/KeyOwnSeat.lean). The place in scope:
`place_own` (E2E/KeyOwnJob.lean). On the plan: `planPlays_KW` (E2E/KeyOwnLines.lean: a kernel line at the written place, no
tree sent in front) through `planPlays_of_B` (K12/PlanPlaysAt.lean). The two parts' readers: `agree_at_W`
(E2E/KeyOwnAgree.lean), at every coins that the book lends, at every input and front.

Limits. In scope (`KeySourced`, `InScope`) and at the written sizes (`fullPub = some K₀`). That `play` returns; nothing on
what is played: at a front that is no run's the pair speaks at the door's default (`idleT12`). `BlockPlays` holds for
nothing where `chainSteps` at the sub-protocol does not return: that it returns at the last chain is not shown here.
Where the field is none the guarded pair's first move errs (`play_guarded_none`, K12/FieldGuardLift.lean): the premise on
Pre cannot be dropped. Nothing on the columns, on a decision, on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineRunsK12
import E2E.KeyOwnSeat
import E2E.KeyOwnLines
import E2E.KeyOwnAgree
import E2E.KeyOwnJob
import E2E.KeyValueHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (SendPub Ask)
open ProofFile.Honest.K12.AtProof (placeW)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces descriptionFromSource)
open OnBytes.Slice (GF)
open H2K.Member (piKWFull)
open H2K.Pub (sgOf)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver In1)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTest (sW)
open AtPublicFiles.KeyLay (pWK jobKWAt proverSideOfGuardedSending)
open AtPublicFiles.KeyLastChain (seat_own places_last planPlays_KW agree_at_W place_own members_own first_k_W)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- Two stages or more at the written place; k = h + g at the first. -/
theorem stages_own :
    ∃ s t rest, piKWFull.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g := by
  have h2 : 2 ≤ piKWFull.nums.stages.length := by decide +kernel
  have hk := first_k_W
  cases h : piKWFull.nums.stages with
  | nil =>
    rw [h] at h2
    exact absurd h2 (by decide)
  | cons s l =>
    cases l with
    | nil =>
      rw [h] at h2
      exact absurd h2 (by simp)
    | cons t rest =>
      rw [h] at hk
      exact ⟨s, t, rest, rfl, hk⟩

/-- A sub-protocol of the last chain's flat list at the own test's place is number 2. -/
theorem number_own (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (j : Nat)
    (b : Block (descriptionFromSource Xs N Pl).S₃ (descriptionFromSource Xs N Pl).Cl) (hj : (descriptionFromSource Xs N Pl).second.blocksInOrder[j]? = some b)
    (hp : b.place = placeW) : j = 2 := by
  have e : ((descriptionFromSource Xs N Pl).second.blocksInOrder.map (·.place))[j]? = some placeW := by
    rw [List.getElem?_map, hj]
    exact congrArg some hp
  rw [places_last Xs N Pl] at e
  match j, e with
  | 0, e =>
    simp only [List.getElem?_cons_zero] at e
    exact absurd (Option.some.inj e) (by decide)
  | 1, e =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at e
    exact absurd (Option.some.inj e) (by decide)
  | 2, _ => rfl
  | 3, e =>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at e
    exact absurd (Option.some.inj e) (by decide)
  | n + 4, e => simp at e

section Letters
variable {W₀ Rc Tr Y Wd V Pb : Type} {Z : PublicFiles} {K₀ : KeyPub} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (A : SendPub)
  (lift : Local W₀ Rc Xi Tr → Wd) (ask : Local W₀ Rc Xi Tr → Ask)

/-- **`play` returns at the own test**, from every state to which columns have been handed. -/
theorem own_plays {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (φ : Face V (Local W₀ Rc Xi Tr) Pb) (hs : List (Placed V (Local W₀ Rc Xi Tr) Y))
    (hhalf : (hs.find? fun g => g.place == (pWK Pl).place) =
      some (proverSideOfGuardedSending Xs N Pl JI JW A lift ask))
    (Pre : Mid (Local W₀ Rc Xi Tr) Y → Prop) (hopen : ∀ m, Pre m → m.opened.isSome = true) :
    ∀ (j : Nat) (b : Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl),
      (keyFileDescription Xs N Pl).second.blocksInOrder[j]? = some b → b.place = placeW →
      BlockPlays φ Bk 2 hs b Pre := by
  intro j b hj hp
  obtain rfl := number_own Xs N Pl j b hj hp
  obtain ⟨blk, hblk, hseat⟩ := seat_own Xs N Pl JI JW A lift ask
  obtain rfl : b = blk := Option.some.inj (hj.symm.trans hblk)
  subst hB
  have hJ : (jobKWAt Xs N Pl JI JW A lift ask).toRun.toTest.p = piKWFull := place_own hsrc scope
  obtain ⟨s, t, rest, hst₀, hk⟩ := stages_own
  have hst : (jobKWAt Xs N Pl JI JW A lift ask).toRun.toTest.p.nums.stages = s :: t :: rest := by
    rw [hJ]
    exact hst₀
  have P := planPlays_of_B (jobKWAt Xs N Pl JI JW A lift ask).toRun.toTest s (t :: rest) hst 0 (by
    rw [hJ]
    exact planPlays_KW)
  exact blockPlays_k12_guarded φ (keyBook K₀) 2 hs b
    (jobKWAt Xs N Pl JI JW A lift ask).toRun.toTest enterOwn leaveOwn hseat Pre s t rest hst hk
    hhalf P.plan P.sorts P.tables hopen
    fun k m c _ hc => agree_at_W K₀ hK (jobKWAt Xs N Pl JI JW A lift ask) hJ
      (members_own Xs N Pl JI JW A lift ask) (sW, JW.P.sent.size - 1) rfl _ _ c hc _ _

end Letters

section Parts
variable {W₀ Rc X₀ X' Wk Wd : Type} {Z : PublicFiles} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums}
  {Pl : LaterPlaces} {JI JW : ProofFile.Honest.K1.SendJob Wd X'} {A : SendPub}
  {lift : Local W₀ Rc Xi Unit → Wd} {ask : Local W₀ Rc Xi Unit → Ask}

/-- The search at the test's place in the last list. -/
theorem find_own (K : KeyParts W₀ Rc X₀ X' Wk) (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A lift ask) :
    ((keyProver K).second.find? fun g => g.place == (pWK Pl).place) =
      some (proverSideOfGuardedSending Xs N Pl JI JW A lift ask) := by
  have e : (K.own.place == (pWK Pl).place) = true := by
    rw [hown]
    show ((pWK Pl).place == (pWK Pl).place) = true
    exact beq_self_eq_true _
  show List.find? _ [K.own] = _
  simp only [List.find?, e]
  exact congrArg some hown

/-- **`play` returns at the own test, at `keyProver K`.** -/
theorem own_plays_at_parts {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) (K : KeyParts W₀ Rc X₀ X' Wk)
    (hown : K.own = proverSideOfGuardedSending Xs N Pl JI JW A lift ask)
    (Pre : Mid (Local W₀ Rc Xi Unit) X' → Prop) (hopen : ∀ m, Pre m → m.opened.isSome = true) :
    ∀ (j : Nat) (b : Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl),
      (keyFileDescription Xs N Pl).second.blocksInOrder[j]? = some b → b.place = placeW →
      BlockPlays .own Bk 2 (keyProver K).second b Pre :=
  own_plays Xs N Pl JI JW A lift ask hB hK hsrc scope .own _ (find_own K hown) Pre hopen

end Parts

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **`play` returns at the own test, at the offline prover's own senders.** -/
theorem own_plays_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (Pre : Mid (Local W₀ Rc Xi Unit) Unit → Prop) (hopen : ∀ m, Pre m → m.opened.isSome = true) :
    ∀ (j : Nat) (b : Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl),
      (keyFileDescription Xs N Pl).second.blocksInOrder[j]? = some b → b.place = placeW →
      BlockPlays .own Bk 2 (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).second
        b Pre :=
  own_plays_at_parts hB hK hs scope _ rfl Pre hopen

/-- **What `BlocksPlay.second` asks at the own test's place**, at the offline prover's own senders, at every
input. -/
theorem own_plays_form {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (own : Local W₀ Rc KeyInst Unit) :
    ∀ (j : Nat) (b : Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl),
      (keyFileDescription Xs N Pl).second.blocksInOrder[j]? = some b → b.place = (⟨3, none, 2, .K12⟩ : Place) →
      BlockPlays .own Bk 2 (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).second
        b (MidForm (startThird (keyFileDescription Xs N Pl)) (roundsIn (keyFileDescription Xs N Pl).second.blocksInOrder j) own) :=
  fun j b hj hp => own_plays_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB _
    (fun _ hm => hm.opened) j b hj hp

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.stages_own
#print axioms AtPublicFiles.OfflineRows.number_own
#print axioms AtPublicFiles.OfflineRows.own_plays
#print axioms AtPublicFiles.OfflineRows.find_own
#print axioms AtPublicFiles.OfflineRows.own_plays_at_parts
#print axioms AtPublicFiles.OfflineRows.own_plays_at_value
#print axioms AtPublicFiles.OfflineRows.own_plays_form
