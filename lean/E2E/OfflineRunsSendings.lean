-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRunsSendings.lean: the share of "every run returns" (`OwedRest.runs`, E2E/OfflineClauses.lean)
at the three sendings of the key file's first chain (the index masks ⟨1,–,1⟩, the multiplicities ⟨1,–,2⟩,
W ⟨1,–,14⟩): what one sub-protocol owes by E2E/OfflineRunsForm.lean (`BlockPlays`), and the frame's own
`PlaysOn` (Honest/Law/ThreadC.lean), at `keyProver`'s own halves and at the offline prover's own senders
(`valueAt`, E2E/KeyValueHolds.lean).

  `first_finds`            the first half that is found at each of the three places is that sending's bare half
  `SendingAt`, `sending_at`   at a sub-protocol of the description's first list at one of the three places:
                           there is a job, one of the three, whose bare half is found there, whose numbers
                           give the sub-protocol's place, rounds and oracle messages, and which passes
                           `sendFits`
  `sendings_blockPlays`    **`BlockPlays` at the three**, at EVERY form Pre of the state in front: nothing of it is
                           used
  `sendings_playsOn`       **`PlaysOn` at the three**, from every A to every B that follows from A and
                           `K1.SendingEnd` (E2E/OfflineRunsSendingPlays.lean)
  `sendings_there`         A TEST OF EMPTINESS: the list has a sub-protocol at each of the three places
  `sendings_blockPlays_at_value`, `sendings_playsOn_at_value`   the same at `valueAt`
  `sendings_first_at_rows`   the three's share of `BlocksPlay.first`, in that field's own form, at the prover of
                           the muted rows at the value

Limits. `BlockPlays` and `PlaysOn` have the lending as a premise (`chainSteps` at the one sub-protocol has
returned): that the key's book lends these three rows is not shown here, and where it does not both are
met emptily. "It plays": play returns and every message has the declared shape. IT IS NO COMPLETENESS:
nothing says that the verifier's step accepts. Nothing leans on the owners' "fresh", on the truth of the
witness or on the verifier's state. On hiding nothing is said. Nothing on any property.
-/
import E2E.OfflineRunsForm
import E2E.OfflineRunsSendingPlays
import E2E.OfflineSendingRowsAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open OnBytes.SendSim.Seat (keyPars key_member)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (OneFull idxPlace msgPlace wPlace)
open AtPublicFiles.KeyValues (WitK oneOf)
open AtPublicFiles.KeyValueHolds (valueAt atPlaces_value)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Letters
variable {W₀ Rc Wk : Type}

/-- **The first half found at each of the three places is that sending's bare half.** -/
theorem first_finds (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == idxPlace) = some (K1.proverSideOfSending K.idx) ∧
      ((keyProver K).first.find? fun g => g.place == msgPlace) = some (K1.proverSideOfSending K.msg) ∧
      ((keyProver K).first.find? fun g => g.place == wPlace) = some (K1.proverSideOfSending K.w) := by
  have hp := AtPublicFiles.KeyFile.first_places K hA
  rw [AtPublicFiles.KeyFile.keyProver_first] at hp ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.find?_cons, p1]
    rfl
  · simp only [List.find?_cons, p1, p2]
    rfl
  · simp only [List.find?_cons, p1, p2, p3, p4, p5, p6, p7]
    rfl

/-- What `K1.sending_plays` and `K1.sending_playsOn` ask of a sub-protocol, a list of halves and a job. -/
structure SendingAt {S Cl V W X : Type} (hs : List (Placed V W X)) (b : Block S Cl)
    (J : K1.SendJob W X) : Prop where
  shape : b.place = J.P.place ∧ b.rounds = VerifiableInference.Desc.K1.rounds J.P ∧
    b.oracles = VerifiableInference.Desc.K1.oracles J.P
  found : (hs.find? fun g => g.place == b.place) = some (K1.proverSideOfSending J)
  fits : K1.sendFits J.P J.ride = true

/-- **At a sub-protocol of the first list at one of the three places** the job of that place is such. -/
theorem sending_at {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs)
    (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs) (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N)
    (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace) :
    ∃ J ∈ [K.idx, K.msg, K.w], SendingAt (keyProver K).first b J := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  obtain ⟨t1, t2, t3⟩ := sendings_fit (W₀ := W₀) (Rc := Rc) (X := Unit) Xs one N f
  obtain ⟨g1, g2, g3⟩ := first_finds K hA
  have at_job : ∀ (J : K1.SendJob (Local W₀ Rc KeyInst Unit) Unit),
      (∃ x ∈ keyPars Xs, J.P = x.1) → b.place = J.P.place →
      ((keyProver K).first.find? fun g => g.place == J.P.place) = some (K1.proverSideOfSending J) →
      K1.sendFits J.P J.ride = true → SendingAt (keyProver K).first b J := by
    rintro J ⟨x, hx, hP⟩ hq hg ht
    obtain ⟨hr, ho⟩ := (key_member Xs N Pl x hx).2 b hb (hP ▸ hq)
    exact ⟨⟨hq, hP ▸ hr, hP ▸ ho⟩, hq ▸ hg, ht⟩
  rcases hp with hp | hp | hp
  · refine ⟨K.idx, by simp, at_job _ ?_ (hp.trans hA.idx.symm) ?_ ?_⟩
    · rw [hi]
      exact keyIdx_pars Xs
    · rw [hA.idx]
      exact g1
    · rw [hi]
      exact t1
  · refine ⟨K.msg, by simp, at_job _ ?_ (hp.trans hA.msg.symm) ?_ ?_⟩
    · rw [hm]
      exact keyMsg_pars Xs f
    · rw [hA.msg]
      exact g2
    · rw [hm]
      exact t2
  · refine ⟨K.w, by simp, at_job _ ?_ (hp.trans hA.w.symm) ?_ ?_⟩
    · rw [hw]
      exact keyW_pars Xs one N f
    · rw [hA.w]
      exact g3
    · rw [hw]
      exact t3

/-- **`BlockPlays` at the three sendings**, at every book and every form of the state in front. -/
theorem sendings_blockPlays {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts) (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs)
    (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs) (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N)
    (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace)
    (Pre : Mid (Local W₀ Rc KeyInst Unit) Unit → Prop) :
    BlockPlays .own Bk 0 (keyProver K).first b Pre := by
  obtain ⟨J, -, hJ⟩ := sending_at hs scope f K hA hi hm hw b hb hp
  intro k m ds l _ hd _ hl
  obtain ⟨c, d₀, d₁, -, -, hy⟩ := K1.sending_plays J hJ.shape hJ.found hJ.fits hl m ds hd
  exact ⟨_, hy⟩

/-- **`PlaysOn` at the three sendings**, from every A to every B that follows from A and what holds
behind a sending's block, where the block's own step returns. -/
theorem sendings_playsOn {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts) (f : W₀ → Weights)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hi : K.idx = AtPublicFiles.KeyValues.indexMaskSending Xs)
    (hm : K.msg = AtPublicFiles.KeyValues.multiplicitiesSending f Xs) (hw : K.w = AtPublicFiles.KeyValues.batchedRowsSending f Xs N)
    (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace)
    {A B : Coins Bk → (keyFileDescription Xs N Pl).S₁ → Mid (Local W₀ Rc KeyInst Unit) Unit → Env → Prop}
    (H : ∀ k s m E ds l m' s' n, A k s m E → drawsFit b.rounds ds = true →
      K1.SendingEnd b m m' E (E.add l) ds l → b.step 0 s (roundsOf l) [] = .ok (s', n) →
      B k s' m' (E.add l)) :
    PlaysOn .own Bk 0 0 (keyProver K).first b A B := by
  obtain ⟨J, -, hJ⟩ := sending_at hs scope f K hA hi hm hw b hb hp
  exact K1.sending_playsOn J hJ.shape hJ.found hJ.fits H

/-- **A TEST OF EMPTINESS.** In scope the first list has a sub-protocol at each of the three places. -/
theorem sendings_there {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (p : Place)
    (hp : p = idxPlace ∨ p = msgPlace ∨ p = wPlace) :
    ∃ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, b.place = p := by
  obtain ⟨-, er, el, ei, ec⟩ := five_sourced hs scope
  have one : OneFull (oneOf Xs) := ⟨ec, ei, er, el⟩
  rcases hp with rfl | rfl | rfl
  · obtain ⟨x, hx, hP⟩ := keyIdx_pars (W₀ := Unit) (Rc := Unit) (X := Unit) Xs
    obtain ⟨b, hb, hq⟩ := (key_member Xs N Pl x hx).1
    exact ⟨b, hb, hq.trans (hP ▸ rfl)⟩
  · obtain ⟨x, hx, hP⟩ := keyMsg_pars (W₀ := Weights) (Rc := Unit) (X := Unit) Xs (fun w => w)
    obtain ⟨b, hb, hq⟩ := (key_member Xs N Pl x hx).1
    exact ⟨b, hb, hq.trans (hP ▸ rfl)⟩
  · obtain ⟨x, hx, hP⟩ := keyW_pars (W₀ := Weights) (Rc := Unit) (X := Unit) Xs one N (fun w => w)
    obtain ⟨b, hb, hq⟩ := (key_member Xs N Pl x hx).1
    exact ⟨b, hb, hq.trans (hP ▸ (keyW_numbers (Rc := Unit) (X := Unit) Xs one N _).2.2.1)⟩

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- In scope the value bears the first chain's seven places. -/
theorem value_bears_places {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtPlaces := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  obtain ⟨w, hw⟩ := written_message
  exact atPlaces_value K' Xs N Pl f g inR d pU pO ent groups first (by
    show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
    rw [el, hw]
    rfl)

/-- **`BlockPlays` at the three sendings, at the offline prover's own senders.** -/
theorem sendings_blockPlays_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace)
    (Pre : Mid (Local W₀ Rc KeyInst Unit) Unit → Prop) :
    BlockPlays .own Bk 0
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first b Pre :=
  sendings_blockPlays hs scope Bk f _
    (value_bears_places K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl rfl b hb hp Pre

/-- **`PlaysOn` at the three sendings, at the offline prover's own senders.** -/
theorem sendings_playsOn_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace)
    {A B : Coins Bk → (keyFileDescription Xs N Pl).S₁ → Mid (Local W₀ Rc KeyInst Unit) Unit → Env → Prop}
    (H : ∀ k s m E ds l m' s' n, A k s m E → drawsFit b.rounds ds = true →
      K1.SendingEnd b m m' E (E.add l) ds l → b.step 0 s (roundsOf l) [] = .ok (s', n) →
      B k s' m' (E.add l)) :
    PlaysOn .own Bk 0 0
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first b A B :=
  sendings_playsOn hs scope Bk f _
    (value_bears_places K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl rfl b hb hp H

/-- **The three sendings' share of `BlocksPlay.first`** (E2E/OfflineRunsForm.lean), in that field's own
form: at the prover of the muted rows at the value, whatever the simulators S, the rows' letters c, the
prover H whose other fields are taken, and the run's input. -/
theorem sendings_first_at_rows {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (own : Local W₀ Rc KeyInst Unit) :
    ∀ j b, (keyFileDescription Xs N Pl).first.blocksInOrder[j]? = some b →
      (b.place = idxPlace ∨ b.place = msgPlace ∨ b.place = wPlace) →
      BlockPlays .own Bk 0 ((offlineRows (keyFileDescription Xs N Pl) Bk
          (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H).first b
        (MidForm startNone (roundsIn (keyFileDescription Xs N Pl).first.blocksInOrder j) own) := by
  intro j b hj hp
  rw [prover_mute, offlineRows_prover_at]
  exact sendings_blockPlays_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope Bk b
    (List.mem_of_getElem? hj) hp _

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.first_finds
#print axioms AtPublicFiles.OfflineRows.SendingAt
#print axioms AtPublicFiles.OfflineRows.sending_at
#print axioms AtPublicFiles.OfflineRows.sendings_blockPlays
#print axioms AtPublicFiles.OfflineRows.sendings_playsOn
#print axioms AtPublicFiles.OfflineRows.sendings_there
#print axioms AtPublicFiles.OfflineRows.value_bears_places
#print axioms AtPublicFiles.OfflineRows.sendings_blockPlays_at_value
#print axioms AtPublicFiles.OfflineRows.sendings_playsOn_at_value
#print axioms AtPublicFiles.OfflineRows.sendings_first_at_rows
