-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsRanges.lean: WHAT ONE SUB-PROTOCOL OWES for "every run returns" (`BlockPlays`, E2E/OfflineRunsForm.lean) AT THE KEY
FILE's TEST ON THE RANGES, place ⟨1, –, 5, K12⟩ of the first chain: from EVERY state of the prover's run (Pre is a
free letter; nothing is asked of it), at challenges that the test's rounds can draw, where the book has lent,
`play` returns. In scope, at the written book.

  `agree_ranges`            the two parts' readers agree (`Agree`), at every coins that the book lends them, at every
                            input and front: from the book's ties (`ties_ranges`, a kernel line) and `jobRng_rows`
  `ranges_plays`            at every list hs with `proverSideOfProximityTest (rangesTestJob …)` at the place: at every sub-protocol of kind K12
                            of the first chain's flat list (there is one: `key_sits_row`)
  `find_ranges`             the search at the place in `keyProver K`'s first list, where K bears the seven places
  `ranges_plays_at_parts`   at `keyProver K`, K a letter with K.rng the job's half
  `ranges_test`             THE END: the field `rangesTest` of `KeyOthersPlay` (E2E/OfflineRunsKey.lean), in its own type:
                            `PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own rngPlace`
  `ranges_plays_at_value`   at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean)
  `ranges_lent_at_value`    A TEST OF EMPTINESS: there, at all coins, `chainSteps` at the sub-protocol returns
                            (`lends_ranges`), so the premise of `BlockPlays` is met at every run's coins
  `ranges_there`            A TEST OF EMPTINESS: the first chain's flat list has a sub-protocol of kind K12
  `ranges_first_at_rows`    the test's share of `BlocksPlay.first`, in that field's own form: at the prover of the
                            muted rows at the value, from `MidForm startNone …`

By `blockPlays_k12` (E2E/OfflineRunsK12.lean). On the plan: `seatOf_rngEntry`, `stages_KRJ` (E2E/KeyRangesK12.lean),
`planPlays_KR` (K12/PlanPlaysAt.lean: a kernel line at the written place).

Limits. In scope (`KeySourced`, `InScope`) and at the written sizes (`fullPub = some K₀`). That `play` returns; nothing on
what is played: behind a refusal, or at a front that is no run's, the pair speaks at `recRanges`' default. Nothing on
the columns, on a decision, on completeness, on soundness or on what is hidden.
-/
import E2E.OfflineRunsK12
import E2E.OfflineRunsKey
import E2E.KeyRangesLends
import E2E.KeyValueHolds
import E2E.OfflineSides
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces enterRanges leaveRanges enterAndAsk
  rangesParams)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open H2K.JointK (rngEntry key_sits_row)
open H2K.Member (piKRFull)
open H2K.Pub (sgOf)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver In1)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace)
open AtPublicFiles.KeyTest (sMsg)
open AtPublicFiles.KeyThread (rangesTestJob jobRng_rows seatOf_rngEntry stages_KRJ place_sourced lends_ranges)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyValueHolds (valueAt atPlaces_value)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section Letters
variable {W₀ Rc X' : Type} {Z : PublicFiles} {K₀ : KeyPub} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The two parts' readers agree**, at every coins that the book lends them, input and front. -/
theorem agree_ranges (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (k : Coins (keyBook K₀))
    (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
      restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c)
    (w : Local W₀ Rc Xi Unit) (fr : Front X') :
    Agree (rangesTestJob (X' := X') Xs N Pl entry groups first) w fr
      (rangesTestJob (X' := X') Xs N Pl entry groups first).s₀
      (firstRd (rangesTestJob (X' := X') Xs N Pl entry groups first) c.1)
      (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1) := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  have hJ : (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).p = piKRFull := rfl
  obtain ⟨s₁, t₁, rest₁, hst, hk⟩ :=
    stages_KRJ (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first) hJ
  have hk' : (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀.k =
      (sgOf (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀).h +
        (sgOf (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀).g := by
    unfold TestJob.s₀
    rw [hst]
    exact hk
  exact agree_of_ties' _ (sMsg, 1) rfl (keyBook K₀) _ _ c hc _ _ (ties_ranges K₀ hK) hk'
    fun mem mem' h => congrArg _ (jobRng_rows Xs H2K.Member.nKRFull Pl entry groups first _ _ mem
      mem' h)

/-- **`play` returns at the test on the ranges**, from every state. -/
theorem ranges_plays {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (Pre : Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, b.place.kind = .K12 → BlockPlays .own Bk 0 hs b Pre := by
  intro b hb hkind
  obtain rfl := (key_sits_row Xs N Pl).ranges.2.2 b hb hkind
  subst hB
  have hJ : (rangesTestJob (X' := X') Xs N Pl entry groups first).p = piKRFull :=
    place_sourced hsrc scope
  obtain ⟨s, t, rest, hst, hk⟩ := stages_KRJ (rangesTestJob (X' := X') Xs N Pl entry groups first) hJ
  have P := planPlays_KR (rangesTestJob (X' := X') Xs N Pl entry groups first) hJ rfl s (t :: rest) hst
  exact blockPlays_k12 .own (keyBook K₀) 0 hs (rngEntry Xs.Y.k.oneTime N)
    (rangesTestJob (X' := X') Xs N Pl entry groups first)
    (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N)) leaveRanges
    (seatOf_rngEntry Xs.Y.k.oneTime N _ rfl) Pre s t rest hst hk hhalf P.plan P.sorts P.tables
    fun k m c _ hc => agree_ranges Xs N Pl entry groups first hK hsrc scope k c hc _ _

end Letters

section Parts
variable {W₀ Rc X₀ X' Wk : Type}

/-- The search at the test's place, where the letters bear the first chain's seven places. -/
theorem find_ranges (K : KeyParts W₀ Rc X₀ X' Wk) (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 5, .K12⟩ : Place)) = some K.rng := by
  have e1 : ((ProofFile.Honest.K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X').place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.idx.P.place == _) = false
    rw [h.idx]
    decide
  have e2 : ((ProofFile.Honest.K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X').place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.msg.P.place == _) = false
    rw [h.msg]
    decide
  have e3 : ((ProofFile.Honest.K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X')
      (ProofFile.Honest.K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0).place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.look0.place == _) = false
    rw [h.look0]
    decide
  have e4 : ((ProofFile.Honest.K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X')
      (ProofFile.Honest.K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1).place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.look1.place == _) = false
    rw [h.look1]
    decide
  have e5 : (K.rng.place == (⟨1, none, 5, .K12⟩ : Place)) = true := by
    rw [h.rng]
    decide
  show List.find? _ (_ :: _ :: _ :: _ :: K.rng :: _) = _
  simp only [List.find?, e1, e2, e3, e4, e5]

variable {Z : PublicFiles} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {entry : Local W₀ Rc Xi Unit → Nat → Nat → GF} {groups : List (List Nat)} {first : Nat}

/-- The half at the job's place. -/
theorem half_ranges (K : KeyParts W₀ Rc X₀ X' Wk) (hA : K.AtPlaces)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)) :
    ((keyProver K).first.find? fun g =>
      g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)) := by
  have e : (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place =
      (⟨1, none, 5, .K12⟩ : Place) := by
    have h := hA.rng
    rw [hrng] at h
    exact h
  rw [e, ← hrng]
  exact find_ranges K hA

/-- **`play` returns at the test on the ranges, at `keyProver K`.** -/
theorem ranges_plays_at_parts {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) (K : KeyParts W₀ Rc X₀ X' Wk)
    (hA : K.AtPlaces) (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first))
    (Pre : Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, b.place.kind = .K12 →
      BlockPlays .own Bk 0 (keyProver K).first b Pre :=
  ranges_plays Xs N Pl entry groups first hB hK hsrc scope _ (half_ranges K hA hrng) Pre

/-- **The field `rangesTest` of `KeyOthersPlay`** (E2E/OfflineRunsKey.lean), in its own type. -/
theorem ranges_test {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (hK : fullPub = some K₀)
    (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) (K : KeyParts W₀ Rc X₀ X' Wk)
    (hA : K.AtPlaces) (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first))
    (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own rngPlace :=
  fun _ b hj hp => ranges_plays_at_parts hB hK hsrc scope K hA hrng _ b (List.mem_of_getElem? hj)
    (by rw [hp]; rfl)

end Parts

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- In scope the value bears the first chain's seven places. -/
theorem value_places_ranges {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtPlaces := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  refine atPlaces_value K' Xs N Pl f g inR d pU pO ent groups first ?_
  show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
  rw [el]
  decide +kernel

/-- **`play` returns at the test on the ranges, at the offline prover's own senders.** -/
theorem ranges_plays_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (Pre : Mid (Local W₀ Rc Xi Unit) Unit → Prop) :
    ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, b.place.kind = .K12 →
      BlockPlays .own Bk 0 (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first b
        Pre :=
  ranges_plays_at_parts hB hK hs scope _
    (value_places_ranges K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl Pre

/-- **A TEST OF EMPTINESS: at all coins the book lends, and the laying of the sub-protocol's steps
returns.** -/
theorem ranges_lent_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (k : Coins (keyBook K₀))
    (v : Option (Local W₀ Rc Xi Unit)) :
    ∃ l, chainSteps (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0) v [rngEntry Xs.Y.k.oneTime N]
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first = .ok l := by
  obtain ⟨c, -, h⟩ := lends_ranges (X' := Unit) Xs N Pl ent groups first hK hs scope
    (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first
    (half_ranges _ (value_places_ranges K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl)
    k v
  exact ⟨_, h⟩

/-- **A TEST OF EMPTINESS: the first chain's flat list has a sub-protocol of kind K12.** -/
theorem ranges_there : ∃ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, b.place.kind = .K12 := by
  have hp : (rngEntry Xs.Y.k.oneTime N).place = (⟨1, none, 5, .K12⟩ : Place) :=
    (seatOf_rngEntry Xs.Y.k.oneTime N
      (rangesTestJob (W₀ := Unit) (Rc := Unit) (X' := Unit) Xs N Pl (fun _ _ _ => 0) [] 0) rfl).place.trans
      (AtPublicFiles.KeyValueHolds.place_p12At _ _)
  exact ⟨_, (key_sits_row Xs N Pl).ranges.1, by rw [hp]⟩

/-- **The share of the test on the ranges in `BlocksPlay.first`** (E2E/OfflineRunsForm.lean), in that field's
own form: at the prover of the muted rows at the value, whatever the simulators S, the rows' letters c, the
prover H whose other fields are taken, and the run's input. -/
theorem ranges_first_at_rows {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (own : Local W₀ Rc KeyInst Unit) :
    ∀ j b, (keyFileDescription Xs N Pl).first.blocksInOrder[j]? = some b → b.place.kind = .K12 →
      BlockPlays .own Bk 0 ((offlineRows (keyFileDescription Xs N Pl) Bk
          (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H).first b
        (MidForm startNone (roundsIn (keyFileDescription Xs N Pl).first.blocksInOrder j) own) := by
  intro j b hj hk
  rw [prover_mute, offlineRows_prover_at]
  exact ranges_plays_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB _ b
    (List.mem_of_getElem? hj) hk

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.agree_ranges
#print axioms AtPublicFiles.OfflineRows.ranges_plays
#print axioms AtPublicFiles.OfflineRows.find_ranges
#print axioms AtPublicFiles.OfflineRows.half_ranges
#print axioms AtPublicFiles.OfflineRows.ranges_plays_at_parts
#print axioms AtPublicFiles.OfflineRows.ranges_test
#print axioms AtPublicFiles.OfflineRows.value_places_ranges
#print axioms AtPublicFiles.OfflineRows.ranges_plays_at_value
#print axioms AtPublicFiles.OfflineRows.ranges_lent_at_value
#print axioms AtPublicFiles.OfflineRows.ranges_there
#print axioms AtPublicFiles.OfflineRows.ranges_first_at_rows
