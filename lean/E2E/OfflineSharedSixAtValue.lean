-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedSixAtValue.lean: the second clauses of the fields `good` and `owed` of `OwedRest`
(E2E/OfflineClauses.lean) at six of the eight rows of the shared chain, at the offline prover's own
senders (`valueAt`, E2E/KeyValueHolds.lean), at the six rows' own simulators (`k14Lists`,
AtFullSide/K14/Sim/AtOffline.lean) and letters, at a book that equals the written one.

  `ownLetters`, `foldedLetters`, `omegaLetters`, `sharedSixLetters_of`   the six rows' letters as values
                       of `RowConditions`; where they are laid at the six places `SharedSixLetters` holds
  `value_senders`      `KeySendersAtTheDescription` at the value, in scope
  `value_atAll`        the value bears the sixteen places, in scope, where its two shared tests do
  `shared_six_good_at_value`, `shared_six_good_at_laid`   the clause of `good`
  `shared_six_owed_at_value`   the clause of what `owed` concludes
  `shared_six_there`   A TEST OF EMPTINESS: at each of the six places the muted rows' shared list has a
                       row, it has a side, and the side has one member

Premises that stay: `KeySourced`, scope; the book equals the written one; the two shared tests' places;
what is laid at the six places; `SharedSixLetters`; for `owed` also that the public files' test says
yes, that the challenges are due and that `runC` has returned.

The limits are those of E2E/OfflineSharedSixGood.lean and E2E/OfflineSharedSixOwed.lean. Nothing on any
property.
-/
import E2E.OfflineSharedSixOwed
import E2E.OfflineSharedSixBook
import AtFullSide.K14.Sim.AtOffline
import E2E.OfflineBatchingRowGood
import E2E.KeyValueHolds
import E2E.KeyBookThirdNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open OnBytes.SendSim.At (budAt)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub pointPlace foldedPlace locPlace omegaPlace zetaPlace
  splitPlace foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyValues (WitK oneOf)
open AtPublicFiles.KeyValueHolds (valueAt atAll_value)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open AtPublicFiles.AtFiles.Full (QK par_sourced)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

section Letters
variable {W₀ Rc X₀ X Wk S : Type} {Bk : ProverCoinCounts}

/-- The letters of "LIN point", "LOC", "LIN zeta" and "SPLIT": they ask nothing. -/
def ownLetters : RowConditions Bk S Empty (Common W₀ Rc TableKey) X₀ TableKey :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ => True, k14On, k14Bud⟩

/-- The letters of the sending of the folded row. -/
def foldedLetters (K : KeyParts W₀ Rc X₀ X Wk) :
    RowConditions Bk S Empty (Common W₀ Rc TableKey) X₀ TableKey :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ m _ => pointApart K.send m.st.heard,
    fun _ _ asks => budAt (jobU K.send).Q asks⟩

/-- The letters of the sending of Omega. -/
def omegaLetters (K : KeyParts W₀ Rc X₀ X Wk) :
    RowConditions Bk S Empty (Common W₀ Rc TableKey) X₀ TableKey :=
  ⟨fun _ _ _ _ => True, fun _ _ _ _ => True, fun _ _ m _ => pointApart K.send m.st.heard,
    fun _ _ asks => budAt (jobOmega K.send).Q asks⟩

end Letters

section AtLetters
variable {W₀ Rc Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}

/-- **Where these letters are laid at the six places, the rows' letters are the six rows' own.** -/
theorem sharedSixLetters_of (K : KeyParts W₀ Rc Unit Unit Wk)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (h1 : c.shared pointPlace = ownLetters) (h2 : c.shared foldedPlace = foldedLetters K)
    (h4 : c.shared locPlace = ownLetters) (h5 : c.shared omegaPlace = omegaLetters K)
    (h7 : c.shared zetaPlace = ownLetters) (h8 : c.shared splitPlace = ownLetters) :
    SharedSixLetters K c := by
  refine ⟨fun r hr => ?_⟩
  rcases List.mem_append.1 (keyRows_mem K r hr) with g | g
  · unfold ownRows at g
    rcases List.mem_append.1 g with g | g
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
      rcases g with rfl | rfl | rfl
      · show (c.shared pointPlace).atPart = _ ∧ (c.shared pointPlace).positions = _
        rw [h1]
        exact ⟨rfl, rfl⟩
      · show (c.shared locPlace).atPart = _ ∧ (c.shared locPlace).positions = _
        rw [h4]
        exact ⟨rfl, rfl⟩
      · show (c.shared zetaPlace).atPart = _ ∧ (c.shared zetaPlace).positions = _
        rw [h7]
        exact ⟨rfl, rfl⟩
    · split at g
      · obtain rfl := List.mem_singleton.1 g
        show (c.shared splitPlace).atPart = _ ∧ (c.shared splitPlace).positions = _
        rw [h8]
        exact ⟨rfl, rfl⟩
      · cases g
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl
    · show (c.shared foldedPlace).atPart = _ ∧ (c.shared foldedPlace).positions = _
      rw [h2]
      exact ⟨rfl, rfl⟩
    · show (c.shared omegaPlace).atPart = _ ∧ (c.shared omegaPlace).positions = _
      rw [h5]
      exact ⟨rfl, rfl⟩

/-- **A TEST OF EMPTINESS.** In scope, at letters that bear the sixteen places, the muted rows' shared
list has a row at each of the six places, that row has a side at the description's shared chain, and
the side has one member. -/
theorem shared_six_there {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtAll) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) (p : Place)
    (hp : SixPlace p) :
    ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = p ∧
      ∃ σ, (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).shared.blocksInOrder
        [] = some σ ∧ σ.members.length = 1 := by
  obtain ⟨-, r2, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have hin : ∀ q : Place, SixPlace q → q ∈ AtPublicFiles.KeyBook.fullShared.map (·.1) := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hrow : ∃ q ∈ keyRows K, q.place = p ∧ q.row.length = 1 := by
    have e := keyRows_places K hA.splits
    have hm : (p, 1) ∈ (keyRows K).map (fun r => (r.place, r.row.length)) := by
      rw [e]
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨q, hq, eq⟩ := List.mem_map.1 hm
    exact ⟨q, hq, (Prod.mk.inj eq).1, (Prod.mk.inj eq).2⟩
  obtain ⟨q, hq, hqp, hql⟩ := hrow
  have hh : q.half ∈ (keyProver K).shared := by
    rw [keyRows_half]
    exact List.mem_append_left _ (List.mem_map.2 ⟨q, hq, rfl⟩)
  refine ⟨(rowOf q.half (S.byChain.shared q.half.place) (c.shared q.half.place)).mute,
    List.mem_map.2 ⟨_, List.mem_map.2 ⟨q.half, hh, rfl⟩, rfl⟩, hqp, ?_⟩
  have hsome := side_isSome (((rowOf (Cl := (keyFileDescription Xs N Pl).Cl) q.half
    (S.byChain.shared q.half.place) (c.shared q.half.place)).mute).withField 1 0
      (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0) (keyFileDescription Xs N Pl).shared.blocksInOrder [] (by
                                                show q.place ∈ _
                                                rw [hqp, places_of_rows r2]
                                                exact hin p hp)
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨σ, hσ, ?_⟩
  have hrow' : σ.row = partsBeside q.half.parts (S.byChain.shared q.half.place) := by
    unfold Lettered.side Side.seated at hσ
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
    rfl
  unfold Side.members
  rw [membersOf_length, hrow', partsBeside_length]
  show (q.row.map (·.1)).length = 1
  rw [List.length_map, hql]

end AtLetters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **In scope the value's sendings and shape are the written ones.** -/
theorem value_senders {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    KeySendersAtTheDescription (valueAt K' Xs N Pl f g inR d pU pO ent groups first) := by
  have e := par_sourced hs scope
  constructor
  · show (⟨AtPublicFiles.KeySharedThread.parKey Xs Pl, 0⟩ : SendPub) = ⟨QK, 0⟩
    rw [show AtPublicFiles.KeySharedThread.parKey Xs Pl = QK from e]
  · show (planData (AtPublicFiles.KeySharedThread.parKey Xs Pl)).S = QK.S
    rw [show AtPublicFiles.KeySharedThread.parKey Xs Pl = QK from e]
    rfl

/-- The written shape has a message W and splits. By evaluation. -/
theorem shape_written : (OnBytes.linMessageW Lk6.AtPlan.keyFull.once.shape).isSome = true ∧
    QK.S.sharedSplitNeeded = true := by decide +kernel

/-- **In scope the value bears the sixteen places**, where its two shared tests do. -/
theorem value_atAll {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtAll := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  refine atAll_value K' Xs N Pl f g inR d pU pO ent groups first ?_ ?_ hU hO
  · show (OnBytes.linMessageW Xs.Y.k.oneTime.lin).isSome = true
    rw [el]
    exact shape_written.1
  · rw [show AtPublicFiles.KeySharedThread.parKey Xs Pl = QK from par_sourced hs scope]
    exact shape_written.2

/-- **The second clause of `OwedRest.good` at the six rows, at the offline prover's own senders.** -/
theorem shared_six_good_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) (S : OfflineSimulators)
    (hS : SimsAtSix (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.shared,
      SixPlace L.place →
      (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 1) .shared (keyFileDescription Xs N Pl).shared.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 1 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                           (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.falls₂ := by
  obtain ⟨b0, b1, b2⟩ := shared_book_paid hs scope hK hB
  exact shared_six_good_mute hs scope _
    (value_atAll K' Xs N Pl f g inR d pU pO ent groups first hs scope hU hO)
    (value_senders K' Xs N Pl f g inR d pU pO ent groups first hs scope) S hS c hc b0 b1 b2

/-- **The same at the laid simulators with the six rows' own lists**, whatever the four lists that
stay letters. -/
theorem shared_six_good_at_laid {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
        (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
          (k14Lists (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)) c).mute.shared,
      SixPlace L.place →
      (L.withField 1 0 (keyFileDescription Xs N Pl).shared.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 1) .shared (keyFileDescription Xs N Pl).shared.blocksInOrder
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 1 0 (offlineRows (keyFileDescription Xs N Pl) Bk
                           (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                           (laidSimulators (valueAt K' Xs N Pl f g inR d pU pO ent groups first)
                             (k14Lists (valueAt K' Xs N Pl f g inR d pU pO ent groups first) T)) c).mute.falls₂ :=
  shared_six_good_at_value K' Xs N Pl f g inR d pU pO ent groups first hs scope hK hB hU hO _
    (simsAtSix_laid _ T) c hc

/-- **The second clause of what `OwedRest.owed` concludes at the six rows, at the offline prover's own
senders.** -/
theorem shared_six_owed_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts}
    (hB : Bk = keyBook K₀) (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace)
    (S : OfflineSimulators)
    (hS : SimsAtSix (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S.byChain.shared)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hc : SharedSixLetters (valueAt K' Xs N Pl f g inR d pU pO ent groups first) c)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (w₀ : W₀) (rc : Rc) (x : KeyInst)
    (k : Coins Bk) (ρ : Draws) (r : RunC (keyFileDescription Xs N Pl))
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                 (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H) w₀ rc x k ρ =
        .ok r) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.shared,
      SixPlace L.place →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                     (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.prover H) w₀ rc x k ρ a))
        r.run (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called :=
  shared_six_owed_mute hs scope live
    (by rw [hB]; exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK) _
    (value_atAll K' Xs N Pl f g inR d pU pO ent groups first hs scope hU hO)
    (value_senders K' Xs N Pl f g inR d pU pO ent groups first hs scope) S hS c hc H w₀ rc x k ρ r
    hρ h

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.sharedSixLetters_of
#print axioms AtPublicFiles.OfflineRows.shared_six_there
#print axioms AtPublicFiles.OfflineRows.value_senders
#print axioms AtPublicFiles.OfflineRows.shape_written
#print axioms AtPublicFiles.OfflineRows.value_atAll
#print axioms AtPublicFiles.OfflineRows.shared_six_good_at_value
#print axioms AtPublicFiles.OfflineRows.shared_six_good_at_laid
#print axioms AtPublicFiles.OfflineRows.shared_six_owed_at_value
