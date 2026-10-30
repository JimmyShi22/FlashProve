-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRangesFive.lean: On at a run at the key file's proximity test on the ranges, as far as it
reads no walk of the verifier and no hidden datum. The condition is `onFree`
(Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFree.lean): at the first member it asks nothing, at the
second `OnFree`'s eight clauses.

  `ranges_public`        `TestPublic` at the job `rangesTestJob` (E2E/KeyRangesJob.lean), in scope
  `ranges_laid`          the sub-protocol at the test's place declares the job's rounds and oracle messages
  `ranges_five_at_run`   FIVE OF THE EIGHT (le, leS, heardFit, heard, fold) at a run's own carried blocks,
                         state and front, at any letters K whose half at the ranges is `proverSideOfProximityTest` of that job
  `RangesThreeAtRun`     THE THREE THAT ARE LEFT (door, asks, tree: `ThreeAtEntry`, E2E/OfflineTestFive.lean)
                         at the same values: a premise's form, with what each hangs on in its docstring
  `ranges_on_at_run`     the socket: `onFree` at every member of the row, at the run's own values, from
                         `RangesThreeAtRun`: at the first member it asks nothing

Limits. It pays none of door, asks, tree. At a state on entry that is the job's own letter rec₀, not shown
to be the verifier's. That a run returns, or calls the part, is not shown here. Nothing on any property.
-/
import E2E.OfflineTestFive
import E2E.OfflineSides
import E2E.KeyRangesJob
import E2E.KeyPublic
import E2E.KeyBookThirdNamed
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey
import Johnson.SendSim.Seat.AtKeyStands
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces rangesParams)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts)
open OnBytes (TableKey Codes)
open OnBytes.Slice (GF)
open H2K.JointK (laidOf rngEntry key_sits_row)
open H2K.Member (piKRFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace)
open AtPublicFiles.KeyThread (rangesTestJob jobRng_rows place_sourced stages_plays seatOf_rngEntry)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

section Public
variable {W₀ Rc : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The job's public part**, in scope. -/
theorem ranges_public (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    ∃ s next rest, TestPublic (rangesTestJob (X' := Unit) Xs N Pl ent groups first) s next rest ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block VerifiableInference.Desc.K12.T12 Unit).planOk = true := by
  have hJ : (rangesTestJob (X' := Unit) Xs N Pl ent groups first).p = piKRFull := place_sourced hs scope
  obtain ⟨s, t, rest, hst, hk, Q⟩ := stages_plays _ hJ rfl
  refine ⟨s, t, rest, ⟨hst, hk, ?_, Q.sorts, Q.tables, fun w fr mem mem' h => ?_⟩, Q.plan⟩
  · rw [hJ]
    decide +kernel
  · rw [jobRng_rows Xs N Pl ent groups first w fr mem mem' h]

/-- **The sub-protocol at the test's place declares the job's rounds and oracle messages.** -/
theorem ranges_laid (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl} (hb : b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder)
    (hp : b.place = rngPlace) :
    b.rounds.zip b.oracles = (rangesTestJob (X' := Unit) Xs N Pl ent groups first).laid := by
  obtain ⟨-, -, -, -, hplan⟩ := ranges_public ent groups first hs scope
  have e : b = rngEntry Xs.Y.k.oneTime N := (key_sits_row Xs N Pl).ranges.2.2 b hb (by rw [hp]; rfl)
  have S := seatOf_rngEntry Xs.Y.k.oneTime N (rangesTestJob (X' := Unit) Xs N Pl ent groups first) rfl
  rw [e, S.rounds, S.oracles]
  exact zip_laid _ hplan

end Public

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- The half of the first chain at the ranges' place is the letter `rng`. -/
theorem half_at_ranges (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    {g : Placed (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit}
    (hg : g ∈ (keyProver K).first) (hp : g.place = rngPlace) : g = K.rng := by
  have hk : g.place.kind = .K12 := by rw [hp]; rfl
  rw [keyProver_first] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hk (by
      show K.idx.P.place.kind ≠ _
      rw [hA.idx]
      decide)
  · exact absurd hk (by
      show K.msg.P.place.kind ≠ _
      rw [hA.msg]
      decide)
  · exact absurd hk (by
      show K.look0.place.kind ≠ _
      rw [hA.look0]
      decide)
  · exact absurd hk (by
      show K.look1.place.kind ≠ _
      rw [hA.look1]
      decide)
  · rfl
  · exact absurd hk (by
      show (K13.k13Place K.batt).kind ≠ _
      rw [hA.batt]
      decide)
  · exact absurd hk (by
      show K.w.P.place.kind ≠ _
      rw [hA.w]
      decide)

/-- **FIVE OF THE EIGHT CLAUSES OF `OnFree` AT A RUN, at the second part of the test on the ranges**: at
every carried block and every state that the frame returns at the part's address, where the part is
called, at the run's own front. Js: any simulators' job: nothing is read of it. -/
theorem ranges_five_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hr : K.rng = proverSideOfProximityTest (rangesTestJob Xs N Pl ent groups first)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob KeyInst) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = rngPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀
        rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry (rangesTestJob Xs N Pl ent groups first) (stretches _ ca) m
        (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  subst hB
  obtain ⟨s, next, rest, P, -⟩ := ranges_public ent groups first hs scope
  intro L hL hp σ hσ
  have hplace : (rangesTestJob (X' := Unit) Xs N Pl ent groups first).p.place = rngPlace := by
    show (rangesParams N).place = _
    rw [place_sourced hs scope]
    rfl
  have hparts : L.row.map (·.1) = [firstPart (rangesTestJob Xs N Pl ent groups first),
      restPart (rangesTestJob Xs N Pl ent groups first)] := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    obtain rfl := half_at_ranges K hA hg hp
    show (partsBeside K.rng.parts _).map (·.1) = _
    rw [partsBeside_parts, hr]
    rfl
  have hT : tiesB (keyBook K₀) (rangesTestJob (X' := Unit) Xs N Pl ent groups first).p.place
      (rangesTestJob (X' := Unit) Xs N Pl ent groups first).members.length = true := by
    rw [hplace]
    exact ties_ranges K₀ hK
  exact five_at_first_row hs.named.plan (AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK) due h hL hσ
    (rangesTestJob Xs N Pl ent groups first) Js _ rfl (hp.trans hplace.symm) hparts
    (ranges_laid ent groups first hs scope (OnBytes.SendSim.Seat.block_of_seated hσ)
      ((side_place hσ).trans hp)) hT s next rest P st

/-- **THE THREE CLAUSES OF `OnFree` THAT ARE LEFT AT THE RANGES' SECOND PART, AT A RUN's OWN VALUES.** A
premise's form; no member is given here.
`door`: shown data alone: the job's state on entry is made by replaying the description's first fifteen
sub-protocols over the rounds shown, with no column and no key (E2E/KeyRangesJob.lean, KeyRangesFront.lean):
it hangs on the text of the simulators' job Js.
`asks`: its public half is evaluated (`planB_KR`); the rest speaks of the verifier's state at the border
15 of the first chain and of hidden data: that the group's open rows say true things of the
multiplicities' words, which holds where the index is in range. It hangs on the first chain's walk.
`tree`: that the tree in front is the one that the sending of the multiplicities sends, and that the
run's front lists its columns. It hangs on the same walk. -/
def RangesThreeAtRun (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
    (first : Nat) {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob KeyInst) (Kc : Codes)
    (o : Fmt.Shape × Fmt.TreeSource) (w₀ : W₀) (rc : Rc) (x : KeyInst) (k : Coins Bk) (ρ : Draws)
    (r : RunC (keyFileDescription Xs N Pl)) (st : List (ℕ × ℕ × List UInt64)) : Prop :=
  ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = rngPlace →
    ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
    r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
    carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    orRefused (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀
      rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    ThreeAtEntry (rangesTestJob Xs N Pl ent groups first) Js Kc 0 o (Face.own.pub m.st.input)
      (stretches _ ca) m (r.run.beforeAt st ⟨L.place, u.number⟩)

/-- **THE SOCKET: `onFree` at every member of the ranges' row, at a run's own values**, from the three
that are left. At the first member the condition asks nothing. In the form in which `owedAt_first_at`
(E2E/OfflineOwedChains.lean) asks On. -/
theorem ranges_on_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hr : K.rng = proverSideOfProximityTest (rangesTestJob Xs N Pl ent groups first)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob KeyInst) (Kc : Codes)
    (o : Fmt.Shape × Fmt.TreeSource) {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws}
    {r : RunC (keyFileDescription Xs N Pl)} (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64))
    (three : RangesThreeAtRun ent groups first K S c H Js Kc o w₀ rc x k ρ r st) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = rngPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀
        rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      onFree Face.own (rangesTestJob Xs N Pl ent groups first) Js Kc 0 o u ca m
        (r.run.beforeAt st ⟨L.place, u.number⟩) :=
  fun L hL hp σ hσ u hu hc ca m hca hm hn =>
    onFree_of_five
      (ranges_five_at_run hs scope hK hB ent groups first K hA hr S c H Js due h st L hL hp σ hσ u hu
        hn hc ca m hca hm)
      (three L hL hp σ hσ u hu hn hc ca m hca hm)

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.half_at_ranges
#print axioms AtPublicFiles.OfflineRows.ranges_five_at_run
#print axioms AtPublicFiles.OfflineRows.ranges_on_at_run
#print axioms AtPublicFiles.OfflineRows.ranges_public
#print axioms AtPublicFiles.OfflineRows.ranges_laid
