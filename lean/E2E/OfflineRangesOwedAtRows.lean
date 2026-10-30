-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRangesOwedAtRows.lean: THE FIRST CLAUSE OF WHAT THE FIELD owed OF `OwedRest` (E2E/OfflineClauses.lean) CONCLUDES, AT THE
ROW OF THE KEY FILE's PROXIMITY TEST ON THE RANGES, FROM ONE NAMED PREMISE ON VALUES: at the called second part the rows that
the test takes in hold at the job's words (`SayAtRun`, E2E/OfflineSayAtRun.lean). A join.

  `trees_before_message`   in scope one tree is sent in front of the multiplicities' sending
  `ranges_row_is`          the row of `offlineRows` at the test's place: its parts beside its simulators, its letters
  `ranges_halves_found`    the prover's side at the test's place and at the multiplicities' sending's
  `rangesPlainRows`        the job's plain rows, of the input, the front and the coins
  `onAtRun_ranges_of_say`  `OnAtRun₁` at such a row, from `SayAtRun`
  `owed_ranges_at_rows`, `owed_ranges_mute`   `owedAt` at the row; the same at the muted rows, in the form of the clause

By what. bud: the count of the key's written rounds at the test (`budOwed₁_at_KR`, Johnson/M1/KeyBudR.lean). On: the five public
clauses, the door and the clause on the trees: `onAtRun_ranges_book` (…/K12/Sim2/RowRangesPub.lean); what is left there, the two
clauses on the asks: `left_ranges_at_run` (E2E/OfflineRangesLeftAtRun.lean). From On at the run to `owedAt`:
`owedAt_first_of_onAtRun` (E2E/OfflineOwedRowAtRun.lean).

Premises that stay. In scope, at a book that equals the written one. The letters K bear the first chain's places; their
half at the test's place is the pair of `rangesTestJob`, their sending of the multiplicities is `msgJob` at the same reader of entries.
What is laid at the place: the two simulators of `simRanges`; On is `OnEntry`, bud is `budBoth`. One member of `ThreadsP` at the
prepared input: it stands in `OnAtRun₁`'s type. The clause's own: the challenges are due, no stop is met, `runC` has returned.
AND `SayAtRun`: THE ONE SENTENCE ON VALUES: no member of it is given here.

Limits. `SayAtRun` reads the input and the carried coins: it says that the multiplicities' words are true at the rows taken in; no
later law may take it as a hypothesis on a run and then speak of the coins as sampled anew. Nothing on completeness, on soundness
or on what is hidden.
-/
import E2E.OfflineRangesLeftAtRun
import E2E.OfflineSayAtRun
import E2E.OfflineOwedRowAtRun
import E2E.OfflineSides
import E2E.KeyRangesTrees
import E2E.KeyBookThirdNamed
import Johnson.M1.KeyBudR
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesPub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Sim2 (LeftAtRanges simRanges OnEntry onAtRun_ranges_book find_ranges facts_KRFull
  dsKR place_KR)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces pieces sendingPar groupsTold rootsAt)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace msgPlace rideMsg sendingPar_sent)
open AtPublicFiles.KeyThread (rangesTestJob sentRanges place_sourced len_oracles trees_len one_idx)
open AtPublicFiles.Key (msgJob)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (six_sourced)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)

section Public
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **In scope one tree is sent in front of the multiplicities' sending.** -/
theorem trees_before_message (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 = 1 := by
  have h6 := six_sourced hs scope
  have e1 : treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 =
      ((VerifiableInference.Desc.K1.oracles (sendingPar Xs.Y.k.oneTime pieces.idx "the index masks"
        #[Xs.Y.k.oneTime.indexMasks] (groupsTold Xs.Y.told.1 0 (rootsAt Xs.Y.D.1 0))) ++
          []).flatMap id ++ []).length := rfl
  rw [e1, List.append_nil, List.append_nil, len_oracles,
    trees_len _ keyFull.codes #[keyFull.once.input] h6.codes
      (by rw [sendingPar_sent, h6.indexMasks]), one_idx]

end Public

section Rows
variable {W₀ Rc Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts}
  (ent : Local W₀ Rc Xi Unit → Nat → Nat → GF) (grp : List (List Nat)) (fst : Nat)

/-- **The row at the test's place.** -/
theorem ranges_row_is (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)) (S : OfflineSimulators)
    (hS : S.rangesTest = [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = rngPlace →
      L.row = testPairs (rangesTestJob (X' := Unit) Xs N Pl ent grp fst) (simRanges Xs N Pl) ∧
        L.On = (c.first rngPlace).atPart ∧ L.bud = (c.first rngPlace).positions := by
  intro L hL hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL
  have hp' : h.place = rngPlace := hp
  have apart : ∀ p : Place, p.kind ≠ .K12 → p ≠ rngPlace := by
    intro p hk e
    rw [e] at hk
    exact hk rfl
  rw [keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hp' (apart _ (by show K.idx.P.place.kind ≠ _; rw [hA.idx]; decide))
  · exact absurd hp' (apart _ (by show K.msg.P.place.kind ≠ _; rw [hA.msg]; decide))
  · exact absurd hp' (apart _ (by show K.look0.place.kind ≠ _; rw [hA.look0]; decide))
  · exact absurd hp' (apart _ (by show K.look1.place.kind ≠ _; rw [hA.look1]; decide))
  · refine ⟨?_, ?_, ?_⟩
    · show partsBeside K.rng.parts (S.byChain.first K.rng.place) = _
      rw [hp']
      show partsBeside K.rng.parts S.rangesTest = _
      rw [hS, hrng]
      rfl
    · show (c.first K.rng.place).atPart = _
      rw [hp']
    · show (c.first K.rng.place).positions = _
      rw [hp']
  · exact absurd hp' (apart _ (by show (K13.k13Place K.batt).kind ≠ _; rw [hA.batt]; decide))
  · exact absurd hp' (apart _ (by show K.w.P.place.kind ≠ _; rw [hA.w]; decide))

/-- **The prover's side at the test's place and at the multiplicities' sending's.** -/
theorem ranges_halves_found (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == rngPlace) = some K.rng ∧
      ((keyProver K).first.find? fun g => g.place == msgPlace) = some (K1.proverSideOfSending K.msg) := by
  have hp := AtPublicFiles.KeyFile.first_places K hA
  rw [keyProver_first] at hp ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_⟩
  · simp only [List.find?_cons, p1, p2, p3, p4, p5]
    rfl
  · simp only [List.find?_cons, p1, p2]
    rfl

/-- The job's plain rows, of the input, the front and the coins. -/
def rangesPlainRows (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (ent : Local W₀ Rc Xi Unit → Nat → Nat → GF) (grp : List (List Nat)) (fst : Nat)
    (w : Local W₀ Rc Xi Unit) (fr : Front Unit) (C : TestCoins) : PlainRows :=
  plainOne (sentRanges Xs ent grp fst) w (C.mem 0)
    ((rangesTestJob (X' := Unit) Xs N Pl ent grp fst).first w fr C)

end Rows

section Run
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky : Type}
  {Kp : KeyPub}

/-- **`OnAtRun₁` at the row of the test on the ranges, from the one sentence on values.** -/
theorem onAtRun_ranges_of_say (scope : InScope Z = true) (hs : KeySourced Z Xs N Pl)
    (hK : fullPub = some Kp) {H : Prover W₀ Rc Xi Ky Unit Unit Unit}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook Kp) W₀ Rc Ky Unit Unit Unit} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins (keyBook Kp)} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit Unit Unit}
    {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook Kp) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook Kp) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook Kp) (G.prover H) w₀ rc x k ρ = .ok r)
    (ent : Local W₀ Rc Xi Unit → ℕ → ℕ → GF) (grp : List (List ℕ)) (fst fst' : ℕ)
    (L : Lettered (keyBook Kp) (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Unit Xi)
    (hplace : L.place = rngPlace)
    (hrow : L.row = testPairs (rangesTestJob (X' := Unit) Xs N Pl ent grp fst) (simRanges Xs N Pl))
    (hOn : L.On = OnEntry Face.own (rangesTestJob (X' := Unit) Xs N Pl ent grp fst) (simRanges Xs N Pl)
      codesKeyFull 0 piKRFull.nums.first)
    (hg : ((G.prover H).first.find? fun g => g.place == rngPlace) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)))
    (hgS : ((G.prover H).first.find? fun g => g.place == msgPlace) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit)
        (msgJob (X := Unit) ent Xs.Y.k.oneTime pieces grp fst' rideMsg)))
    (hsay : SayAtRun (Local W₀ Rc Xi Unit) (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)
      (rangesPlainRows Xs N Pl ent grp fst) k 0 rngPlace r.called
      (midAtW (keyFileDescription Xs N Pl) (keyBook Kp) (G.prover H) w₀ rc x k ρ)) :
    OnAtRun₁ T ρ r L := by
  refine onAtRun_ranges_book scope hs hK T hρ hR hrun ent grp fst fst' L hplace hrow hOn hg hgS
    (trees_before_message hs scope) fun m ca _ _ _ _ _ _ _ hc hm hca _ => ?_
  rw [hplace] at hc hm hca
  exact left_ranges_at_run scope hs hρ hR hrun ent grp fst hg (ties_ranges Kp hK) hc m hm _
    (hsay hc m ca hm hca)

variable {Wk : Type} {Bk : ProverCoinCounts}

/-- **`owedAt` at the row of the test on the ranges**, at a run that has returned. -/
theorem owed_ranges_at_rows (scope : InScope Z = true) (hs : KeySourced Z Xs N Pl)
    (hK : fullPub = some Kp) (hB : Bk = keyBook Kp) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hA : K.AtPlaces) (ent : Local W₀ Rc Xi Unit → ℕ → ℕ → GF) (grp : List (List ℕ)) (fst fst' : ℕ)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl ent grp fst))
    (hmsg : K.msg = msgJob (X := Unit) ent Xs.Y.k.oneTime pieces grp fst' rideMsg)
    (S : OfflineSimulators)
    (hS : S.rangesTest = [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hcOn : (c.first rngPlace).atPart = OnEntry Face.own (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)
      (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first)
    (hcBud : (c.first rngPlace).positions = budBoth (simRanges Xs N Pl))
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (w₀ : W₀) (rc : Rc) (x : KeyInst)
    (k : Coins Bk) (ρ : Draws) (R : Ready W₀ Rc KeyInst TableKey Unit Unit Unit)
    (r : RunC (keyFileDescription Xs N Pl)) (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl) ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x ρ =
      none)
    (hR : ready (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k =
      .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k
      ρ = .ok r)
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x
      k R)
    (hsay : SayAtRun (Local W₀ Rc Xi Unit) (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)
      (rangesPlainRows Xs N Pl ent grp fst) k 0 rngPlace r.called
      (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k
        ρ)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = rngPlace →
      L.owedAt (keyFileDescription Xs N Pl).first.blocksInOrder k 0
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  subst hB
  intro L hL hp
  obtain ⟨hrow, hOn, hbud⟩ := ranges_row_is ent grp fst K hA hrng S hS c L hL hp
  obtain ⟨f1, f2⟩ := ranges_halves_found K hA
  have hJ : (rangesTestJob (X' := Unit) Xs N Pl ent grp fst).p = piKRFull := place_sourced hs scope
  have hPR : (rangesTestJob (X' := Unit) Xs N Pl ent grp fst).p.place = rngPlace := by
    rw [hJ]
    exact place_KR
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_ranges scope hs.named
    (rangesTestJob (X' := Unit) Xs N Pl ent grp fst) rfl
  have F : PlaceFacts (rangesTestJob (X' := Unit) Xs N Pl ent grp fst).p dsKR := by
    rw [hJ]
    exact facts_KRFull
  refine owedAt_first_of_onAtRun hs.named.plan (AtPublicFiles.KeyBook.book_passes scope hs.named Kp hK) hρ hsil
    hR hrun T hL ?_ ?_
  · intro σ hσ u hu pre t n hcut hn
    exact OnBytes.M1.KeyBud.budOwed₁_at_KR scope hs.named L
      (rangesTestJob (X' := Unit) Xs N Pl ent grp fst) F (by rw [hJ]) hPR hf hbp hr hor rfl
      (simRanges Xs N Pl) hJ.symm rfl (hp.trans hPR.symm) hrow
      (fun n ds asks h => by rw [hbud, hcBud]; exact h) σ hσ u hu pre t n hcut hn ρ hρ
  · refine onAtRun_ranges_of_say scope hs hK T hρ hR hrun ent grp fst fst' L hp hrow
      (hOn.trans hcOn) ?_ ?_ hsay
    · rw [offlineRows_prover_at]
      exact f1.trans (congrArg some hrng)
    · rw [offlineRows_prover_at]
      exact f2.trans (by rw [hmsg])

/-- **The row in the form of the first clause of what `OwedRest.owed` concludes.** -/
theorem owed_ranges_mute (scope : InScope Z = true) (hs : KeySourced Z Xs N Pl)
    (hK : fullPub = some Kp) (hB : Bk = keyBook Kp) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hA : K.AtPlaces) (ent : Local W₀ Rc Xi Unit → ℕ → ℕ → GF) (grp : List (List ℕ)) (fst fst' : ℕ)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl ent grp fst))
    (hmsg : K.msg = msgJob (X := Unit) ent Xs.Y.k.oneTime pieces grp fst' rideMsg)
    (S : OfflineSimulators)
    (hS : S.rangesTest = [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)])
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (hcOn : (c.first rngPlace).atPart = OnEntry Face.own (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)
      (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first)
    (hcBud : (c.first rngPlace).positions = budBoth (simRanges Xs N Pl))
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (w₀ : W₀) (rc : Rc) (x : KeyInst)
    (k : Coins Bk) (ρ : Draws) (R : Ready W₀ Rc KeyInst TableKey Unit Unit Unit)
    (r : RunC (keyFileDescription Xs N Pl)) (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl) ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc
      x ρ = none)
    (hR : ready (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x
      k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc
      x k ρ = .ok r)
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀
      rc x k R)
    (hsay : SayAtRun (Local W₀ Rc Xi Unit) (rangesTestJob (X' := Unit) Xs N Pl ent grp fst)
      (rangesPlainRows Xs N Pl ent grp fst) k 0 rngPlace r.called
      (midAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x
        k ρ)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = rngPlace →
      L.owedAt (keyFileDescription Xs N Pl).first.blocksInOrder k 0
        (fun a => orRefused (midAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  rw [prover_mute] at hsil hR hrun T hsay ⊢
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact (owedAt_mute L' _ _ _ _ _ _ _).2
    (owed_ranges_at_rows scope hs hK hB K hA ent grp fst fst' hrng hmsg S hS c hcOn hcBud H w₀ rc x k
      ρ R r hρ hsil hR hrun T hsay L' hL' hp)

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.trees_before_message
#print axioms AtPublicFiles.OfflineRows.ranges_row_is
#print axioms AtPublicFiles.OfflineRows.ranges_halves_found
#print axioms AtPublicFiles.OfflineRows.onAtRun_ranges_of_say
#print axioms AtPublicFiles.OfflineRows.owed_ranges_at_rows
#print axioms AtPublicFiles.OfflineRows.owed_ranges_mute
