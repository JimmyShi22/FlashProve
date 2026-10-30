-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/AcceptedAtTest.lean: the frame's sentences «it plays» and «it is
accepted», asked from a thread's pair (`PlaysS`, `AcceptedS`, Honest/Thread/PaysS.lean), at a member at which
a seated proximity test stands: with the half `proverSideOfProximityTest J`, or with that half behind the guard
(`Placed.needsField`, K12/FieldGuard.lean). General in the thread, the letter, the job and the falls.

  `acceptedS_of_saysYes`   `AcceptedS` from `SaysYes`: `accepted_of_saysYes` (Honest/Thread/FileRowYes.lean)
                 at the pair
  `acceptedS_at_test`   `AcceptedS` at a test with no guard, where the pair gives `K12At`
  `playsS_at_guarded`, `acceptedS_at_guarded`   the same behind the guard, where what is said of the run
                 gives the field

The premise hop. A half behind the guard errs at its first move where the field `opened` is none:
`play_guarded_none` (K12/FieldGuardLift.lean). So at such a member no sentence of the frame can be had from
the thread alone: the pair must give the field. hop asks that it is there, of the pair and not of the
letter alone, and nothing of what it holds: what it holds reaches the law through `K12At.enters`.

By what. `saysYes_seat` (K12/SaysYesSeat.lean), `playsOn_k12` (K12/PlaysK12.lean), `playsOn_guarded`,
`saysYes_guarded` (K12/FieldGuardLift.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: each statement here has the thread's pair as a premise and a sentence
  of the frame as its end.
- That the pair holds at any run is not said here.
- `K12At` is a premise: no value of it is given here. Where the first fold sends its own table its field
  `opens` cannot be met (the limits of K12/SaysYesK12.lean): the test on G_omega takes the twin at its own
  tree.
- `K12/FieldGuardLift.lean` is a file of trials, on no row.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysAtTest
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift
import Johnson.Desc.ProofFile.Honest.Thread.FileRowYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **`AcceptedS` from `SaysYes`.** Where `fall b` is silent, so is fl. -/
theorem acceptedS_of_saysYes (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} {fall : ℕ → S → List Fmt.Drawn → Option String}
    {fl : S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (h : SaysYes T.φ Bk T.chain T.ft T.hs blk fl (ThrS T Said b))
    (hf : ∀ s ds, fall b s ds = none → fl s ds = none) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hT hd hst hn hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨s', n, hs⟩ := h k s m E ds l y cols hT hd hst (hf s ds hn) hl hy hc
  have hn' : n = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hn'
  exact ⟨s', hMv, hs⟩

/-- **It is accepted, at a test with no guard**, where the pair gives `K12At`. -/
theorem acceptedS_at_test (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E → drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
      fall b st ds = none →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      K12At J enter leave st m E ds c) :
    AcceptedS T Said fall b :=
  acceptedS_of_saysYes T Said hblk
    (saysYes_seat T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (fall b) (ThrS T Said b) s t rest
      hst hk hf HA) fun _ _ h => h

/-- **It plays, behind the guard**, where what is said of the run gives the field. -/
theorem playsS_at_guarded (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hop : ∀ k s m E, ThrS T Said b k s m E → m.opened.isSome = true) (sent : ℕ)
    (P : PlanPlays J s (t :: rest) sent) (hsent : treesTo T.bs b = sent)
    (hA : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1))
    (hold : ∀ k st m E, ThrS T Said b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
        ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hT : ∀ k st m E ds y cols, ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    PlaysS T Said b := by
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J) := by
    have e : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := beq_self_eq_true _
    simp [List.find?, e]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J) := by
    rw [hseat.place]
    exact f1
  have P0 : PlaysOn T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk (ThrS T Said b) (fun _ _ _ _ => True) :=
    playsOn_k12 T.φ Bk T.chain T.ft _ blk J enter leave hseat _ _ s t rest hst hk f1 sent P
      (fun k st m E _ c u _ hc =>
        ⟨hA k st m E c u hc, by
          obtain ⟨⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩, -⟩ := u
          rw [h3, hsent], hold k st m E u⟩)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  have P1 := playsOn_guarded (hs := T.hs) (proverSideOfProximityTest J) hf f2 hop P0
  intro blk' hblk' k st m E ds l u hd hs hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hy, hc, -⟩ := P1 k st m E ds l u hd hs hl
  have hMv : T.Moved blk k m E ds y cols := ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, hT k st m E ds y cols u hd hMv⟩

/-- **It is accepted, behind the guard**, where what is said of the run gives the field and the pair
gives `K12At`. -/
theorem acceptedS_at_guarded (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hop : ∀ k s m E, ThrS T Said b k s m E → m.opened.isSome = true)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E → drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
      fall b st ds = none →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      K12At J enter leave st m E ds c) :
    AcceptedS T Said fall b := by
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J) := by
    have e : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := beq_self_eq_true _
    simp [List.find?, e]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J) := by
    rw [hseat.place]
    exact f1
  exact acceptedS_of_saysYes T Said hblk
    (saysYes_guarded (hs := T.hs) (proverSideOfProximityTest J) hf f2 hop
      (saysYes_seat T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk J enter leave hseat (fall b)
        (ThrS T Said b) s t rest hst hk f1 HA)) fun _ _ h => h

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.acceptedS_of_saysYes
#print axioms ProofFile.Honest.K12.AtFile.acceptedS_at_test
#print axioms ProofFile.Honest.K12.AtFile.playsS_at_guarded
#print axioms ProofFile.Honest.K12.AtFile.acceptedS_at_guarded
