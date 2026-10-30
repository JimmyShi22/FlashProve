-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsK12.lean: WHAT ONE SUB-PROTOCOL OWES for "every run returns" (`BlockPlays`, E2E/OfflineRunsForm.lean: from a
state of the form Pre, at challenges that its rounds can draw, where nothing of it stops and the book has lent,
`play` returns) AT A BLOCK THAT SEATS A PROXIMITY TEST, general in the block, the job, the book, the chain and Pre. Two
laws, and their join.

  `blockPlays_k12`       the prover's side at the place is `proverSideOfProximityTest J`. By `half_returns` (K12/HalfReturns.lean), called as
                         `playsOn_k12` (K12/PlaysK12.lean) calls it
  `blockPlays_guarded`   from a list hs' with the half h at the place to a list hs with h behind the guard
                         (`Placed.needsField`, K12/FieldGuard.lean), where Pre says that columns are handed: by
                         E2E/OfflineGuardLaws.lean
  `blockPlays_k12_guarded`   the two joined: the prover's side at the place is `(proverSideOfProximityTest J).needsField`

Premises of `blockPlays_k12`. hb: the block has the test's place, rounds and oracle messages (`SeatOf`; its clause on the
decision is not used). hst, hk: two stages or more, k = h + g at the first. hf: the half at the place. plan, sorts,
tables: three of the six fields of `PlanPlays`: on the plan alone, and on whether `J.fresh` is none. HA: wherever Pre
holds, at the coins that the book lends the two parts, their readers agree (`Agree`, K12/CoinsAgree.lean).

WHY NO SHAPE HANGS ON A VALUE. That each message has the shape that its round declares (`Sending.fits`) is
`fits_all` (K12/FitsAll.lean), which holds AT EVERY input, front, family of coins and list of challenges, from sorts
and tables alone: the sorts by `test_sorts`, the widths by `test_widths`. So nothing is asked here of what the job's
`rec₀`, `rows₀` or `trees₀` make of the front.

Limits. Premises are premises: no job is shown here to meet them. `BlockPlays` holds for nothing where `chainSteps` at
the block does not return. Nothing on the columns, on a decision, on what is played, on completeness, on soundness
or on what is hidden.
-/
import E2E.OfflineRunsForm
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import E2E.OfflineGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (member_lengths zip_length)

variable {S Cl V W X Pb : Type}

/-- **`play` returns at a block that seats a proximity test**, the half being `proverSideOfProximityTest J`. -/
theorem blockPlays_k12 (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain : ℕ) (hs : List (Placed V W X))
    (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave) (Pre : Mid W X → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (plan : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true)
    (sorts : (laidOf J.p).map asked = [] :: bodyItems s (t :: rest))
    (tables : tablesFitB J = true)
    (HA : ∀ (k : Coins Bk) (m : Mid W X) (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      Pre m →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)) :
    BlockPlays φ Bk chain hs b Pre := by
  intro k m ds l hA hd _ hl
  have hpl := hb.place
  have hf' : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J) := by
    rw [hpl]
    exact hf
  obtain ⟨ho, hr⟩ := member_lengths hf' hl
  obtain ⟨c, hc, rfl⟩ := steps_one_half hf' hl
  rw [hpl] at hc
  have hdr := hd
  rw [hb.rounds] at hdr
  have ag := HA k m c hA hc
  have hs0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [hst]
    rfl
  rw [hs0] at ag
  have hz := zip_laid J.p plan
  have hzl := zip_length ho hr
  rw [hb.rounds, hb.oracles, hz] at hzl
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : (laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  have hzr : (laidOf J.p).length = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := by
    have ho' := ho
    rw [hb.rounds, hb.oracles] at ho'
    rw [← hz, List.length_zip, ho', Nat.min_self]
  have hlen : ds.length = (laidOf J.p).length := by
    rw [hzr]
    exact drawsFit_length _ _ hdr
  obtain ⟨y, hy⟩ := half_returns J s t rest hst hk b.name (φ.sees m.st.input) hrs c ds [] m ag
    sorts tables hlen
  refine ⟨y, ?_⟩
  unfold Placed.steps
  rw [hpl, hb.rounds, hb.oracles, hz]
  exact hy

/-- **From the plain half to the half behind the guard**, where Pre says that columns are handed. -/
theorem blockPlays_guarded {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs hs' : List (Placed V W X)} {b : Block S Cl} {Pre : Mid W X → Prop} (h : Placed V W X)
    (hf : (hs.find? fun g => g.place == b.place) = some h.needsField)
    (hf' : (hs'.find? fun g => g.place == b.place) = some h)
    (hopen : ∀ m, Pre m → m.opened.isSome = true)
    (hP : BlockPlays φ Bk chain hs' b Pre) : BlockPlays φ Bk chain hs b Pre := by
  intro k m ds l hA hd hst hl
  rw [chainSteps_behindGuard _ _ _ _ b hs hs' h hf hf'] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := ProofFile.Honest.map_ok hl
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 (hopen m hA)
  obtain ⟨y, h1⟩ := hP k m ds l₀ hA hd
    ((chainStop_behindGuard _ b hs hs' h hf hf' _ _).symm.trans hst) hl₀
  exact ⟨y, (play_behindGuard l₀ ds [] m cs hcs).trans h1⟩

/-- **`play` returns at a block that seats a proximity test**, the half being `proverSideOfProximityTest J` behind the
guard. -/
theorem blockPlays_k12_guarded (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain : ℕ)
    (hs : List (Placed V W X)) (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave) (Pre : Mid W X → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField)
    (plan : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true)
    (sorts : (laidOf J.p).map asked = [] :: bodyItems s (t :: rest))
    (tables : tablesFitB J = true)
    (hopen : ∀ m, Pre m → m.opened.isSome = true)
    (HA : ∀ (k : Coins Bk) (m : Mid W X) (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      Pre m →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J.p.place [(firstPart J : Part V W X), restPart J]
        0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)) :
    BlockPlays φ Bk chain hs b Pre := by
  have hp : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := by
    show (J.p.place == J.p.place) = true
    exact beq_self_eq_true _
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    simp [List.find?, hp]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == b.place) =
      some (proverSideOfProximityTest J : Placed V W X) := by
    rw [hb.place]
    exact f1
  have hf' : (hs.find? fun g => g.place == b.place) =
      some (proverSideOfProximityTest J : Placed V W X).needsField := by
    rw [hb.place]
    exact hf
  exact blockPlays_guarded (hs' := [(proverSideOfProximityTest J : Placed V W X)]) (proverSideOfProximityTest J) hf' f2 hopen
    (blockPlays_k12 φ Bk chain [proverSideOfProximityTest J] b J enter leave hb Pre s t rest hst hk f1 plan sorts
      tables HA)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.blockPlays_k12
#print axioms AtPublicFiles.OfflineRows.blockPlays_guarded
#print axioms AtPublicFiles.OfflineRows.blockPlays_k12_guarded
