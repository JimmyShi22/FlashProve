-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the key file's proximity test on G_omega: the public ties at the written place.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Key.lean: THE KEY FILE's TEST ON G_omega, where the first fold sends its own fresh table too (`piKOFull` has `ownMask` true): the sentences of the frame at its two members, general in the job, at a place that stands like `piKOFull`. All public premises are paid by Lean's kernel at `piKOFull`.

  `AtKeyPlace`       what a place must share with `piKOFull`: numbers, thin lists, code numbers, two flags
  `firstListAtKey`, `firstListAtKey_length`, `opens_at_written_key`   the list that the test's first switch opens
  `alike_key`, `alike_renum_key`, `planOB_key`, `reach_renum_key`, `declared_renum_key`   as at the proof file
  `firstPubOwn_key`, `publicTiesOwn_key`, `openTies_key`   the public ties at every job at such a place whose first fold sends its own table
  `exact_first_key`, `exact_free_key`, `exact_entry_key`   **`ExactMember` at the two members**
  `OnOmegaKey`, `key_omega_fields`, `key_omega_good`   the three fields and `Good` at the pair behind the guard, at A := False
  `atKeyPlace_pKO`   the library's seated place `pKO` stands like the written one

Limits. CONDITIONAL at the second member on `onFreeOwn`, `OnEntryOwn` or `OnOmegaKey`. The job is a letter: E2E/KeyProver.lean's half at that place is a letter too: that it is this job is not said here. `exact_first_key`, `exact_free_key`, `exact_entry_key` are at the bare pair, `key_omega_fields`, `key_omega_good` at the pair behind the guard. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.AtHead
import Johnson.Desc.ProofFile.Honest.K12.SimO.Top
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyPlaceFactsOwn
import Johnson.HB.LLHARD.KB8.TieK12

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest (ProverCoinCounts Coins Env Good Side Member Face Before fresh_of_nil)
open ProofFile.Honest.Small (FreshMember noneSpent spentBy_of_noneSpent)
open H2K.Member (piKOFull codesKeyFull)
open H2K.JointK (laidOf laidS)
open ProofFile.Honest.Small (ExactMember)
open Johnson.Prover.Link
open ProofFile.Honest.K12.Own (planOB renumP renum planOB_KO_full)

variable {S Cl V W X Pb : Type}

/-- **What a place must share with the written place.** -/
structure AtKeyPlace (p : P12) : Prop where
  nums : p.nums = piKOFull.nums
  thin : thinOf p = thinOf piKOFull
  idx : p.idx = piKOFull.idx
  early : p.early = piKOFull.early
  answers : p.answers = piKOFull.answers

/-- The list that the test's first switch opens, as the written place has it. -/
def firstListAtKey : List (Fmt.Shape × Fmt.TreeSource) :=
  ((((((laidOf piKOFull).map (·.1)).drop (firstLen piKOFull.nums.stages))[1]?).map (·.opens))).getD []

theorem firstListAtKey_length : firstListAtKey.length = 3 := by decide +kernel

theorem opens_at_written_key :
    ((((laidOf piKOFull).map (·.1)).drop (firstLen piKOFull.nums.stages))[1]?).map (·.opens) =
      some firstListAtKey := by
  decide +kernel

theorem written_key :
    (formPubB piKOFull && tabB piKOFull true && reachTB (renumP piKOFull) && piKOFull.nums.ownMask &&
      decide (firstLen piKOFull.nums.stages ≤ (laidOf piKOFull).length) &&
      decide ((piKOFull.nums.stages.headD default).Z.a ≤ 32) &&
      decide ((laidOf piKOFull).length = firstLen piKOFull.nums.stages + restLen piKOFull.nums.stages) &&
      decide (restLen piKOFull.nums.stages = 2 + lenFrom (stN piKOFull) (piKOFull.nums.stages.drop 2))) = true := by
  decide +kernel

theorem positions_renum_key :
    ((laidOf (renumP piKOFull)).map (·.1)).map (·.entry.poss) =
      ((laidOf piKOFull).map (·.1)).map (·.entry.poss) := by
  decide +kernel

theorem oracles_length_key :
    ((H2U.roundsOfNums piKOFull.nums).getD []).length ≤ piKOFull.oracles.length ∧
    ((H2U.roundsOfNums (renumP piKOFull).nums).getD []).length =
      ((H2U.roundsOfNums piKOFull.nums).getD []).length := by
  decide +kernel

section
variable {p : P12} (A : AtKeyPlace p)
include A

theorem alike_key : Alike p piKOFull where
  nums := A.nums
  idx := A.idx
  early := A.early
  answers := A.answers
  decls := by rw [decls_thin, decls_thin, A.thin]

theorem rounds_renum_key : (laidOf (renumP p)).map (·.1) = (laidOf (renumP piKOFull)).map (·.1) := by
  have e1 : (renumP p).nums = (renumP piKOFull).nums := by
    show renum p.nums = renum piKOFull.nums
    rw [A.nums]
  have hl : (laidOf p).length = (laidOf piKOFull).length := length_congr A.thin
  have h1 : (laidOf piKOFull).length = ((H2U.roundsOfNums piKOFull.nums).getD []).length := by
    unfold laidOf
    rw [List.length_zip]
    exact Nat.min_eq_left oracles_length_key.1
  have h2 : (laidOf p).length ≤ p.oracles.length := by
    unfold laidOf
    rw [List.length_zip]
    exact Nat.min_le_right _ _
  have h3 := oracles_length_key.2
  have l1 : ((H2U.roundsOfNums (renumP p).nums).getD []).length ≤ (renumP p).oracles.length := by
    rw [e1]
    show _ ≤ p.oracles.length
    omega
  have l2 : ((H2U.roundsOfNums (renumP piKOFull).nums).getD []).length ≤ (renumP piKOFull).oracles.length := by
    show _ ≤ piKOFull.oracles.length
    have := oracles_length_key.1
    omega
  rw [rounds_of_enough_oracles _ l1, rounds_of_enough_oracles _ l2, e1]

theorem alike_renum_key : Alike (renumP p) (renumP piKOFull) where
  nums := by
    show renum p.nums = renum piKOFull.nums
    rw [A.nums]
  idx := A.idx
  early := A.early
  answers := A.answers
  decls := rounds_renum_key A

theorem planOB_key : planOB p codesKeyFull 3 = true := by
  rw [planOB_alike (alike_key A) (alike_renum_key A)]
  exact planOB_KO_full

theorem reach_renum_key : reachTB (renumP p) = true := by
  have hs : (renumP p).nums.stages = (renumP piKOFull).nums.stages := congrArg (·.stages) A.nums
  rw [reachTB_reads hs rfl (rounds_renum_key A)]
  have k := written_key
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  exact k.1.1.1.1.1.2

theorem declared_renum_key (i : ℕ) : declared (renumP p) i = declared p i := by
  refine declared_of_rounds ?_ i
  rw [rounds_renum_key A, positions_renum_key, decls_thin p, A.thin, ← decls_thin]

/-- The public ties of the first member. -/
theorem firstPubOwn_key (J : TestJob W X) (hp : J.p = p) (hfr : J.fresh = none) (Js : SimJob Pb)
    (hJ : Js.p = p) (ho : Js.own = true) : FirstPubOwn J Js := by
  have k := written_key
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  obtain ⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, -⟩, -⟩, k5⟩, k6⟩, -⟩, -⟩ := k
  refine ⟨hJ.trans hp.symm, ho, ?_, ?_, ?_, ?_⟩
  · rw [hp, formPubB_congr A.nums A.thin]
    exact k1
  · rw [hp, A.nums, length_congr A.thin]
    exact k5
  · rw [tablesFitB_eq, hfr, hp]
    show tabB p true = true
    rw [tabB_congr A.nums A.thin]
    exact k2
  · show (J.p.nums.stages.headD default).Z.a ≤ 32
    rw [hp, A.nums]
    exact k6

/-- **The public ties of the second member.** -/
theorem publicTiesOwn_key (J : TestJob W X) (hp : J.p = p) (hfr : J.fresh = none) (Js : SimJob Pb)
    (hJ : Js.p = p) (ho : Js.own = true) : PublicTiesOwn J Js codesKeyFull 3 := by
  have F := firstPubOwn_key A J hp hfr Js hJ ho
  have k := written_key
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, k4⟩, -⟩, -⟩, k7⟩, k8⟩ := k
  refine ⟨hJ.trans hp.symm, ?_, ?_, ?_, ?_, ?_, F.form, ?_, ?_, F.tables⟩
  · rw [ho, hfr]
    rfl
  · rw [hp, A.nums]
    exact k4
  · rw [hp]
    exact reach_renum_key A
  · rw [hp]
    exact planOB_key A
  · rw [hp]
    exact declared_renum_key A
  · rw [hp, length_congr A.thin, A.nums]
    exact k7
  · show restLen J.p.nums.stages = 2 + lenFrom (stN J.p) (J.p.nums.stages.drop 2)
    unfold stN
    rw [hp, A.nums]
    exact k8

/-- `OpenTies` at every job at the place. -/
theorem openTies_key (J : TestJob W X) (Js : SimJob Pb) (hp : J.p = p) (chain : ℕ)
    (hop : Js.opens = firstListAtKey.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain firstListAtKey := by
  refine ⟨?_, hop⟩
  have e : ((((laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) = some firstListAtKey := by
    rw [hp, decls_thin p, A.thin, ← decls_thin, A.nums]
    exact opens_at_written_key
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **The first member.** At every On. -/
theorem exact_first_key (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (hp : J.p = p)
    (hfr : J.fresh = none) (Js : SimJob Pb) (hJ : Js.p = p) (ho : Js.own = true) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop) :
    ExactMember φ σ chain firstTree On (budBoth Js) (firstMember J Js) :=
  exact_first_job φ σ J Js chain firstTree On (by rw [hfr]; rfl) (firstPubOwn_key A J hp hfr Js hJ ho)

/-- **The second member.** Conditional on `onFreeOwn`. -/
theorem exact_free_key (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (hp : J.p = p)
    (hfr : J.fresh = none) (Js : SimJob Pb) (hJ : Js.p = p) (ho : Js.own = true) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtKey.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree (onFreeOwn φ J Js codesKeyFull chain firstListAtKey)
      (budOpened J.p.nums.stages) (restMember J Js) :=
  exact_free_own φ σ J Js codesKeyFull chain firstTree firstListAtKey
    (firstListAtKey_length ▸ publicTiesOwn_key A J hp hfr Js hJ ho) (openTies_key A J Js hp chain hop)

/-- **The second member, at a state that stands in.** -/
theorem exact_entry_key (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (hp : J.p = p)
    (hfr : J.fresh = none) (Js : SimJob Pb) (hJ : Js.p = p) (ho : Js.own = true) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtKey.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    ExactMember φ σ chain firstTree (OnEntryOwn φ J Js codesKeyFull chain firstListAtKey)
      (budOpened J.p.nums.stages) (restMember J Js) :=
  exact_entry_own φ σ J Js codesKeyFull chain firstTree firstListAtKey
    (firstListAtKey_length ▸ publicTiesOwn_key A J hp hfr Js hJ ho) (openTies_key A J Js hp chain hop)

/-- The condition at the guarded pair, at the key file's codes. -/
def OnOmegaKey (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ) :
    (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop :=
  fun u ca m front => (∃ cs, m.opened = some cs) ∧ OnEntryOwn φ J Js codesKeyFull chain firstListAtKey u ca m front

/-- **The three fields at the pair behind the guard, at the key file's test.** -/
theorem key_omega_fields (J : TestJob W X) (hp : J.p = p) (hfr : J.fresh = none) (Js : SimJob Pb)
    (hJ : Js.p = p) (ho : Js.own = true) (hk : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (fs : List (ProofFile.Honest.Fall S)) (bs : List (Block S Cl)) (σ : Side S Cl V W X Pb)
    (hσ : Side.seated bs p.place (omegaRow J Js) fs = some σ)
    (hr : σ.block.rounds = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds)
    (hor : σ.block.oracles = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).oracles)
    (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtKey.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree (OnOmegaKey φ J Js chain) (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hpl : b.place = p.place := by
    have := List.find?_some hb
    exact beq_iff_eq.1 this
  have hst : p.nums.stages = piKOFull.nums.stages := congrArg (·.stages) A.nums
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piKOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  have hst' : J.p.nums.stages = s :: t :: rest := by rw [hp, hst, hlit]
  have hk' : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true := by rw [hp]; exact hk
  have hcount := (publicTiesOwn_key A J hp hfr Js hJ ho).count
  have hr' : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds := by rw [hp]; exact hr
  have hor' : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles := by rw [hp]; exact hor
  have hfit := fits_of (V := V) J Js (hJ.trans hp.symm) b (ProofFile.Honest.fallOf fs p.place) (hpl.trans (congrArg (·.place) hp).symm)
    hk' hr' hor' s t rest hst' hcount
  have hbare : testSide (V := V) bs J Js fs =
      some (⟨b, testPairs J Js, ProofFile.Honest.fallOf fs p.place⟩ : Side S Cl V W X Pb) := by
    unfold testSide Side.seated
    show Option.map _ (bs.find? fun b => b.place == J.p.place) = _
    rw [hp, hb]
    rfl
  have hmem := members_of_seat bs J Js fs _ hbare (by
      show b.rounds.zip b.oracles = _
      rw [hr', hor']
      exact zip_laid J.p hk') s t rest hst' hcount
  refine ⟨?_, ?_, ?_⟩
  · show (⟨b, guardRow _, _⟩ : Side S Cl V W X Pb).fits = true
    rw [fits_guardRow]
    exact hfit
  · have hm : (⟨b, omegaRow J Js, ProofFile.Honest.fallOf fs p.place⟩ : Side S Cl V W X Pb).members =
        [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      show membersOf (guardRow _) 0 _ = _
      rw [membersOf_guardRow]
      have := congrArg (List.map Member.guarded) hmem
      exact this
    intro u hu
    have hu' : u ∈ [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      rw [← hm]
      exact hu
    rcases List.mem_cons.1 hu' with rfl | hu
    · refine exact_guarded (On := fun _ _ _ _ => True) (fun ca m front hOn => ⟨trivial, hOn.1⟩) ?_
      exact exact_first_key A φ _ J hp hfr Js hJ ho chain firstTree _
    · rcases List.mem_singleton.1 hu with rfl
      refine exact_guarded (On := OnEntryOwn φ _ Js codesKeyFull chain firstListAtKey) (fun ca m front hOn => ⟨hOn.2, hOn.1⟩) ?_
      refine exact_bud (bud := budOpened J.p.nums.stages) (fun ds asks hb => ?_)
        (exact_entry_key A φ _ J hp hfr Js hJ ho chain firstTree hop)
      have h2 := hb.2
      rw [hJ, ← hp] at h2
      exact h2
  · intro u hu p' sp ca m ds asks _ _ _
    exact fresh_of_nil _ (spentBy_of_noneSpent (hB u hu) p') _ _

/-- **`Good` at the pair behind the guard, at the key file's test, at A := False.** -/
theorem key_omega_good (J : TestJob W X) (hp : J.p = p) (hfr : J.fresh = none) (Js : SimJob Pb)
    (hJ : Js.p = p) (ho : Js.own = true) (hk : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (fs : List (ProofFile.Honest.Fall S)) (bs : List (Block S Cl)) (σ : Side S Cl V W X Pb)
    (hσ : Side.seated bs p.place (omegaRow J Js) fs = some σ)
    (hr : σ.block.rounds = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds)
    (hor : σ.block.oracles = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).oracles)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtKey.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (Bk : ProverCoinCounts) (ord : List Place) (B : Coins Bk → S → ProofFile.Honest.Mid W X → Env → Prop)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B (OnOmegaKey φ J Js chain) (budBoth Js) := by
  obtain ⟨hf, he, hfr'⟩ := key_omega_fields A J hp hfr Js hJ ho hk fs bs σ hσ hr hor φ chain firstTree hop Bk ord hB
  exact { fits := hf
          plays := fun _ _ _ _ _ hA => hA.elim
          acc := fun _ _ _ _ _ hA => hA.elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (he u hu)
          fresh := hfr' }

end

/-- **The key file's seated place stands like the written one**: by Lean's kernel. -/
theorem atKeyPlace_pKO : AtKeyPlace pKO :=
  have hn : pKO.nums = piKOFull.nums := Johnson.KB8.o_tie
  have hp : (proximityTestKind guardedProximityTestParts piKOFull : Block T12 Unit).planOk = true := by decide +kernel
  { nums := hn
    thin := thin_of_planOk guardedProximityTestParts hn plan_KO hp
    idx := by decide +kernel
    early := by decide +kernel
    answers := by decide +kernel }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.key_omega_fields
#print axioms ProofFile.Honest.K12.Light.key_omega_good
#print axioms ProofFile.Honest.K12.Light.atKeyPlace_pKO
#print axioms ProofFile.Honest.K12.Light.written_key
#print axioms ProofFile.Honest.K12.Light.planOB_key
#print axioms ProofFile.Honest.K12.Light.publicTiesOwn_key
#print axioms ProofFile.Honest.K12.Light.openTies_key
#print axioms ProofFile.Honest.K12.Light.exact_first_key
#print axioms ProofFile.Honest.K12.Light.exact_free_key
#print axioms ProofFile.Honest.K12.Light.exact_entry_key
