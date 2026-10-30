-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the test on the ranges.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowRanges.lean: the row number 5 of the offline clause: the
proximity test on the ranges, at the key file's first chain, place ⟨1, none, 5, .K12⟩ (K.rng :=
proverSideOfProximityTest (rangesTestJob …)): fits, exact at both members, fresh; Good at an A that never holds, B free.

  dsKR, facts_KRFull, reachT_KR, restLen_KR, opens_KRFull   the written place, by Lean's kernel
  find_ranges       the search at the place, in the key file's first chain
  pubTies_ranges, openTies_ranges   the two public premises
  slot_ranges       fits, exact, fresh
  ranges_good       Good, at every job and simulators' job at the place
  stateAtRanges, simRanges, recRanges_is_view   the simulators' job; one function on both sides
  spent_rng_full    nothing is spent of the two parts at the key's book, by the kernel
  ranges_row        Good at rangesTestJob, simRanges and keyBook K, where fullPub = some K

Limits. Conditional on OnEntry at a run, which this file does not show; plays and acc are asked at an A
that never holds. The side is testSide's: that keyProver's half is the side's row is read off the
prover's text, no lemma here. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyRangesK12
import E2E.KeyRangesJob
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Entry
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FreshAny
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.AtKeyRanges
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead
import E2E.KeyPlacesNamed
import E2E.KeyPublic
import E2E.KeyBookAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi rangesParams)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open H2K.Member (piKRFull codesKeyFull)
open H2K.JointK (rngEntry)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeySourced)
open AtPublicFiles.KeyBook (places_named fullFirst rngPlace)
open AtPublicFiles.KeyThread (member15 seatOf_rngEntry place_sourced)

/-- As many challenges as the first part has rounds, each of one field element. -/
def dsKR : List Fmt.Drawn :=
  List.replicate (firstLen piKRFull.nums.stages) ⟨[(1, 0, 0)], [], [], none⟩

theorem facts_KRFull : PlaceFacts piKRFull dsKR :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem reachT_KR : reachTB piKRFull = true := by decide +kernel

theorem restLen_KR : restLen piKRFull.nums.stages =
    2 + lenFrom (stN piKRFull) (piKRFull.nums.stages.drop 2) := by decide +kernel

theorem opens_KRFull :
    ((((H2K.JointK.laidOf piKRFull).map (·.1)).drop (firstLen piKRFull.nums.stages))[1]?).map (·.opens) =
      some piKRFull.nums.first := by decide +kernel

theorem first_KR_length : piKRFull.nums.first.length = 1 := by decide +kernel

section Key
variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces} {V W X Pb : Type}

theorem fifteen_off : ((fullFirst.take 15).all fun r => r.1 != rngPlace) = true := by decide +kernel

theorem fifteen_at : (fullFirst[15]?).map (·.1) = some rngPlace := by decide +kernel

/-- The search finds what stands at a number where nothing in front answers. -/
theorem find_at_index {α : Type} (l : List α) (p : α → Bool) (i : ℕ) (e : α) (g : l[i]? = some e)
    (hp : p e = true) (hn : ∀ b ∈ l.take i, p b = false) : l.find? p = some e := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.1 g
  have hc : l = l.take i ++ e :: l.drop (i + 1) := by
    rw [← he, List.getElem_cons_drop, List.take_append_drop]
  have h0 : (l.take i).find? p = none := by
    refine List.find?_eq_none.2 fun b hb hb' => ?_
    rw [hn b hb] at hb'
    cases hb'
  rw [hc, List.find?_append, h0, List.find?_cons_of_pos hp]
  rfl

/-- **The search at the test's place, in the key file's first chain.** -/
theorem find_ranges (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) (J : TestJob W X)
    (hJ : J.p = rangesParams N) :
    ∃ b, ((keyFileDescription Xs N Pl).first.blocksInOrder.find? fun b => b.place == J.p.place) = some b ∧
      b.place = J.p.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block VerifiableInference.Desc.K12.T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block VerifiableInference.Desc.K12.T12 Unit).oracles := by
  have S := seatOf_rngEntry Xs.Y.k.oneTime N J hJ
  have g := member15 scope h
  have r := (places_named scope h).1
  have q : ((keyFileDescription Xs N Pl).first.blocksInOrder[15]?).map (fun b => (b.place, b.rounds.length)) =
      fullFirst[15]? := by
    rw [← List.getElem?_map]
    exact congrArg (·[15]?) r
  have q2 := (congrArg (Option.map fun b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl =>
    (b.place, b.rounds.length)) g).symm.trans q
  have e := fifteen_at
  rw [← q2] at e
  have hpl : (rngEntry Xs.Y.k.oneTime N).place = rngPlace := Option.some.inj e
  refine ⟨_, find_at_index _ _ 15 _ g ?_ fun b hb => ?_, S.place, S.rounds, S.oracles⟩
  · rw [← S.place]
    exact beq_self_eq_true _
  · rw [← S.place, hpl]
    have hm : (b.place, b.rounds.length) ∈ fullFirst.take 15 := by
      rw [← r]
      show _ ∈ ((keyFileDescription Xs N Pl).first.blocksInOrder.map fun b => (b.place, b.rounds.length)).take 15
      rw [← List.map_take]
      exact List.mem_map_of_mem (f := fun b => (b.place, b.rounds.length)) hb
    have hne := List.all_eq_true.1 fifteen_off _ hm
    simpa using hne

/-- **The two public premises.** -/
theorem pubTies_ranges {K : OnBytes.Codes} (hK : K = codesKeyFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hs : Js.p = piKRFull)
    (ho : Js.own = false) : PubTiesT J Js K 1 := by
  subst hK
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ]
    exact reachT_KR
  · rw [hJ]
    exact planB_KR
  · rw [hJ]
    exact facts_KRFull.form
  · rw [hJ]
    exact facts_KRFull.count
  · rw [hJ]
    exact restLen_KR
  · rw [tablesFitB_eq, hfr, hJ]
    exact facts_KRFull.tab

theorem openTies_ranges (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = piKRFull) (chain : ℕ)
    (hop : Js.opens = piKRFull.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain piKRFull.nums.first := by
  refine ⟨?_, hop⟩
  have e : ((((H2K.JointK.laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some piKRFull.nums.first := by
    rw [hJ]
    exact opens_KRFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **fits, exact and fresh at the side of the test on the ranges.** -/
theorem slot_ranges (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (hp : rangesParams N = piKRFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hs : Js.p = piKRFull)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = piKRFull.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : testSide (keyFileDescription Xs N Pl).first.blocksInOrder J Js fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (OnEntry φ J Js codesKeyFull chain piKRFull.nums.first) (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_ranges scope h J (hJ.trans hp.symm)
  have F : PlaceFacts J.p dsKR := by
    rw [hJ]
    exact facts_KRFull
  obtain ⟨T₀, -, hall⟩ := any_at_place (V := V) J Js F _ b hf hpl hr hor hfr (hs.trans hJ.symm) ho
  obtain ⟨hfit, hmem, -⟩ := hall fs σ hσ
  have T : PubTiesT J Js codesKeyFull piKRFull.nums.first.length := by
    rw [first_KR_length]
    exact pubTies_ranges rfl J Js hJ hfr hs ho
  have To := openTies_ranges J Js hJ chain hop
  refine ⟨hfit, fun u hu => ?_, fun u hu => fresh_member φ σ Bk ord _ u (hB u hu)⟩
  rw [hmem] at hu
  exact exact_both_entry φ σ J Js codesKeyFull chain firstTree _ hfr T₀ T To u hu

/-- **Good at that side, at A := False.** -/
theorem ranges_good (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (hp : rangesParams N = piKRFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) (hs : Js.p = piKRFull)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = piKRFull.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : testSide (keyFileDescription Xs N Pl).first.blocksInOrder J Js fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts) (ord : List Place)
    (A B : Coins Bk → (keyFileDescription Xs N Pl).S₁ → ProofFile.Honest.Mid W X → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree A B
      (OnEntry φ J Js codesKeyFull chain piKRFull.nums.first) (budBoth Js) := by
  obtain ⟨hf, he, hfr'⟩ := slot_ranges scope h hp J Js hJ hfr hs ho φ chain firstTree hop fs σ hσ Bk
    ord hB
  exact { fits := hf
          plays := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          acc := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (he u hu)
          fresh := hfr' }

end Key

/-! ## At the key's own job, book and simulator -/

section Term
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub)
open AtPublicFiles.KeyThread (rangesTestJob recRanges)
open AtPublicFiles.AtFiles (rangesState)
open VerifiableInference.Desc (foldBlocks)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The simulators' state on entry**: the replay of recRanges, of the public part and of what a
Before shows. -/
def stateAtRanges (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (Pl : VerifiableInference.Desc.Key.LaterPlaces) (pb : Xi) (f : Before) :
    VerifiableInference.Desc.K12.T12 :=
  match foldBlocks 0 ((keyFileDescription Xs N Pl).first.blocksInOrder.take 15) ((keyFileDescription Xs N Pl).start₁ pb) f.seen [] with
  | .ok x => rangesState x.1
  | .error _ => rangesState ((keyFileDescription Xs N Pl).start₁ pb)

/-- **The simulators' job at the test on the ranges.** -/
def simRanges (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (Pl : VerifiableInference.Desc.Key.LaterPlaces) : SimJob Xi :=
  ⟨piKRFull, false, stateAtRanges Xs N Pl, piKRFull.nums.first.map fun x =>
    ((ProofFile.Honest.srcOf 0 x.2).1, (ProofFile.Honest.srcOf 0 x.2).2, x.1.a)⟩

/-- The one function on both sides: where the two rounds shown are one, the job's state on entry is
the simulators'. -/
theorem recRanges_is_view {W₀ Rc X' : Type} (w : Local W₀ Rc Xi Unit) (fr : Front X') (f : Before)
    (h : fr.seen.rounds = f.seen) :
    recRanges Xs N Pl w fr = stateAtRanges Xs N Pl ((keyFileDescription Xs N Pl).pub w.x) f := by
  unfold recRanges stateAtRanges
  rw [h]
  rfl

theorem spent_rng_full : (fullPub.map fun K => noneSpent (keyBook K) ⟨rngPlace, 0⟩ &&
    noneSpent (keyBook K) ⟨rngPlace, 1⟩) = some true := by decide +kernel

theorem place_KR : piKRFull.place = rngPlace := by decide +kernel

/-- **Row 5**: Good at the job that keyProver lays, at the simulators' job, at the key's book. -/
theorem ranges_row {W₀ Rc X' V : Type} (scope : VerifierAndGoals.InScope Z = true)
    (hS : KeySourced Z Xs N Pl) {K : KeyPub} (hK : fullPub = some K)
    (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → OnBytes.Slice.GF) (groups : List (List ℕ)) (first : ℕ)
    (φ : Face V (Local W₀ Rc Xi Unit) Xi) (firstTree : ℕ)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl V (Local W₀ Rc Xi Unit) X'
      Xi)
    (hσ : testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob Xs N Pl entry groups first)
      (simRanges Xs N Pl) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₁ → ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) X' → Env →
      Prop) (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 0 firstTree A B
      (OnEntry φ (rangesTestJob Xs N Pl entry groups first) (simRanges Xs N Pl) codesKeyFull 0
        piKRFull.nums.first) (budBoth (simRanges Xs N Pl)) := by
  have hp := place_sourced hS scope
  have hJ : (rangesTestJob (X' := X') Xs N Pl entry groups first).p = piKRFull := hp
  have hfr : (rangesTestJob (X' := X') Xs N Pl entry groups first).fresh.isNone = false := rfl
  have hsp := spent_rng_full
  rw [hK] at hsp
  have hsp' : (noneSpent (keyBook K) ⟨rngPlace, 0⟩ && noneSpent (keyBook K) ⟨rngPlace, 1⟩) = true :=
    Option.some.inj hsp
  simp only [Bool.and_eq_true] at hsp'
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_ranges scope hS.named (rangesTestJob (X' := X') Xs N Pl entry groups
    first) rfl
  have F : PlaceFacts (rangesTestJob (X' := X') Xs N Pl entry groups first).p dsKR := by
    rw [hJ]
    exact facts_KRFull
  obtain ⟨-, -, hall⟩ := any_at_place (V := V) (rangesTestJob (X' := X') Xs N Pl entry groups first)
    (simRanges Xs N Pl) F _ b hf hpl hr hor hfr hJ.symm rfl
  obtain ⟨-, hmem, -⟩ := hall fs σ hσ
  have hbp : σ.block.place = rngPlace := by
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hσ
    have hb2 : b' = b := Option.some.inj (hb'.symm.trans hf)
    show b'.place = _
    rw [hb2, hpl, hJ]
    exact place_KR
  refine ranges_good scope hS.named hp _ _ hJ hfr rfl rfl φ 0 firstTree rfl fs σ hσ pre _ ord A B hA
    fun u hu => ?_
  rw [hmem] at hu
  rw [hbp]
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact hsp'.1
  · rcases List.mem_singleton.1 hu' with rfl
    exact hsp'.2

end Term

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.facts_KRFull
#print axioms ProofFile.Honest.K12.Sim2.reachT_KR
#print axioms ProofFile.Honest.K12.Sim2.restLen_KR
#print axioms ProofFile.Honest.K12.Sim2.opens_KRFull
#print axioms ProofFile.Honest.K12.Sim2.find_ranges
#print axioms ProofFile.Honest.K12.Sim2.slot_ranges
#print axioms ProofFile.Honest.K12.Sim2.ranges_good
#print axioms ProofFile.Honest.K12.Sim2.recRanges_is_view
#print axioms ProofFile.Honest.K12.Sim2.spent_rng_full
#print axioms ProofFile.Honest.K12.Sim2.ranges_row
