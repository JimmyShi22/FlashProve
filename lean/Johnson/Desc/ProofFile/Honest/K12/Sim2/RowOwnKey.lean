-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the key file's own test.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowOwnKey.lean: row 16 of the offline clause: the proximity
test on the own group, at the key file's last chain, place ⟨3, none, 2, .K12⟩, behind the guard
(proverSideOfGuardedSending, E2E/KeyProverSideOfOwnTest.lean): fits, exact at both guarded members, fresh, and Good at A := False at
any stand. The twin of RowRanges.lean with SlotOwnTest.lean's guard.

  dsKW, facts_KWFull, reachT_KW, planB_KW, restLen_KW, opens_KWFull   the written place, by kernel
  place_k12, second_flat_key, find_own_key   the search at the place, in the key file's last chain
  slot_own_key, own_key_good   at every job and simulators' job at the place
  stateAtOwnKey, simOwnKey   the simulators' job
  spent_own_full, own_sourced, own_key_row, own_key_row_at_half   Good at the simulators' job and
                    keyBook K, at a job at the place and at the job that proverSideOfGuardedSending lays

Limits. Conditional on OnEntry. No property of the protocol is claimed.
-/
import E2E.KeyProverSideOfOwnTest
import E2E.KeyProtocolOverDescription
import E2E.KeyShapeSharedTies
import E2E.KeyPublic
import E2E.KeyBookAtWritten
import Johnson.Unfolds.SplitOn
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotOwnTest
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open H2K.Member (piKWFull codesKeyFull)
open AtPublicFiles.AtFiles (keyFileDescription)

/-- As many challenges as the first part has rounds, each of one field element. -/
def dsKW : List Fmt.Drawn :=
  List.replicate (firstLen piKWFull.nums.stages) ⟨[(1, 0, 0)], [], [], none⟩

theorem facts_KWFull : PlaceFacts piKWFull dsKW :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

theorem reachT_KW : reachTB piKWFull = true := by decide +kernel

theorem restLen_KW : restLen piKWFull.nums.stages =
    2 + lenFrom (stN piKWFull) (piKWFull.nums.stages.drop 2) := by decide +kernel

theorem opens_KWFull :
    ((((H2K.JointK.laidOf piKWFull).map (·.1)).drop (firstLen piKWFull.nums.stages))[1]?).map (·.opens) =
      some piKWFull.nums.first := by decide +kernel

theorem planB_KW : planB piKWFull codesKeyFull piKWFull.nums.first.length = true := by
  decide +kernel

theorem place_k12 (p : VerifiableInference.Desc.K12.P12) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Unit).place = p.place := by
  unfold proximityTestKind
  split <;> rfl

theorem first_KW_length : piKWFull.nums.first.length = 3 := by decide +kernel

section Key
variable {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces} {V W X Pb : Type}

/-- A list whose image has four members has four. -/
theorem four_of_map {α β : Type} (L : List α) (f : α → β) (x₀ x₁ x₂ x₃ : β)
    (h : L.map f = [x₀, x₁, x₂, x₃]) :
    ∃ a b c d, L = [a, b, c, d] ∧ f a = x₀ ∧ f b = x₁ ∧ f c = x₂ ∧ f d = x₃ := by
  match L, h with
  | [a, b, c, d], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨a, b, c, d, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

theorem find_third {α : Type} (p : α → Bool) (a b c d : α) (ha : p a = false) (hb : p b = false)
    (hc : p c = true) : [a, b, c, d].find? p = some c := by
  simp [List.find?, ha, hb, hc]

/-- The key file's last chain, as a list of four. -/
theorem second_flat_key :
    (VerifiableInference.Desc.Key.descriptionFromSource Xs N Pl).second.blocksInOrder.map
        (fun b => (b.place, b.rounds, b.oracles)) =
      [(⟨3, none, 0, .K14⟩, [], []), (⟨3, none, 1, .frame⟩, [], []),
       (⟨3, none, 2, (proximityTestKind guardedProximityTestParts (AtPublicFiles.KeyLay.pWK Pl) : Block T12 Unit).place.kind⟩,
         (proximityTestKind guardedProximityTestParts (AtPublicFiles.KeyLay.pWK Pl) : Block T12 Unit).rounds,
         (proximityTestKind guardedProximityTestParts (AtPublicFiles.KeyLay.pWK Pl) : Block T12 Unit).oracles),
       (⟨3, none, 3, .frame⟩, [], [])] := rfl

/-- **The search at the test's place, in the key file's last chain.** -/
theorem find_own_key (J : TestJob W X) (hJ : J.p = AtPublicFiles.KeyLay.pWK Pl)
    (hq : (AtPublicFiles.KeyLay.pWK Pl).place = ⟨3, none, 2, .K12⟩) :
    ∃ b, ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == J.p.place) = some b ∧
      b.place = J.p.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles := by
  have hm := second_flat_key (Xs := Xs) (N := N) (Pl := Pl)
  have hk : (proximityTestKind guardedProximityTestParts (AtPublicFiles.KeyLay.pWK Pl) : Block T12 Unit).place.kind = .K12 := by
    rw [place_k12, hq]
  have hP : J.p.place = ⟨3, none, 2, .K12⟩ := by
    rw [hJ]
    exact hq
  rw [hk] at hm
  obtain ⟨a, b, c, d, e, fa, fb, fc, -⟩ := four_of_map _ _ _ _ _ _ hm
  simp only [Prod.mk.injEq] at fa fb fc
  obtain ⟨a1, -, -⟩ := fa
  obtain ⟨b1, -, -⟩ := fb
  obtain ⟨c1, c2, c3⟩ := fc
  refine ⟨c, ?_, c1.trans hP.symm, ?_, ?_⟩
  · rw [e]
    refine find_third _ a b c d ?_ ?_ ?_
    · show (a.place == J.p.place) = false
      rw [a1, hP]
      decide
    · show (b.place == J.p.place) = false
      rw [b1, hP]
      decide
    · show (c.place == J.p.place) = true
      rw [c1, hP]
      decide
  · rw [hJ]
    exact c2
  · rw [hJ]
    exact c3

/-- **fits, exact and fresh at the guarded side.** -/
theorem slot_own_key (hp : AtPublicFiles.KeyLay.pWK Pl = piKWFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = piKWFull) (hfr : J.fresh.isNone = false) (hs : Js.p = piKWFull)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = piKWFull.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₃))
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (OnOwnTestEntry φ J Js codesKeyFull chain piKWFull.nums.first) (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨b', hf, hpl, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl) J (hJ.trans hp.symm)
    (by rw [hp]; rfl)
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  obtain rfl : b' = b := Option.some.inj (hf.symm.trans hb)
  have hbare : testSide (V := V) (keyFileDescription Xs N Pl).second.blocksInOrder J Js fs =
      some (⟨b', testPairs J Js, fallOf fs J.p.place⟩ :
        Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb) := by
    unfold testSide Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == J.p.place) = _
    rw [hb]
    rfl
  have F : PlaceFacts J.p dsKW := by
    rw [hJ]
    exact facts_KWFull
  obtain ⟨T₀, -, hall⟩ := any_at_place (V := V) J Js F _ b' hf hpl hr hor hfr (hs.trans hJ.symm) ho
  obtain ⟨hfit, hmem, -⟩ := hall fs _ hbare
  have T : PubTiesT J Js codesKeyFull piKWFull.nums.first.length := by
    refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hJ]
      exact reachT_KW
    · rw [hJ]
      exact planB_KW
    · rw [hJ]
      exact facts_KWFull.form
    · rw [hJ]
      exact facts_KWFull.count
    · rw [hJ]
      exact restLen_KW
    · rw [tablesFitB_eq, hfr, hJ]
      exact facts_KWFull.tab
  have To : OpenTies J Js chain piKWFull.nums.first := by
    refine ⟨?_, hop⟩
    have e : ((((H2K.JointK.laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map
        (·.opens) = some piKWFull.nums.first := by
      rw [hJ]
      exact opens_KWFull
    rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
    obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
    exact ⟨d, hd, hdo⟩
  have hm : (⟨b', guardRow (testPairs J Js), fallOf fs J.p.place⟩ :
      Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb).members =
      [(firstMember J Js).guarded, (restMember J Js).guarded] := by
    show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hmem
  have E := exact_both_entry φ (⟨b', guardRow (testPairs J Js), fallOf fs J.p.place⟩ :
    Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb) J Js codesKeyFull chain firstTree _ hfr
    T₀ T To
  refine ⟨?_, fun u hu => ?_, fun u hu => fresh_member φ _ Bk ord _ u (hB u hu)⟩
  · show (⟨b', guardRow _, _⟩ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb).fits = true
    rw [fits_guarded_row]
    exact hfit
  · have hu' : u ∈ [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      rw [← hm]
      exact hu
    rcases List.mem_cons.1 hu' with rfl | hu₂
    · exact exact_guarded (On := OnEntry φ J Js codesKeyFull chain piKWFull.nums.first)
        (fun ca m front hOn => ⟨hOn.2, hOn.1⟩) (E _ List.mem_cons_self)
    · rcases List.mem_singleton.1 hu₂ with rfl
      exact exact_guarded (On := OnEntry φ J Js codesKeyFull chain piKWFull.nums.first)
        (fun ca m front hOn => ⟨hOn.2, hOn.1⟩)
        (E _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Good at that side, at A := False.** -/
theorem own_key_good (hp : AtPublicFiles.KeyLay.pWK Pl = piKWFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = piKWFull) (hfr : J.fresh.isNone = false) (hs : Js.p = piKWFull)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = piKWFull.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₃))
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts) (ord : List Place)
    (A B : Coins Bk → (keyFileDescription Xs N Pl).S₃ → ProofFile.Honest.Mid W X → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree A B
      (OnOwnTestEntry φ J Js codesKeyFull chain piKWFull.nums.first) (budBoth Js) := by
  obtain ⟨hf, he, hfr'⟩ := slot_own_key hp J Js hJ hfr hs ho φ chain firstTree hop fs σ hσ Bk ord hB
  exact { fits := hf
          plays := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          acc := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (he u hu)
          fresh := hfr' }

end Key

/-! ## At the key's own book and simulator -/

section Term
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub ownTestPlace)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest.K12.AtProof (placeW idleT12)
open AtPublicFiles.AtFiles (KeySourced)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The simulators' state on entry**: the last chain's door over what a Before shows. -/
def stateAtOwnKey (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (Pl : VerifiableInference.Desc.Key.LaterPlaces) :
    VerifiableInference.Desc.Key.Xi → Before → T12 :=
  stateFromViewOnLastChain (keyFileDescription Xs N Pl)
    ((keyFileDescription Xs N Pl).second.blocksInOrder.takeWhile (·.place != placeW)) enterOwn idleT12

/-- **The simulators' job at the key's own test.** -/
def simOwnKey (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (Pl : VerifiableInference.Desc.Key.LaterPlaces) : SimJob VerifiableInference.Desc.Key.Xi :=
  ⟨piKWFull, false, stateAtOwnKey Xs N Pl, piKWFull.nums.first.map fun x =>
    ((ProofFile.Honest.srcOf 2 x.2).1, (ProofFile.Honest.srcOf 2 x.2).2, x.1.a)⟩

theorem spent_own_full : (fullPub.map fun K => noneSpent (keyBook K) ⟨ownTestPlace, 0⟩ &&
    noneSpent (keyBook K) ⟨ownTestPlace, 1⟩) = some true := by decide +kernel

theorem place_KW : piKWFull.place = ownTestPlace := by decide +kernel

/-- In scope the seated numbers are the written ones. -/
theorem own_sourced (hS : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    AtPublicFiles.KeyLay.pWK Pl = piKWFull := by
  rw [AtPublicFiles.AtFiles.Full.later_sourced hS scope]
  rfl

/-- **Row 16**: Good at a job at the place, at the simulators' job, at the key's book. -/
theorem own_key_row {V W X : Type} (scope : VerifierAndGoals.InScope Z = true)
    (hS : KeySourced Z Xs N Pl) {K : KeyPub} (hK : fullPub = some K) (J : TestJob W X)
    (hJ : J.p = AtPublicFiles.KeyLay.pWK Pl) (hfr : J.fresh.isNone = false)
    (φ : Face V W VerifiableInference.Desc.Key.Xi) (firstTree : ℕ)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₃))
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X VerifiableInference.Desc.Key.Xi)
    (hσ : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder J.p.place
      (guardRow (testPairs J (simOwnKey Xs N Pl))) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₃ → ProofFile.Honest.Mid W X → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 2 firstTree A B
      (OnOwnTestEntry φ J (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first)
      (budBoth (simOwnKey Xs N Pl)) := by
  have hp := own_sourced hS scope
  have hJ' : J.p = piKWFull := hJ.trans hp
  have hsp := spent_own_full
  rw [hK] at hsp
  have hsp' : (noneSpent (keyBook K) ⟨ownTestPlace, 0⟩ && noneSpent (keyBook K) ⟨ownTestPlace, 1⟩) =
      true := Option.some.inj hsp
  simp only [Bool.and_eq_true] at hsp'
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hbp : b'.place = ownTestPlace := by
    have e := (List.find?_some hb')
    have e' : b'.place = J.p.place := by simpa using e
    rw [e', hJ']
    exact place_KW
  have hmem : (⟨b', guardRow (testPairs J (simOwnKey Xs N Pl)), fallOf fs J.p.place⟩ :
      Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X VerifiableInference.Desc.Key.Xi).members =
      [(firstMember J (simOwnKey Xs N Pl)).guarded, (restMember J (simOwnKey Xs N Pl)).guarded] := by
    obtain ⟨b₂, hf, hpl, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl) J hJ (by rw [hp]; rfl)
    obtain rfl : b₂ = b' := Option.some.inj (hf.symm.trans hb')
    have hbare : testSide (V := V) (keyFileDescription Xs N Pl).second.blocksInOrder J (simOwnKey Xs N Pl) fs =
        some (⟨b₂, testPairs J (simOwnKey Xs N Pl), fallOf fs J.p.place⟩ :
          Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V W X VerifiableInference.Desc.Key.Xi) := by
      unfold testSide Side.seated
      show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == J.p.place) = _
      rw [hb']
      rfl
    have F : PlaceFacts J.p dsKW := by
      rw [hJ']
      exact facts_KWFull
    obtain ⟨-, -, hall⟩ := any_at_place (V := V) J (simOwnKey Xs N Pl) F _ b₂ hf hpl hr hor hfr
      hJ'.symm rfl
    obtain ⟨-, hm₀, -⟩ := hall fs _ hbare
    show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hm₀
  refine own_key_good hp J _ hJ' hfr rfl rfl φ 2 firstTree rfl fs _ (by
      show Option.map _ _ = _
      rw [hb']
      rfl) pre _ ord A B hA fun u hu => ?_
  rw [hmem] at hu
  show noneSpent _ ⟨b'.place, _⟩ = true
  rw [hbp]
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact hsp'.1
  · rcases List.mem_singleton.1 hu' with rfl
    exact hsp'.2

/-- **The same at the job that proverSideOfGuardedSending lays.** -/
theorem own_key_row_at_half {V W₀ Rc Tr Y Wd : Type} (scope : VerifierAndGoals.InScope Z = true)
    (hS : KeySourced Z Xs N Pl) {K : KeyPub} (hK : fullPub = some K)
    (JI JW : ProofFile.Honest.K1.SendJob Wd Y) (Sp : ProofFile.Honest.K14.SendPub)
    (lift : Local W₀ Rc VerifiableInference.Desc.Key.Xi Tr → Wd)
    (ask : Local W₀ Rc VerifiableInference.Desc.Key.Xi Tr → ProofFile.Honest.K14.Ask)
    (φ : Face V (Local W₀ Rc VerifiableInference.Desc.Key.Xi Tr) VerifiableInference.Desc.Key.Xi)
    (firstTree : ℕ) (fs : List (Fall (keyFileDescription Xs N Pl).S₃))
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V
      (Local W₀ Rc VerifiableInference.Desc.Key.Xi Tr) Y VerifiableInference.Desc.Key.Xi)
    (hσ : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder
      (AtPublicFiles.KeyLay.jobKWAt Xs N Pl JI JW Sp lift ask).toRun.toTest.p.place
      (guardRow (testPairs (AtPublicFiles.KeyLay.jobKWAt Xs N Pl JI JW Sp lift ask).toRun.toTest
        (simOwnKey Xs N Pl))) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₃ →
      ProofFile.Honest.Mid (Local W₀ Rc VerifiableInference.Desc.Key.Xi Tr) Y → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 2 firstTree A B
      (OnOwnTestEntry φ (AtPublicFiles.KeyLay.jobKWAt Xs N Pl JI JW Sp lift ask).toRun.toTest
        (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first)
      (budBoth (simOwnKey Xs N Pl)) :=
  own_key_row scope hS hK _ rfl rfl φ firstTree fs σ hσ pre ord A B hA

end Term

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.facts_KWFull
#print axioms ProofFile.Honest.K12.Sim2.reachT_KW
#print axioms ProofFile.Honest.K12.Sim2.planB_KW
#print axioms ProofFile.Honest.K12.Sim2.opens_KWFull
#print axioms ProofFile.Honest.K12.Sim2.second_flat_key
#print axioms ProofFile.Honest.K12.Sim2.find_own_key
#print axioms ProofFile.Honest.K12.Sim2.slot_own_key
#print axioms ProofFile.Honest.K12.Sim2.own_key_good
#print axioms ProofFile.Honest.K12.Sim2.spent_own_full
#print axioms ProofFile.Honest.K12.Sim2.own_sourced
#print axioms ProofFile.Honest.K12.Sim2.own_key_row
#print axioms ProofFile.Honest.K12.Sim2.own_key_row_at_half
