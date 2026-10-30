-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the test on the folded row's group.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFolded.lean: the row number 14 of the offline clause: the
proximity test on G_u, at the key file's shared chain, place ⟨2, none, 9, .K12⟩ (K.onU := onUOf …):
fits, exact at both members, fresh; Good at an A that never holds, B free.

  dsKU, facts_KUFull, reachT_KU, restLen_KU, opens_KUFull, first_KU, planB_KU   the written place
  pKU, alike_KU     the key's numbers are alike the written place's, in scope
  find_folded       the search at the place, in the key file's shared chain
  facts_KU, pubTies_folded, openTies_folded   the public premises
  slot_folded, spent_folded_full, folded_good, folded_row   fits, exact, fresh; the book; Good

Limits. Conditional on OnEntry at a run, which this file does not show. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRanges
import E2E.KeyHalves
import Johnson.Loose.H2K12.RoundsAtKeySeats
import Johnson.Desc.K12.Law.Sizes.KeyClosedAtScope
import Johnson.Desc.K12.Law.RoundsAtKeyPlaces
import AtFullSide.K12.RestTiesAtWL
import Johnson.Desc.ProofFile.Honest.K12.AsksAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts P12 T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open H2K.Member (piKUFull codesKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeySourced)

/-- As many challenges as the first part has rounds. -/
def dsKU : List Fmt.Drawn :=
  List.replicate (firstLen piKUFull.nums.stages) ⟨[(1, 0, 0)], [], [], none⟩

theorem facts_KUFull : PlaceFacts piKUFull dsKU :=
  ⟨H2K.Pub.piKUFull_planOk, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem reachT_KU : reachTB piKUFull = true := by decide +kernel

theorem restLen_KU : restLen piKUFull.nums.stages =
    2 + lenFrom (stN piKUFull) (piKUFull.nums.stages.drop 2) := by decide +kernel

theorem opens_KUFull :
    ((((H2K.JointK.laidOf piKUFull).map (·.1)).drop (firstLen piKUFull.nums.stages))[1]?).map
      (·.opens) = some piKUFull.nums.first := by decide +kernel

theorem first_KU : piKUFull.nums.first.length = 2 := by decide +kernel

theorem planB_KU : planB piKUFull codesKeyFull 2 = true := by decide +kernel

section Key
open VerifiableInference.Desc.Key (LaterPlaces Source)
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {V W X Pb : Type}

/-- The test's numbers at the key file's plan. -/
abbrev pKU (Pl : LaterPlaces) : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U

/-- **In scope the place of the test on G_u and the written one are alike.** -/
theorem alike_KU (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) :
    (proximityTestKind guardedProximityTestParts (pKU Pl) : Block T12 Unit).planOk = true ∧ Alike (pKU Pl) piKUFull := by
  obtain ⟨X₀, m, h0, hm, hX, -, hP⟩ := hS.source
  obtain ⟨X₁, m₁, h0', hm', -, hl⟩ := hS.named.named
  obtain rfl : X₀ = X₁ := Except.ok.inj (h0.symm.trans h0')
  obtain rfl : m = m₁ := Except.ok.inj (hm.symm.trans hm')
  have hR := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope scope hR hm
  have hset : m.p.chains.made.sized.set = H2K.Member.setAt :=
    (Johnson.RunOne.Law.K12Facts15.set_in_scope scope hR hm).trans (by decide +kernel)
  have hpinAt : VerifiableInference.PlanWritten.pinnedKeyAt m (keyFileDescription Xs N Pl) = true :=
    hl ("its rounds are not the written ones", _)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpin : VerifiableInference.PlanWritten.seatPinnedKey Z.pol (keyFileDescription Xs N Pl) = true :=
    (VerifiableInference.Desc.Key.pinned_is_seat _
      (VerifiableInference.PlanWritten.publicOfO_scan h0) hm).symm.trans hpinAt
  have hW := (VerifiableInference.PlanWritten.seat_in_scope_key _ _ Z scope hpin).1
  have pk := H2K.JointK.keyPlan_U Xs N Pl hS.named.plan
  have nU := H2K.Sizes.nums_KU hk hset hP (H2K.JointK.rounds_at_key_U hk hset hP Xs N hS.named.plan hW)
  have n1 : (pKU Pl).nums = piKUFull.nums := (H2K.Made.nums_of_planOk _ Pl.U pk).trans nU
  obtain ⟨-, -, -, -, e5, -, -⟩ := (H2K.Sizes.later_of_full hk hset hP).1
  obtain ⟨-, -, -, -, g5, -, -⟩ := H2K.Pub.held_KU
  refine ⟨pk, n1, (H2K.Sizes.idx_of_planOk _ Pl.U pk).trans (e5.trans g5.symm),
    (H2K.JointK.early_of_planOk _ pk).trans (by decide +kernel),
    (H2K.JointK.answers_of_planOk _ pk).trans (by decide +kernel), ?_⟩
  rw [decls_thin, decls_thin, thin_of_planOk guardedProximityTestParts n1 pk H2K.Pub.piKUFull_planOk]

/-- The search finds what stands in a list whose keys are all different. -/
theorem find_after_nodup {α β : Type} [BEq β] [LawfulBEq β] (pl : α → β) (pre : List α) (e : α)
    (rest : List α) (hnd : ((pre ++ e :: rest).map pl).Nodup) (p : β) (hp : pl e = p) :
    (pre ++ e :: rest).find? (fun b => pl b == p) = some e := by
  rw [List.map_append, List.map_cons] at hnd
  have hdis := List.disjoint_of_nodup_append hnd
  have h0 : pre.find? (fun b => pl b == p) = none := by
    refine List.find?_eq_none.2 fun b hb e' => ?_
    have e'' := beq_iff_eq.1 e'
    exact hdis (List.mem_map_of_mem (f := pl) hb) (by
      rw [e'', ← hp]
      exact List.mem_cons_self)
  rw [List.find?_append, h0, List.find?_cons_of_pos (by rw [hp]; exact beq_self_eq_true _)]
  rfl

/-- **The search at the test's place, in the key file's shared chain.** -/
theorem find_folded (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) (J : TestJob W X)
    (hJ : J.p = pKU Pl) :
    ∃ b, ((keyFileDescription Xs N Pl).shared.blocksInOrder.find? fun b => b.place == J.p.place) = some b ∧
      b.place = J.p.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles := by
  have r := (AtPublicFiles.KeyBook.places_named scope h).2.1
  have hcut := H2K.JointK.keyShared_cut Xs.chains Pl
  have hnd : (((keyFileDescription Xs N Pl).shared.blocksInOrder).map (·.place)).Nodup := by
    have e : ((keyFileDescription Xs N Pl).shared.blocksInOrder).map (·.place) = AtPublicFiles.KeyBook.fullShared.map (·.1) := by
      rw [← r]
      show _ = (((keyFileDescription Xs N Pl).shared.blocksInOrder).map fun b => (b.place, b.rounds.length)).map (·.1)
      rw [List.map_map]
      rfl
    rw [e]
    decide +kernel
  have hpl : (H2K.JointK.keyGu Pl).place = J.p.place := by
    rw [hJ]
    exact H2K.JointK.k12_place guardedProximityTestParts (pKU Pl)
  refine ⟨H2K.JointK.keyGu Pl, ?_, hpl, ?_, ?_⟩
  · have key := find_after_nodup (fun b : Block Desc.K14.St VerifiableInference.Desc.Key.Claim => b.place)
      (H2K.JointK.keySharedPre Xs.chains Pl) (H2K.JointK.keyGu Pl)
      ((Pl.O.toList.map H2K.JointK.keyOmega) ++ [H2K.JointK.keySharedEnd Xs.chains Pl])
      (by rw [← hcut]; exact hnd) J.p.place hpl
    show List.find? _ ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
    rw [hcut]
    exact key
  · rw [hJ]
    exact (H2K.JointK.keyGu_sits Pl).rounds
  · rw [hJ]
    rfl

/-- The written facts at the key's own numbers. -/
theorem facts_KU (P : PlaceFacts piKUFull dsKU) (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (A : Alike p piKUFull) : PlaceFacts p dsKU :=
  facts_carry (congrArg (·.stages) A.nums) (thin_of_planOk guardedProximityTestParts A.nums hp H2K.Pub.piKUFull_planOk)
    hp P

/-- **The public premises at the key's numbers.** -/
theorem pubTies_folded (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (A : Alike p piKUFull) (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = p)
    (hfr : J.fresh.isNone = false) (hs : Js.p = p) (ho : Js.own = false) :
    PubTiesT J Js codesKeyFull 2 := by
  have F := facts_KU facts_KUFull p hp A
  have h1 : p.nums.stages = piKUFull.nums.stages := congrArg (·.stages) A.nums
  have h2 : p.nums.ownMask = piKUFull.nums.ownMask := congrArg (·.ownMask) A.nums
  refine ⟨hs.trans hJ.symm, ho.trans hfr.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, reachTB_reads h1 h2 A.decls]
    exact reachT_KU
  · rw [hJ, planB_alike A]
    exact planB_KU
  · rw [hJ]
    exact F.form
  · rw [hJ]
    exact F.count
  · rw [hJ]
    show restLen p.nums.stages = 2 + lenFrom (p.nums.stages.getD 1 default) (p.nums.stages.drop 2)
    rw [h1]
    exact restLen_KU
  · rw [tablesFitB_eq, hfr, hJ]
    exact F.tab

theorem openTies_folded (p : P12) (A : Alike p piKUFull) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = p) (chain : ℕ)
    (hop : Js.opens = p.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a)) :
    OpenTies J Js chain p.nums.first := by
  refine ⟨?_, hop⟩
  have e : ((((H2K.JointK.laidOf J.p).map (·.1)).drop (firstLen J.p.nums.stages))[1]?).map (·.opens) =
      some p.nums.first := by
    rw [hJ, A.decls, A.nums]
    exact opens_KUFull
  rw [← List.map_drop, List.getElem?_map, Option.map_map] at e
  obtain ⟨d, hd, hdo⟩ := Option.map_eq_some_iff.1 e
  exact ⟨d, hd, hdo⟩

/-- **fits, exact and fresh at the side of the test on G_u.** -/
theorem slot_folded (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = pKU Pl) (hfr : J.fresh.isNone = false)
    (hs : Js.p = pKU Pl) (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = (pKU Pl).nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₂))
    (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : testSide (keyFileDescription Xs N Pl).shared.blocksInOrder J Js fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (OnEntry φ J Js codesKeyFull chain (pKU Pl).nums.first) (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨pk, A⟩ := alike_KU scope hS
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_folded scope hS.named J hJ
  have F : PlaceFacts J.p dsKU := by
    rw [hJ]
    exact facts_KU facts_KUFull _ pk A
  obtain ⟨T₀, -, hall⟩ := any_at_place (V := V) J Js F _ b hf hpl hr hor hfr (hs.trans hJ.symm) ho
  obtain ⟨hfit, hmem, -⟩ := hall fs σ hσ
  have T : PubTiesT J Js codesKeyFull (pKU Pl).nums.first.length := by
    rw [A.nums, first_KU]
    exact pubTies_folded _ pk A J Js hJ hfr hs ho
  have To := openTies_folded _ A J Js hJ chain hop
  refine ⟨hfit, fun u hu => ?_, fun u hu => fresh_member φ σ Bk ord _ u (hB u hu)⟩
  rw [hmem] at hu
  exact exact_both_entry φ σ J Js codesKeyFull chain firstTree _ hfr T₀ T To u hu

open AtPublicFiles.KeyBook (keyBook fullPub KeyPub foldedTestPlace)

theorem spent_folded_full : (fullPub.map fun K => noneSpent (keyBook K) ⟨foldedTestPlace, 0⟩ &&
    noneSpent (keyBook K) ⟨foldedTestPlace, 1⟩) = some true := by decide +kernel

/-- **Row 14**: Good at every job at the place whose fresh table has come earlier, at every
simulators' job at it, at the key's book. -/
theorem folded_good (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K : KeyPub}
    (hK : fullPub = some K) (J : TestJob W X) (Js : SimJob Pb) (hJ : J.p = pKU Pl)
    (hfr : J.fresh.isNone = false) (hs : Js.p = pKU Pl) (ho : Js.own = false) (φ : Face V W Pb)
    (chain firstTree : ℕ)
    (hop : Js.opens = (pKU Pl).nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (keyFileDescription Xs N Pl).S₂))
    (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : testSide (keyFileDescription Xs N Pl).shared.blocksInOrder J Js fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₂ → ProofFile.Honest.Mid W X → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord chain firstTree A B
      (OnEntry φ J Js codesKeyFull chain (pKU Pl).nums.first) (budBoth Js) := by
  have hsp := spent_folded_full
  rw [hK] at hsp
  have hsp' : (noneSpent (keyBook K) ⟨foldedTestPlace, 0⟩ &&
      noneSpent (keyBook K) ⟨foldedTestPlace, 1⟩) = true := Option.some.inj hsp
  simp only [Bool.and_eq_true] at hsp'
  obtain ⟨pk, Al⟩ := alike_KU scope hS
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_folded scope hS.named J hJ
  have F : PlaceFacts J.p dsKU := by
    rw [hJ]
    exact facts_KU facts_KUFull _ pk Al
  obtain ⟨-, -, hall⟩ := any_at_place (V := V) J Js F _ b hf hpl hr hor hfr (hs.trans hJ.symm) ho
  obtain ⟨-, hmem, -⟩ := hall fs σ hσ
  have hbp : σ.block.place = foldedTestPlace := by
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hσ
    have hb2 : b' = b := Option.some.inj (hb'.symm.trans hf)
    show b'.place = _
    rw [hb2, hpl, hJ]
    exact H2K.JointK.place_of_p12At _ _
  obtain ⟨h1, h2, h3⟩ := slot_folded scope hS J Js hJ hfr hs ho φ chain firstTree hop fs σ hσ
    (keyBook K) ord (fun u hu => by
      rw [hmem] at hu
      rw [hbp]
      rcases List.mem_cons.1 hu with rfl | hu'
      · exact hsp'.1
      · rcases List.mem_singleton.1 hu' with rfl
        exact hsp'.2)
  exact { fits := h1
          plays := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          acc := fun _ _ _ _ _ hA' => (hA _ _ _ _ hA').elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (h2 u hu)
          fresh := h3 }

open ProofFile.Honest.K12.Light (simLocU sentOf)

/-- **Row 14 at the pair that keyProver lays**: the job of proverSideOfTestOnU, the simulators' job simLocU. -/
theorem folded_row {W₀ Rc X' : Type} (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    {K : KeyPub} (hK : fullPub = some K) (Ap : ProofFile.Honest.K14.SendPub)
    (bs : List (Block Desc.K14.St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (wt : Common W₀ Rc OnBytes.TableKey → Weights) (rd : Common W₀ Rc OnBytes.TableKey → TableRand)
    (φ : Face Empty (Common W₀ Rc OnBytes.TableKey) OnBytes.TableKey) (firstTree : ℕ)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₂))
    (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X'
      OnBytes.TableKey)
    (hσ : testSide (keyFileDescription Xs N Pl).shared.blocksInOrder
      (AtPublicFiles.KeyLay.jobKU (X := X') Ap (pKU Pl) bs st wt rd).toRun.toTest
      (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₂ →
      ProofFile.Honest.Mid (Common W₀ Rc OnBytes.TableKey) X' → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 1 firstTree A B
      (OnEntry φ (AtPublicFiles.KeyLay.jobKU (X := X') Ap (pKU Pl) bs st wt rd).toRun.toTest
        (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first)
      (budBoth (simLocU Ap.P (sentOf Ap.P.S) bs (pKU Pl) 1)) :=
  folded_good scope hS hK _ _ rfl rfl rfl rfl φ 1 firstTree rfl fs σ hσ pre ord A B hA

end Key

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.facts_KUFull
#print axioms ProofFile.Honest.K12.Sim2.reachT_KU
#print axioms ProofFile.Honest.K12.Sim2.opens_KUFull
#print axioms ProofFile.Honest.K12.Sim2.planB_KU
#print axioms ProofFile.Honest.K12.Sim2.alike_KU
#print axioms ProofFile.Honest.K12.Sim2.find_folded
#print axioms ProofFile.Honest.K12.Sim2.slot_folded
#print axioms ProofFile.Honest.K12.Sim2.spent_folded_full
#print axioms ProofFile.Honest.K12.Sim2.folded_good
#print axioms ProofFile.Honest.K12.Sim2.folded_row
