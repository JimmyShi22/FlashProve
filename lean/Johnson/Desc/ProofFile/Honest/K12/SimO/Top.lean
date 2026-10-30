-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the slot at the parts that the base filling lays.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Top.lean: UNDER THE HEAD, AT ⟨2, none, 10, K12⟩, AT THE PARTS THAT THE BASE FILLING LAYS THERE (NOT READ THROUGH: THE CROSSING TO `onlineFilling` IS NOT HERE): `halfO` (K12/AtProof/HalfO.lean) is `proverSideOfProximityTest` of `jobAtOmega` behind the guard `needsField` (`halfO_at_head`): this file
seats that row beside the two simulators `firstSim` and `restSim`, and gives the frame's fields `fits`, `exact`, `fresh` at its side.

  `omegaRow`         the two guarded parts, each with its simulator
  `omegaRow_half`    the row's parts are `proverSideOfProximityTest J` behind the guard: the half that `halfO_at_head` names
  `fits_guardRow`    the guard changes nothing of `Side.fits`
  `OnOmega`          the condition: the stand's field holds columns; and `OnEntryOwn` (SimO/Entry.lean) at the second member
  `omega_fields`     **`fits`, `exact` at both members, `fresh` at both members at a book that spends nothing of them**
  `omega_good`       `Good` as one term, at A := False

Limits. CONDITIONAL ON `OnOmega`: nothing here pays its clauses at a run. `noneSpent` at the two addresses is a premise. `exact` at the first member asks the field alone. The door `J.rec₀` and the simulators' letter `Js.rec₀` are free here, tied by the clause `door` of `OnFreeOwn` alone.
No law stated here reads the book's carrying entries. No property of the protocol is claimed: nothing on completeness, soundness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.AtHead
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard
import Johnson.Desc.ProofFile.Honest.Small.Book
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open H2K.Member (piOFull codesFull)
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent spentBy_of_noneSpent)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- The two guarded parts, each with its simulator. -/
def omegaRow (J : TestJob W X) (Js : SimJob Pb) : List (Part V W X × Sim Pb) := guardRow (testPairs J Js)

/-- **The row's parts are `halfO`'s half, the base filling's.** -/
theorem omegaRow_half (J : TestJob W X) (Js : SimJob Pb) :
    (⟨J.p.place, (omegaRow J Js).map (·.1)⟩ : Placed V W X) = (proverSideOfProximityTest J : Placed V W X).needsField := rfl

theorem foldl_guardRow (row : List (Part V W X × Sim Pb)) : ∀ n : ℕ,
    ((guardRow row).map (·.1)).foldl (fun n p => n + p.moves.length) n =
      (row.map (·.1)).foldl (fun n p => n + p.moves.length) n := by
  induction row with
  | nil => intro n; rfl
  | cons x l ih =>
    intro n
    show ((guardRow l).map (·.1)).foldl (fun n p => n + p.moves.length)
        (n + (x.1.needsField).moves.length) = (l.map (·.1)).foldl (fun n p => n + p.moves.length) (n + x.1.moves.length)
    rw [needsField_length, ih]

/-- The guard changes nothing of `Side.fits`. -/
theorem fits_guardRow (b : Block S Cl) (row : List (Part V W X × Sim Pb))
    (f : S → List Fmt.Drawn → Option String) :
    (⟨b, guardRow row, f⟩ : Side S Cl V W X Pb).fits = (⟨b, row, f⟩ : Side S Cl V W X Pb).fits := by
  have e1 : (guardRow row).zipIdx.all (fun s => s.1.2.addr == (⟨b.place, s.2⟩ : Addr)) =
      row.zipIdx.all (fun s => s.1.2.addr == (⟨b.place, s.2⟩ : Addr)) := by
    unfold guardRow
    rw [List.zipIdx_map, List.all_map]
    rfl
  have e2 : (⟨b.place, (guardRow row).map (·.1)⟩ : Placed V W X).rounds =
      (⟨b.place, row.map (·.1)⟩ : Placed V W X).rounds := foldl_guardRow row 0
  unfold Side.fits Side.half
  simp only [e1, e2]

/-- **The condition.** -/
def OnOmega (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : ProofFile.Honest.Mid W X) (front : Before) : Prop :=
  (∃ cs, m.opened = some cs) ∧ OnEntryOwn φ J Js codesFull chain os u ca m front

/-- **`fits`, `exact` and `fresh` at the side of the base filling's parts.** -/
theorem omega_fields (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb) (hJ : Js.p = pO)
    (ho : Js.own = true) (fs : List (ProofFile.Honest.Fall St)) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place
      (omegaRow (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) fs = some σ)
    (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtOmega.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (OnOmega φ (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js chain firstListAtOmega)
        (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hbare : testSide (V := V) (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js fs =
      some (⟨b, testPairs (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js,
        ProofFile.Honest.fallOf fs pO.place⟩ : Side St ProofFile.Cl V W X Pb) := by
    unfold testSide Side.seated
    show Option.map _ ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place == pO.place) = _
    rw [hb]
    rfl
  obtain ⟨hfit, hmem, -⟩ := seated_head_O h hO door weights rand omega? Js fs hJ ho _ hbare
  refine ⟨?_, ?_, ?_⟩
  · show (⟨b, guardRow _, _⟩ : Side St ProofFile.Cl V W X Pb).fits = true
    rw [fits_guardRow]
    exact hfit
  · have hm : (⟨b, omegaRow (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js,
        ProofFile.Honest.fallOf fs pO.place⟩ : Side St ProofFile.Cl V W X Pb).members =
        [(firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded,
          (restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded] := by
      show membersOf (guardRow _) 0 _ = _
      rw [membersOf_guardRow]
      have := congrArg (List.map Member.guarded) hmem
      exact this
    intro u hu
    have hu' : u ∈ [(firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded,
        (restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js).guarded] := by
      rw [← hm]
      exact hu
    rcases List.mem_cons.1 hu' with rfl | hu
    · refine exact_guarded (On := fun _ _ _ _ => True) (fun ca m front hOn => ⟨trivial, hOn.1⟩) ?_
      exact exact_first_own_head h hO φ _ door weights rand omega? Js hJ ho chain firstTree _
    · rcases List.mem_singleton.1 hu with rfl
      refine exact_guarded (On := OnEntryOwn φ _ Js codesFull chain firstListAtOmega) (fun ca m front hOn => ⟨hOn.2, hOn.1⟩) ?_
      refine exact_bud (bud := budOpened pO.nums.stages) (fun ds asks hb => ?_)
        (exact_entry_head_omega h hO φ _ door weights rand omega? Js hJ ho chain firstTree hop)
      have h2 := hb.2
      rw [hJ] at h2
      exact h2
  · intro u hu p sp ca m ds asks _ _ _
    exact fresh_of_nil _ (spentBy_of_noneSpent (hB u hu) p) _ _

/-- **`Good` at the side of the base filling's parts, at A := False.** `plays` and `acc` are met for nothing there. -/
theorem omega_good (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb) (hJ : Js.p = pO)
    (ho : Js.own = true) (fs : List (ProofFile.Honest.Fall St)) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : Side.seated (P5J.F0T o Zp Np cF).shared.blocksInOrder pO.place
      (omegaRow (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (φ : Face V W Pb) (chain firstTree : ℕ)
    (hop : Js.opens = firstListAtOmega.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (Bk : ProverCoinCounts) (ord : List Place) (B : Coins Bk → St → ProofFile.Honest.Mid W X → Env → Prop)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B
      (OnOmega φ (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js chain firstListAtOmega)
      (budBoth Js) := by
  obtain ⟨hf, he, hfr⟩ := omega_fields h hO door weights rand omega? Js hJ ho fs σ hσ φ chain firstTree hop Bk ord hB
  exact { fits := hf
          plays := fun _ _ _ _ _ hA => hA.elim
          acc := fun _ _ _ _ _ hA => hA.elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (he u hu)
          fresh := hfr }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.omega_good
#print axioms ProofFile.Honest.K12.Light.omegaRow
#print axioms ProofFile.Honest.K12.Light.omegaRow_half
#print axioms ProofFile.Honest.K12.Light.fits_guardRow
#print axioms ProofFile.Honest.K12.Light.OnOmega
#print axioms ProofFile.Honest.K12.Light.omega_fields
