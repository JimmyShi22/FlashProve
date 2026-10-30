-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the slot at the request's own test, at the parts that the prover's term lays.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SlotOwnTest.lean: at the request's own proximity test on the
last chain, under the head, at the side that seats the job's two parts behind the guard (halfW lays
(proverSideOfProximityTest J).needsField): fits, exact and fresh, and Good as one term at A := False. No property of
the protocol is claimed.

  OnOwnTestEntry   the condition: the stand's field holds columns, and OnEntry
  slot_own_test    fits; exact at both guarded members; fresh at both where the book spends nothing
  own_test_good    Good at A := False: plays and acc are met for nothing there

Premises. To: the openings' public ties. hB: a test on the book: no real book exists yet.

Limits. Conditional on OnEntry: whether a run meets it here is not shown by this file. exact stands at
every value of the field that holds columns; the field's form ExactMemberAt follows at every pre. No
property of a prover: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Entry
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FreshAny
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OwnTestEntry
import AtFullSide.K12.RestTiesAtHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)
open H2K.Member (codesFull)

variable {V W X Pb : Type}

/-- **The condition at a guarded member.** -/
def OnOwnTestEntry (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : ProofFile.Honest.Mid W X) (front : Before) : Prop :=
  (∃ cs, m.opened = some cs) ∧ OnEntry φ J Js K chain os u ca m front

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T o Zp Np cF

/-- **fits, exact and fresh at the side of the parts that the term lays.** -/
theorem slot_own_test (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false) (hs : Js.p = (fourOf Np).W)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3) (To : OpenTies J Js chain os)
    (fs : List (Fall (𝔽).S₃)) (σ : Side (𝔽).S₃ (𝔽).Cl V W X Pb)
    (hσ : Side.seated (𝔽).second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (Bk : ProverCoinCounts) (ord : List Place)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    σ.fits = true ∧
      (∀ u ∈ σ.members, ExactMember φ σ chain firstTree
        (OnOwnTestEntry φ J Js codesFull chain os) (budBoth Js) u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord (budBoth Js) u := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hbare : testSide (V := V) (𝔽).second.blocksInOrder J Js fs =
      some (⟨b, testPairs J Js, fallOf fs J.p.place⟩ : Side (𝔽).S₃ (𝔽).Cl V W X Pb) := by
    unfold testSide Side.seated
    show Option.map _ ((𝔽).second.blocksInOrder.find? fun b => b.place == J.p.place) = _
    rw [hb]
    rfl
  obtain ⟨T₀, -, hall⟩ := first_any_head_W (V := V) h J Js hJ hfr hs ho
  obtain ⟨hfit, hmem, -⟩ := hall fs _ hbare
  have T : PubTiesT J Js codesFull os.length := by
    rw [hos]
    exact pubTiesT_head_W h J Js hJ hfr hs ho (planB_head_W h)
  have hm : (⟨b, guardRow (testPairs J Js), fallOf fs J.p.place⟩ :
      Side (𝔽).S₃ (𝔽).Cl V W X Pb).members =
      [(firstMember J Js).guarded, (restMember J Js).guarded] := by
    show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hmem
  have E := exact_both_entry φ (⟨b, guardRow (testPairs J Js), fallOf fs J.p.place⟩ :
    Side (𝔽).S₃ (𝔽).Cl V W X Pb) J Js codesFull chain firstTree os hfr T₀ T To
  refine ⟨?_, fun u hu => ?_, fun u hu => fresh_member φ _ Bk ord _ u (hB u hu)⟩
  · show (⟨b, guardRow _, _⟩ : Side (𝔽).S₃ (𝔽).Cl V W X Pb).fits = true
    rw [fits_guarded_row]
    exact hfit
  · have hu' : u ∈ [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      rw [← hm]
      exact hu
    rcases List.mem_cons.1 hu' with rfl | hu₂
    · exact exact_guarded (On := OnEntry φ J Js codesFull chain os)
        (fun ca m front hOn => ⟨hOn.2, hOn.1⟩) (E _ List.mem_cons_self)
    · rcases List.mem_singleton.1 hu₂ with rfl
      exact exact_guarded (On := OnEntry φ J Js codesFull chain os)
        (fun ca m front hOn => ⟨hOn.2, hOn.1⟩)
        (E _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **Good at that side, at A := False.** plays and acc are met for nothing there. -/
theorem own_test_good (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (J : TestJob W X) (Js : SimJob Pb)
    (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false) (hs : Js.p = (fourOf Np).W)
    (ho : Js.own = false) (φ : Face V W Pb) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3) (To : OpenTies J Js chain os)
    (fs : List (Fall (𝔽).S₃)) (σ : Side (𝔽).S₃ (𝔽).Cl V W X Pb)
    (hσ : Side.seated (𝔽).second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (Bk : ProverCoinCounts) (ord : List Place)
    (B : Coins Bk → (𝔽).S₃ → ProofFile.Honest.Mid W X → Env → Prop)
    (hB : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B
      (OnOwnTestEntry φ J Js codesFull chain os) (budBoth Js) := by
  obtain ⟨hf, he, hfr'⟩ := slot_own_test h J Js hJ hfr hs ho φ chain firstTree os hos To fs σ hσ Bk
    ord hB
  exact { fits := hf
          plays := fun _ _ _ _ _ hA => hA.elim
          acc := fun _ _ _ _ _ hA => hA.elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (he u hu)
          fresh := hfr' }

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.OnOwnTestEntry
#print axioms ProofFile.Honest.K12.Sim2.slot_own_test
#print axioms ProofFile.Honest.K12.Sim2.own_test_good
