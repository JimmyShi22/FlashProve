-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the door of the real job against the simulators' state.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/DoorOmega.lean: the simulators' letter at the test on G_omega, and the clause `door` of `OnFreeOwn` at a called second member, at a run of the frame's walking prover: the real job's door (`doorOmegaF` at `colsOpened`, read at `restFront`) is `stateAtOmega` at the run's own front cut back by the
first part's rounds.

  `stateAtOmega`        the letter: the fold over the blocks in front of the test, from `first Q.codes` at the key, at what the Before lists of the shared chain; the way in; `fallOmega` where that refuses
  `door_at_omega`       **the equation**

Premises. `hpre`: the blocks in front are like the front block, bs and the test on G_u; `hstart`: the description's start is `first Q.codes` at the key: the two of the five named in DoorOpened.lean's limits that this file does not pay. `hi`: i is the first part's number of rounds.

Limits. The fall-back is taken at a front where the fold refuses: no state of the verifier. That the run reaches the part is a premise (`hc`). The door reads ALL columns opened in front: "LOC"'s, and those that the test on G_u has read: at a run they are in the Before; that a simulator of the whole view has made them is the parts' in front. Of the walk (runC). No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Door
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first frontBlock)
open Desc.K14.Honest (Like)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC midSharedAtW Before)
open ProofFile.Honest.K12.Sim2 (stateFromViewOnSharedChain stateFromViewOnSharedChain_at_stand)

/-- **The simulators' letter at the test on G_omega.** -/
def stateAtOmega {Cl : Type} (Q : P14) (sentU : Array OracleNotice) (p : P12) (pre : List (Block St Cl)) :
    TableKey → Before → T12 :=
  stateFromViewOnSharedChain pre (first Q.codes)
    (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) (fallOmega Q sentU p)

/-- Like blocks have the same rounds. -/
theorem rounds_like {Cl : Type} : ∀ {xs : List (Block St Cl)} {bs : List (Block St Unit)},
    List.Forall₂ Like xs bs → bs.flatMap (·.rounds) = xs.flatMap (·.rounds)
  | _, _, .nil => rfl
  | x :: _, b :: _, .cons hl ht => by
    simp only [List.flatMap_cons]
    rw [hl.rounds, rounds_like ht]

/-- **The clause door at a called second member.** -/
theorem door_at_omega {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {W₀ Rc Tr X₀ Y V Pq : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hpl : (P5J.F0T o Zp Np cF).planOk = true) (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V (Common W₀ Rc TableKey) X₀ Pq)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pq)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (bs : List (Block St Unit)) (p : P12)
    (hpre : List.Forall₂ Like pre (frontBlock c ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])))
    (hstart : (P5J.F0T o Zp Np cF).start₂ ((P5J.F0T o Zp Np cF).pub x) = first Q.codes (P.key x))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hi : i = firstLen J.p.nums.stages) :
    ∃ m, ProofFile.Honest.midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      doorOmegaF Q sentU bs p (fun w : Common W₀ Rc TableKey => w.key) colsOpened m.st.input (restFront J m) =
        stateAtOmega Q sentU p (frontBlock c :: (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])) (P.key x)
          ((r.run.beforeAt (ProofFile.Honest.storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, u.number⟩).cut i) := by
  obtain ⟨m, s, cols, hm, hin, ho, hseen, hfold, hrd, hcl, -⟩ := stateFromViewOnSharedChain_at_stand hpl hR hrun σ u pre t i S hc
    (first Q.codes) (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) (fallOmega Q sentU p) (P.key x)
    hstart.symm
  refine ⟨m, hm, ?_⟩
  have hlen : m.seen.length = (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
    have Q' := ((P5J.F0T o Zp Np cF).planOk_ok).1 hpl
    obtain ⟨-, -, -, -, -, s1, s2, s3⟩ := ProofFile.Honest.ready_ok hR
    obtain ⟨-, l2, -⟩ := ProofFile.Honest.runC_laidAs hrun hR (ProofFile.Honest.steps_shaped s1 Q'.blocks₁)
      (ProofFile.Honest.steps_shaped s2 Q'.blocks₂) (ProofFile.Honest.steps_shaped s3 Q'.blocks₃)
    have d₂ := ProofFile.Honest.laidAs_drawn l2
    have hall : r.run.played.2.1.length = R.shared.length := by
      have h1 := congrArg List.length d₂
      rw [List.length_map] at h1
      exact h1.trans l2.1
    have hfits := S.fits
    rw [hseen, ProofFile.Honest.roundsOf_length, List.length_take, hall, ← hi]
    omega
  obtain ⟨e1, e2⟩ := rest_front_at J m (pre.flatMap (·.rounds)).length hlen
  have hN : m.seen.take (pre.flatMap (·.rounds)).length =
      ProofFile.Honest.roundsOf (r.run.played.2.1.take (pre.flatMap (·.rounds)).length) := by
    rw [hseen]
    unfold ProofFile.Honest.roundsOf
    rw [← List.map_take, List.take_take]
    simp
  rw [hstart] at hfold
  have hd := door_of_opened c Q sentU bs p pre hpre (P.key x) _ cols s hfold
    (fun w : Common W₀ Rc TableKey => w.key) m.st.input (restFront J m) (by rw [hin]) (e1.trans hN)
    (e2.trans ho)
  have hL : (frontBlock c :: (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])).flatMap (·.rounds) =
      pre.flatMap (·.rounds) := rounds_like hpre
  have hf' := Desc.K14.Honest.fold_like 0 _ _ hpre _ _ _ _ hfold
  show _ = stateFromViewOnSharedChain _ (first Q.codes) _ _ _ _
  unfold stateFromViewOnSharedChain ProofFile.Honest.K12.Sim2.doorFromViewOnSharedChain
  rw [hL, hcl, hrd]
  dsimp only
  rw [hf']
  show _ = ((VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) s).toOption.getD _ 
  rw [hd]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.stateAtOmega
#print axioms ProofFile.Honest.K12.Light.door_at_omega
