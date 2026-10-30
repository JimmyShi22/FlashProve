-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the simulators' door at the request's own test, at the seated description.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorWAt.lean: `stateAtOwnTest`, the simulators' state on entry of the request's own proximity test (the
place `placeW`, on the last chain), at the seated description's own term; and the equation of DoorW.lean at that place, where the
blocks in front are cut off the description by the place alone.

  `stateFromViewOnLastChain_at_place`   at a description that passes the tests on the plan, at a called part of a side at place a: `stateFromViewOnLastChain` over the blocks
      in front of a (off the public description) is what the way in makes of the run's own fold
  `stateAtOwnTest`              the letter: of the public letters o, Zp, Np, cF, the public input and the Before, at every Before
  `stateAtOwnTest_at_stand`     the equation at `placeW`

The fall-back is `idleT12`, where the fold refuses: no state of the verifier. Of the walk (runC). No job is typed at this test and no law
on a part is stated. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks Place)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof

/-- **At the place**: the blocks in front are read off the public description. -/
theorem stateFromViewOnLastChain_at_place {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (enter : F.S₃ → Except String T12) (fall : T12)
    (a : Place) (ha : σ.block.place = a) :
    ∃ (e₁ : F.S₁) (e₂ : F.S₂) (v₀ s : F.S₃) (cols : List OpenedColumn),
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧ F.start₃ (F.pub x) e₁ e₂ = .ok v₀ ∧
      foldBlocks F.lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      stateFromViewOnLastChain F (F.second.blocksInOrder.takeWhile (·.place != a)) enter fall x
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut i) = (enter s).toOption.getD fall := by
  have hn := (places_nodup ((F.planOk_ok).1 hpl).places).2.2
  have hcut : F.second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : F.second.blocksInOrder.takeWhile (·.place != a) = pre := by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  rw [hpre]
  exact stateFromViewOnLastChain_at_stand hpl hR hrun σ u pre t i S hc enter fall

/-- **The simulators' state on entry at the request's own test.** -/
def stateAtOwnTest (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) :
    ProofFile.Inst → Before → T12 :=
  stateFromViewOnLastChain (P5J.F0T o Zp Np cF) ((P5J.F0T o Zp Np cF).second.blocksInOrder.takeWhile (·.place != placeW)) enterOwn idleT12

/-- **At a called part at that place**: `stateAtOwnTest` at the run's front, cut back by i, is what `enterOwn` makes of the state of the run's own
fold. -/
theorem stateAtOwnTest_at_stand {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts} {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc}
    {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₃ (P5J.F0T o Zp Np cF).Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).second.blocksInOrder R.second σ u pre t i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = placeW) :
    ∃ (e₁ : (P5J.F0T o Zp Np cF).S₁) (e₂ : (P5J.F0T o Zp Np cF).S₂) (v₀ s : (P5J.F0T o Zp Np cF).S₃)
      (cols : List OpenedColumn),
      r.ends.1 = some e₁ ∧ r.ends.2.1 = some e₂ ∧
      (P5J.F0T o Zp Np cF).start₃ ((P5J.F0T o Zp Np cF).pub x) e₁ e₂ = .ok v₀ ∧
      foldBlocks (P5J.F0T o Zp Np cF).lastChainFirstTreeNumber pre v₀
        (roundsOf (r.run.played.2.2.take (pre.flatMap (·.rounds)).length)) cols = .ok (s, [], []) ∧
      stateAtOwnTest o Zp Np cF x ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, u.number⟩).cut i) = (enterOwn s).toOption.getD idleT12 :=
  stateFromViewOnLastChain_at_place hpl hR hrun σ u pre t i S hc enterOwn idleT12 placeW ha

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.stateFromViewOnLastChain_at_place
#print axioms ProofFile.Honest.K12.Sim2.stateAtOwnTest
#print axioms ProofFile.Honest.K12.Sim2.stateAtOwnTest_at_stand
