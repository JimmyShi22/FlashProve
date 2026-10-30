-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the door's equation under the head.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/DoorHead.lean: `door_at_omega` (SimO/DoorOmega.lean) under the library's head: its premises `hpre` and `hstart` are paid: the ten blocks in front of the test are the front block, the eight and the test on G_u, and the description's start is `first` at the key.

  `flat_ten`          the shared chain's first ten blocks, and that the test on G_omega stands next, from the library's `flat_retype_all`
  `place_at`, `pre_at_omega`   what stands in front of a block at that place is those ten
  `door_head_omega`   **the equation**

Left as premises: `hα` (the prover's key is the instance's), the run's. Of the walk (`runC`). No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.DoorOmega
import Johnson.Desc.ProofFile.Honest.K12.DoorAtRun
import Johnson.Desc.K14.Law.SharedFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St first frontBlock blocks chainOf)
open Desc.K14.Honest (Like)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC midSharedAtW Before)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The blocks in front of the test on G_omega.** -/
theorem flat_ten {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14) (N : H2U.Places4)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ (pre : List (Block St Cl)) (tl : List (Block St Cl)),
      ((chainOf c Q (VerifiableInference.Desc.K12.Seat.tests N) VerifiableInference.Desc.K12.Seat.last).retype
        (Cl' := Cl)).blocksInOrder = pre ++ tl ∧ pre.length = 10 ∧
      List.Forall₂ Like pre (frontBlock c :: ([b1, b2, b3, b4, b5, b6, b7, b8] ++
        [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U))])) ∧
      ∀ nO, N.O = some nO → ∃ (x : Block St Cl) (tl' : List (Block St Cl)), tl = x :: tl' ∧
        x.place = ⟨2, none, 10, .K12⟩ := by
  rw [Desc.K14.Law.flat_retype_all c Q b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb]
  refine ⟨Desc.K14.Law.frontOf c :: ([b1, b2, b3, b4, b5, b6, b7, b8].map Block.retype ++
      [Desc.K14.Law.bareOf (Block.retype (VerifiableInference.Desc.K12.Seat.onGu
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U))))]),
    (((N.O.toList.map fun nO => VerifiableInference.Desc.K12.Seat.onGomega
        (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))) ++
      [VerifiableInference.Desc.K12.Seat.last ([b1, b2, b3, b4, b5, b6, b7, b8] ++
        VerifiableInference.Desc.K12.Seat.tests N)]).map Block.retype).map Desc.K14.Law.bareOf, ?_, rfl, ?_, ?_⟩
  · simp [VerifiableInference.Desc.K12.Seat.tests]
  · exact .cons (Desc.K14.Honest.like_frontOf c) (.cons (Desc.K14.Honest.like_retype b1)
      (.cons (Desc.K14.Honest.like_retype b2) (.cons (Desc.K14.Honest.like_retype b3)
      (.cons (Desc.K14.Honest.like_retype b4) (.cons (Desc.K14.Honest.like_retype b5)
      (.cons (Desc.K14.Honest.like_retype b6) (.cons (Desc.K14.Honest.like_retype b7)
      (.cons (Desc.K14.Honest.like_retype b8) (.cons ⟨rfl, rfl, rfl, rfl⟩ .nil)))))))))
  · intro nO hn
    rw [hn]
    refine ⟨_, _, rfl, ?_⟩
    show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block _ Unit).place = _
    exact (H2K.JointK.k12_place guardedProximityTestParts _).trans (H2K.JointK.place_of_p12At _ _)

/-- **The door's equation at a called second member, under the head.** -/
theorem door_head_omega {W₀ Rc Tr X₀ Y V Pq : Type} (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} (hα : ∀ x, P.key x = x.pub.key) {w₀ : W₀}
    {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {r : RunC (P5J.F0T o Zp Np cF)}
    (hpl : (P5J.F0T o Zp Np cF).planOk = true)
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V (Common W₀ Rc TableKey) X₀ Pq)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pq)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre t i)
    (h10 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hi : i = firstLen J.p.nums.stages) :
    ∃ m, ProofFile.Honest.midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] (fourOf Np).U
          (fun w : Common W₀ Rc TableKey => w.key) colsOpened m.st.input (restFront J m) =
        stateAtOmega (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) (fourOf Np).U
          (frontBlock Zp.p.chains :: ([b1, b2, b3, b4, b5, b6, b7, b8] ++
            [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)])) (P.key x)
          ((r.run.beforeAt (ProofFile.Honest.storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, u.number⟩).cut i) := by
  obtain ⟨pre₀, tl, e, hl, hL, -⟩ := flat_ten (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) Np b1 b2 b3 b4 b5 b6 b7 b8 hb
  have e' : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ tl := e
  have hp : pre = pre₀ := h10.trans ((congrArg (List.take 10) e').trans (List.take_left' hl))
  rw [hp] at S
  exact door_at_omega hpl hR hrun σ u pre₀ t i S hc Zp.p.chains (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
    [b1, b2, b3, b4, b5, b6, b7, b8] (fourOf Np).U hL (by rw [hα x]; rfl) J hi

theorem place_at {S Cl : Type} (pre : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl))
    (p : VerifiableInference.Desc.Place) (hp : b.place = p) :
    ((pre ++ b :: t).map (·.place))[pre.length]? = some p := by
  simp [hp]

/-- **What stands in front of the test on G_omega is the shared chain's first ten.** -/
theorem pre_at_omega (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hnd : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.map (·.place)).Nodup)
    (nO : H2U.PlaceNums) (hO : Np.O = some nO)
    (pre t : List (Block St ProofFile.Cl)) (b : Block St ProofFile.Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t) (hp : b.place = ⟨2, none, 10, .K12⟩) :
    pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 10 := by
  obtain ⟨pre₀, tl, e, hl, -, hx⟩ := flat_ten (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) Np b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨x, tl', rfl, hxp⟩ := hx nO hO
  have e' : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ x :: tl' := e
  have g1 : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.map (·.place))[pre.length]? = some ⟨2, none, 10, .K12⟩ := by
    rw [hcut]
    exact place_at pre b t _ hp
  have g2 : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.map (·.place))[pre₀.length]? = some ⟨2, none, 10, .K12⟩ := by
    rw [e']
    exact place_at pre₀ x tl' _ hxp
  have hlt : pre.length < ((P5J.F0T o Zp Np cF).shared.blocksInOrder.map (·.place)).length :=
    (List.getElem?_eq_some_iff.1 g1).1
  have hle : pre.length = 10 := (List.getElem?_inj hlt hnd (g1.trans g2.symm)).trans hl
  rw [hcut, ← hle]
  exact (List.take_left' rfl).symm

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.pre_at_omega
#print axioms ProofFile.Honest.K12.Light.door_head_omega
#print axioms ProofFile.Honest.K12.Light.flat_ten
