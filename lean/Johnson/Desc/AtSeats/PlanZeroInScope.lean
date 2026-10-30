-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanZeroInScope.lean: THE CLOSED TEST `planZeroB`
(Johnson/Desc/AtSeats/PlanGOfTest.lean: six facts on the planner's values at the first segment
come down to it) ACCEPTS, IN THE GOALS' SCOPE, WHERE EVERY SUB-PROTOCOL OF THE FIRST CHAIN PASSES
ITS OWN TEST ON THE PLAN. Statements with their proofs: calls and unfoldings. `built_zero`: the
  planner's entry of segment 0 has the group 0 and, of that group's plan in the public parameters,
  the number of slots and the planned ledger: the blank letters' entry is the planner's but for
  its routine (`blank_built`, Johnson/IMR/OwnSeat.lean); its group and its plan's values by
  `ground_named`, `ground_tails` (Johnson/IMR/PureJoin.lean, K8Seat.lean). `planZero_in_scope`:
  the test. SLOTS: `built_zero`. UNHEARD: `public_G_heard`
  (Johnson/Desc/First/Look/HeardNone.lean). PLACE: the lookup argument on the calls at segment 0
  stands in the flat list (`k3_of`); its own test on the plan holds the kind's public test at the
  place's parameters (`stated_planOk`, Johnson/Desc/First/Look/K3PlanOfOk.lean): a shape, and room
  within the slots; the rest by `lookAt`'s text.
What is not claimed. That the scope can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.AtSeats.PlanGOfTest
import Johnson.Desc.First.Look.HeardNone
import Johnson.Desc.First.Look.K3PlanOfOk
import Johnson.IMR.K3Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt lookAt)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open ProofFile (Cl)
open IM (Open)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The planner's entry of segment 0, against the public parameters' first group's plan. -/
theorem built_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) :
    ∃ X0 hp, Z.p.built.links[0]? = some X0 ∧ X0.g = 0 ∧ Z.p.X.G[0]? = some hp ∧
      X0.ns = hp.ns ∧ X0.Fp = hp.Fp := by
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨l0, _, hb0, _, hg0, _⟩ := nam 0 (by omega)
  obtain ⟨tails, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, _, l0', _, hG, _, hb0', _, hFp, _, hns, _⟩ := tails 0 (by omega)
  obtain rfl : l0 = l0' := Option.some.inj (hb0.symm.trans hb0')
  obtain ⟨links, e⟩ := Meaning.K2.blank_built O.blank
  rw [e] at hb0
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hb0
  have hl1 : 2 * 0 < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [O.W] at hG
  exact ⟨_, hp, Array.getElem?_eq_getElem hl1, (congrArg (·.g) e').trans hg0, hG,
    (congrArg (·.ns) e').trans hns, (congrArg (·.Fp) e').trans hFp⟩

/-- **The closed test accepts.** -/
theorem planZero_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true) : planZeroB Z.p.built.links Z.p.X false = true := by
  obtain ⟨X0, hp, h0, hg, hG, hns, hFp⟩ := built_zero hS hR O
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← O.W]
    exact IM.ground_publicK O.pub O.blank
  obtain ⟨p4, ng, -⟩ := Meaning.scope_plans hS hR hX
  have hh : hp.tl.heard = none := Fo.ZPlan.public_G_heard hX 0 hp hG
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O 0 (by omega) false
  have hb : b'.planOk = true := by
    rw [← IM.alone_planOk hla]
    exact hOk b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  rw [O.W] at h3
  obtain ⟨i, d, p, laid, hi, hpc, hP, hk⟩ := K3.stated_planOk _ _ _ _ _ _ b' h3 hb
  obtain rfl : 0 = i := Option.some.inj hi
  have hd : d = false := by
    refine (K3.pieceAt_inj Z.p.X 0 (d' := false) (hpc.symm.trans ?_))
    unfold K3.pieceAt K3.isHead
    rw [p4, ng]
    rfl
  subst hd
  unfold VerifiableInference.Desc.First.Look.P.planOk at hk
  cases hf : p.shape with
  | none =>
    rw [hf] at hk
    cases hk
  | some f =>
    rw [hf] at hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    have hroom := hk.1.1.2
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hP
    have hlk := IM.lookAt_link hx
    have hxx : x.ns = hp.ns ∧ x.F.next = (hp.Fp.fillL.slots hp.ns).next := by
      unfold lookAt at hx
      simp [p4, ng, hG] at hx
      rw [← hx]
      exact ⟨rfl, rfl⟩
    have hroom' : x.F.next + Forest.elems f ≤ x.ns := hroom
    have hst : (startFork (pubOf X0) hp.ns).next = x.F.next := by
      rw [hxx.2]
      show X0.Fp.next = _
      rw [hFp]
      rfl
    unfold planZeroB
    rw [h0]
    dsimp only
    rw [hg, hG]
    dsimp only
    rw [hP]
    dsimp only
    rw [hf]
    dsimp only
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
      Option.isNone_iff_eq_none]
    exact ⟨⟨hns, hh⟩, ⟨⟨rfl, hst⟩, by rw [← hxx.1]; exact hroom'⟩, hlk⟩

end

end VerifiableInference.Desc.K13.Law
