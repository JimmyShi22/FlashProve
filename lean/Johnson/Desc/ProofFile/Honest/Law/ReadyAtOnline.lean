-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyAtOnline.lean: what is left to show so that `ready` returns at
the maker's return at the online filling: sixteen payments, by name. Everything else that
`ReadyDebts` asks is paid here from the head and the return. One structure; six theorems.

  `OnlinePayments`            the twelve kinds that lay sides in the first chain, the three in the
                              shared chain, the one in the second: sixteen premises
  `firstOf_through`           the first chain of a filling read through is the first chain read through
  `readyDebts_online`         **`ReadyDebts` at the return, from the head, the return and the payments**
  `ready_online`              `ready` returns at every index in range and request with a trace
  `readyAtServedRequests_of_payments`   the proposition `ReadyAtServedRequests`, given
                              `TraceWhereServed`
  `readyDebts_same_sides`     `ReadyDebts` reads of a prover its three lists, its range and its named
                              member alone
  `ready_at_provG`            `ready` at the prover that the field `ready₁` of `PlainAt` names, where
                              that prover's three lists are the return's

«The head» is `P5J.AtMgA`, the structure that says what the public files make.

Which fields are paid here. Of the thirteen fields of `ReadyDebts`: `plan`, `places` from the head;
`book`, `seats₁`, `seats₂`, `seats₃`, `dummy` from the maker's own tests (`atPure_tests`); `once₁`,
`once₂`, `once₃` from `twice_first_fill`, `twice_shared_fill`, `twice_second_fill`, read through by
`twice_thru`. Left: `pays₁`, `pays₂`, `pays₃`: `OnlinePayments`, joined by `kindPays_online_all`,
`kindPays_online_shared_all`, `kindPays_online_second_all`.

What parts this from `ready₁`. That field asks one return of `ready` at `provG`. Three things stand
between: `provG` reads its three lists off a value `G` of `Sides`, and that these are the return's is a
premise here; some index in range, request with a trace, table's randomness and coins must exist;
and the description there is `descZ` at the head's letters, which the head gives.

Limits.
  * Nothing here pays a kind. What is paid by the sixteen is that `chainSteps` returns at the members:
    nothing here says that a part plays, or that a verifier accepts.
  * `ready` returning says nothing on what it returns.
  * That the maker returns is a premise here (hA).
  * The statements under the head stand at the full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import AtFullSide.K12.TwiceFirstW
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm (ServedInput ReadyAtServedRequests TraceWhereServed)
open VerifiableInference.Desc (Block KindName FileDescription Chain)

/-- **The sixteen payments**, at a return of the maker: the twelve kinds that lay sides in the first
chain, the three in the shared chain, the one in the second, each at the description that the maker
returned. -/
structure OnlinePayments {files : VerifierAndGoals.PublicFiles} (returned : OnlineReturn files) : Prop where
  k1 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K1
  k2 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K2
  k3 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K3
  k4 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K4
  k5 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K5
  k6 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K6
  k7 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K7
  k8 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K8
  k10 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K10
  k11 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K11
  k12 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K12
  k13 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K13
  k14Shared : KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared .K14
  k1Shared : KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared .K1
  k12Shared : KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared .K12
  k12Second : KindPays returned.B 2 returned.F.second.blocksInOrder returned.H.second .K12

/-- **The first chain of a list of lots read through is the first chain read through.** -/
theorem firstOf_through {V V' W W' X : Type} (see : V' → V) (wit : W' → W) (Zq : Pub) (G : Ground)
    (ls : List (HLot V W X)) :
    firstOf Zq G (ls.map (HLot.thru see wit)) = (firstOf Zq G ls).map (Placed.thru see wit) := by
  unfold firstOf
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [ih]
    rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {returned : OnlineReturn Z}

/-- **`ReadyDebts` at the return.** Conditional on the head, on the return and on the sixteen
payments. -/
theorem readyDebts_online (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned) :
    ReadyDebts returned.F returned.B returned.H := by
  obtain ⟨hw, s1, s2, s3, hd⟩ := atPure_tests hA
  obtain ⟨eZ, eF⟩ := atPure_at_laid h.laid hA
  obtain ⟨-, -, -, -, -, -, -, e1, e2, e3, -⟩ := atPure_ok hA
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have hpl : returned.F.planOk = true := by
    rw [eF]
    exact h.laid.planOk
  refine ⟨hpl, Johnson.RunOne.Sound.placesOk_of_planOk _ hpl, hw, List.isEmpty_iff.1 s1,
    List.isEmpty_iff.1 s2, List.isEmpty_iff.1 s3, ?_, ?_, ?_, hd, ?_, ?_, ?_⟩
  · rw [e1, eZ]
    show twice (firstOf Zp returned.G (onlineBase.lots.map
      (HLot.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))))) = []
    rw [firstOf_through, twice_thru]
    exact AtFullSide.K12.twice_first_fill h Op _ _ _ _ _
  · rw [e2, eZ]
    show twice ((onlineBase.shared Zp returned.G).map
      (Placed.thru id (Common.thru id (tableCoins Z)))) = []
    rw [twice_thru]
    exact AtFullSide.K12.twice_shared_fill h matrixInput
  · rw [e3]
    show twice ((onlineBase.second returned.Z returned.G).map
      (Placed.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z)))) = []
    rw [twice_thru]
    exact AtFullSide.K12.twice_second_fill _ _ _ _ _ _
  · refine kindPays_online_all hA fun k hk => ?_
    cases k
    all_goals first
      | exact Pm.k1 | exact Pm.k2 | exact Pm.k3 | exact Pm.k4 | exact Pm.k5 | exact Pm.k6
      | exact Pm.k7 | exact Pm.k8 | exact Pm.k10 | exact Pm.k11 | exact Pm.k12 | exact Pm.k13
      | exact absurd (by decide) hk
  · refine kindPays_online_shared_all h hA fun k hk => ?_
    rcases hk with rfl | rfl | rfl
    · exact Pm.k14Shared
    · exact Pm.k1Shared
    · exact Pm.k12Shared
  · exact kindPays_online_second_all hA Pm.k12Second

/-- **`ready` returns at the return, at every index in range, every request with a trace, every
table's randomness and every run's coins.** Conditional on the head, on the return and on the sixteen
payments. -/
theorem ready_online (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned) {w₀ : FullSizeMatrix} {x : ProofFile.Inst}
    (hi : returned.H.inRange w₀ = true) (ht : (returned.H.trace w₀ x).isSome = true)
    (rc : (protocolAtFiles Z).EncodingRandomness) (k : Coins returned.B) :
    ∃ R, ready returned.F returned.B returned.H w₀ rc x k = .ok R :=
  ready_of_sides (readyDebts_online h hA Pm) hi ht rc k

/-- **The proposition `ReadyAtServedRequests`.** Conditional on the head, on the return, on the
sixteen payments and on `TraceWhereServed`. -/
theorem readyAtServedRequests_of_payments (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned)
    {Served : FullSizeMatrix → LPFD.Full.XF → Prop} (hT : TraceWhereServed Served returned) :
    ReadyAtServedRequests Served returned := by
  rintro M rc x k ⟨request, seed, hS, rfl⟩
  obtain ⟨hi, ht⟩ := hT M request _ hS
  exact ready_online h hA Pm hi ht rc k

/-- **`ReadyDebts` reads of a prover its three lists, its range and its named member alone.** -/
theorem readyDebts_same_sides {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
    {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} (Dt : ReadyDebts F B H) (e1 : H'.first = H.first)
    (e2 : H'.shared = H.shared) (e3 : H'.second = H.second) (er : H'.inRange = H.inRange)
    (ed : H'.dummy = H.dummy) : ReadyDebts F B H' := by
  have seats₁ := Dt.seats₁
  have seats₂ := Dt.seats₂
  have seats₃ := Dt.seats₃
  have once₁ := Dt.once₁
  have once₂ := Dt.once₂
  have once₃ := Dt.once₃
  have dummy := Dt.dummy
  have pays₁ := Dt.pays₁
  have pays₂ := Dt.pays₂
  have pays₃ := Dt.pays₃
  rw [← e1] at seats₁ once₁ pays₁
  rw [← e2] at seats₂ once₂ pays₂
  rw [← e3] at seats₃ once₃ pays₃
  rw [← er, ← ed] at dummy
  exact ⟨Dt.plan, Dt.places, Dt.book, seats₁, seats₂, seats₃, once₁, once₂, once₃, dummy, pays₁,
    pays₂, pays₃⟩

/-- **`ready` at the prover that the field `ready₁` of `PlainAt` names.** G: a value of `Sides` whose
three lists are the return's (e1, e2, e3). Conditional on the head, on the return, on the sixteen
payments, on those three equations, and on an index in range and a request with a trace. -/
theorem ready_at_provG (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned)
    {G : ProofFile.Honest.Sides (descZ Zp Np cF) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness OnBytes.TableKey Cells Unit Unit}
    (e1 : (provG Z Zp Np cF returned.B G returned.H).first = returned.H.first)
    (e2 : (provG Z Zp Np cF returned.B G returned.H).shared = returned.H.shared)
    (e3 : (provG Z Zp Np cF returned.B G returned.H).second = returned.H.second) {w₀ : FullSizeMatrix}
    {x : ProofFile.Inst} (hi : returned.H.inRange w₀ = true)
    (ht : (returned.H.trace w₀ x).isSome = true) (rc : (protocolAtFiles Z).EncodingRandomness) (k : Coins returned.B) :
    ∃ R, ready (descZ Zp Np cF) returned.B (provG Z Zp Np cF returned.B G returned.H) w₀ rc x k =
      .ok R := by
  have Dt := readyDebts_online h hA Pm
  rw [(atPure_at_laid h.laid hA).2] at Dt
  exact ready_of_sides (readyDebts_same_sides Dt e1 e2 e3 rfl rfl) hi ht rc k

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.OnlinePayments
#print axioms ProofFile.Honest.Term.firstOf_through
#print axioms ProofFile.Honest.Term.readyDebts_online
#print axioms ProofFile.Honest.Term.ready_online
#print axioms ProofFile.Honest.Term.readyAtServedRequests_of_payments
#print axioms ProofFile.Honest.Term.readyDebts_same_sides
#print axioms ProofFile.Honest.Term.ready_at_provG
