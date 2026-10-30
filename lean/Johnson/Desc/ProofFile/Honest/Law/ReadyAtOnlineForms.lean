-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyAtOnlineForms.lean: more forms beside
Honest/Law/ReadyAtOnline.lean. No definition; nine theorems.

  `description_is_heads`      under the head the maker's description is the head's
  `kindPays_first_of_base_return`, `kindPays_shared_of_base_return`,
  `kindPays_second_of_base_return`   a kind that pays at every return at the base filling pays at the
                              online return: in each of the three chains
  `readyDebts_proverAt`       `Committer.proverAt` keeps `ReadyDebts`
  `ready_at_played`           `ready` at the prover that the online provers read
  `ready_one_at_provG`        **the type of the field `ready₁` of `PlainAt`, to the letter**: from the
                              payments, the three equations on G, `TraceWhereServed` and one served pair
  `ready_where_files_pass`, `readyAtServedRequests_where_files_pass`   the same with no head among
                              the premises: the public files pass the two tests

«The head» is `P5J.AtMgA`, the structure that says what the public files make.

Limits.
  * Nothing here pays a kind. What is paid by the payments is that `chainSteps` returns at the members:
    nothing here says that a part plays, or that a verifier accepts.
  * `ready_one_at_provG` asks one served pair. That some pair is served is not shown here: without
    one it says nothing.
  * The theorems on `ready` hang on a return of the maker (hA).
  * That the public files pass the tests is a premise.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyAtOnline
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.LPFPol.LiveAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm (ServedInput ReadyAtServedRequests TraceWhereServed)
open VerifiableInference.Desc (Block KindName FileDescription Chain)

/-! ## 1 From the base filling's return to the online return -/

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files} {S Cl : Type}
  {bs : List (Block S Cl)} {κ : KindName}

/-- **A kind that pays at every return at the base filling pays at the online return: first chain.** -/
theorem kindPays_first_of_base_return (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 0 bs A₀.H.first κ) :
    KindPays returned.B 0 bs returned.H.first κ := by
  obtain ⟨A₀, h₀, eZ, eG, -, eB⟩ := online_base_return hA
  obtain ⟨-, -, -, -, -, -, -, e1, -⟩ := atPure_ok h₀
  refine kindPays_of_base_sides id (tableCoins files) matrixInput.dummy hA fun L hL x hx hk => ?_
  rw [← eB]
  refine hbase A₀ h₀ x ?_ hk
  rw [e1, eZ, eG]
  exact List.mem_flatMap.2 ⟨L, hL, hx⟩

/-- **The same at the shared chain.** -/
theorem kindPays_shared_of_base_return (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 1 bs A₀.H.shared κ) :
    KindPays returned.B 1 bs returned.H.shared κ := by
  obtain ⟨A₀, h₀, eZ, eG, -, eB⟩ := online_base_return hA
  obtain ⟨-, -, -, -, -, -, -, -, e2, -⟩ := atPure_ok h₀
  refine kindPays_shared_of_base_sides id (tableCoins files) matrixInput.dummy hA fun x hx hk => ?_
  rw [← eB]
  refine hbase A₀ h₀ x ?_ hk
  rw [e2, eZ, eG]
  exact hx

/-- **The same at the second chain.** -/
theorem kindPays_second_of_base_return (hA : onlineMaker files = .ok returned)
    (hbase : ∀ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ →
        KindPays A₀.B 2 bs A₀.H.second κ) :
    KindPays returned.B 2 bs returned.H.second κ := by
  obtain ⟨A₀, h₀, eZ, eG, -, eB⟩ := online_base_return hA
  obtain ⟨-, -, -, -, -, -, -, -, -, e3, -⟩ := atPure_ok h₀
  refine kindPays_second_of_base_sides id (tableCoins files) matrixInput.dummy hA fun x hx hk => ?_
  rw [← eB]
  refine hbase A₀ h₀ x ?_ hk
  rw [e3, eZ, eG]
  exact hx

end

/-! ## 2 The other provers -/

/-- **`Committer.proverAt` keeps `ReadyDebts`**: it changes the stored tables and the key alone. -/
theorem readyDebts_proverAt {Xi W₀ Rc Sd Xc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} (Cm : Committer W₀ Rc Sd Xc Xi Ky) (item₀ : Nat)
    (Dt : ReadyDebts F B H) : ReadyDebts F B (Cm.proverAt item₀ H) :=
  readyDebts_same_sides Dt rfl rfl rfl rfl rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {returned : OnlineReturn Z}

/-- **Under the head the maker's description is the head's.** -/
theorem description_is_heads (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) : returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF :=
  (atPure_at_laid h.laid hA).2

/-- **`ready` at the prover that the online provers read**: the return's prover with a committer's
tables and key; the online provers use `cmAlong` at the item 0. Conditional on the head, on the
return, on the sixteen payments, on an index in range and a request with a trace. -/
theorem ready_at_played {Sd Xc : Type} (Cm : Committer FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Sd Xc ProofFile.Inst OnBytes.TableKey)
    (item₀ : Nat) (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned) {w₀ : FullSizeMatrix} {x : ProofFile.Inst}
    (hi : returned.H.inRange w₀ = true) (ht : (returned.H.trace w₀ x).isSome = true)
    (rc : (protocolAtFiles Z).EncodingRandomness) (k : Coins returned.B) :
    ∃ R, ready (descZ Zp Np cF) returned.B (Cm.proverAt item₀ returned.H) w₀ rc x k = .ok R := by
  have Dt := readyDebts_online h hA Pm
  rw [description_is_heads h hA] at Dt
  exact ready_of_sides (readyDebts_proverAt Cm item₀ Dt) hi ht rc k

/-- **The type of the field `ready₁` of `PlainAt`, to the letter.** Conditional on the head, on the
return, on the sixteen payments, on G's three lists being the return's, on `TraceWhereServed` and on
one served pair. -/
theorem ready_one_at_provG (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) (Pm : OnlinePayments returned)
    {G : ProofFile.Honest.Sides (descZ Zp Np cF) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness OnBytes.TableKey Cells Unit Unit}
    (e1 : (provG Z Zp Np cF returned.B G returned.H).first = returned.H.first)
    (e2 : (provG Z Zp Np cF returned.B G returned.H).shared = returned.H.shared)
    (e3 : (provG Z Zp Np cF returned.B G returned.H).second = returned.H.second)
    {Served : FullSizeMatrix → LPFD.Full.XF → Prop} (hT : TraceWhereServed Served returned) {M : FullSizeMatrix}
    {request : LPFD.Full.XF} (hS : Served M request) :
    ∃ w₀ rc x k R,
      ready (descZ Zp Np cF) returned.B (provG Z Zp Np cF returned.B G returned.H) w₀ rc x k =
        .ok R := by
  have rc : (protocolAtFiles Z).EncodingRandomness := Classical.choice (protocolAtFiles Z).encodingRandomnessIsNonempty
  have seed : (protocolAtFiles Z).OutOfDomainSeed := Classical.choice (protocolAtFiles Z).outOfDomainSeedIsNonempty
  obtain ⟨hi, ht⟩ := hT M request ((protocolAtFiles Z).recOf M rc seed) hS
  obtain ⟨R, hR⟩ := ready_at_provG h hA Pm e1 e2 e3 hi ht rc default
  exact ⟨M, rc, _, default, R, hR⟩

/-! ## 3 With no head among the premises -/

/-- **`ready` returns where the public files pass.** Conditional on the two tests, on the return, on
the sixteen payments, on an index in range and a request with a trace. -/
theorem ready_where_files_pass (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (hA : onlineMaker Z = .ok returned)
    (Pm : OnlinePayments returned) {w₀ : FullSizeMatrix} {x : ProofFile.Inst}
    (hi : returned.H.inRange w₀ = true) (ht : (returned.H.trace w₀ x).isSome = true)
    (rc : (protocolAtFiles Z).EncodingRandomness) (k : Coins returned.B) :
    ∃ R, ready returned.F returned.B returned.H w₀ rc x k = .ok R := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨_, _, _, _, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  exact ready_online h hA Pm hi ht rc k

/-- **The proposition `ReadyAtServedRequests` where the public files pass.** Conditional on the two
tests, on the return, on the sixteen payments and on `TraceWhereServed`. -/
theorem readyAtServedRequests_where_files_pass (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (hA : onlineMaker Z = .ok returned)
    (Pm : OnlinePayments returned) {Served : FullSizeMatrix → LPFD.Full.XF → Prop}
    (hT : TraceWhereServed Served returned) : ReadyAtServedRequests Served returned := by
  obtain ⟨_, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨_, _, _, _, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  exact readyAtServedRequests_of_payments h hA Pm hT

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.kindPays_first_of_base_return
#print axioms ProofFile.Honest.Term.kindPays_shared_of_base_return
#print axioms ProofFile.Honest.Term.kindPays_second_of_base_return
#print axioms ProofFile.Honest.Term.readyDebts_proverAt
#print axioms ProofFile.Honest.Term.description_is_heads
#print axioms ProofFile.Honest.Term.ready_at_played
#print axioms ProofFile.Honest.Term.ready_one_at_provG
#print axioms ProofFile.Honest.Term.ready_where_files_pass
#print axioms ProofFile.Honest.Term.readyAtServedRequests_where_files_pass
