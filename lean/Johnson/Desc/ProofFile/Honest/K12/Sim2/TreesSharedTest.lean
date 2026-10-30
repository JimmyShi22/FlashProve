-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause trees at the test on G_u, at the filling.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesSharedTest.lean: under the head, at the unread filling
onlineProverPartsInUse, at a run of the prover that onlineProverFromPublicFiles returns: the clause trees of the condition at the
second part of the test on G_u, at the job that halfU lays. The law is trees_head_U_pub
(TreesAtHeadUPub.lean); this file pays its premises on the filling, hgU and hgO, and joins its job to
jobRealU (realU_at_head, AtProof/HalfAtPure.lean). No property of the protocol is claimed.

  halves_not_sending   no half of the kind's own stands at a sending's place
  sendings_found       the two sendings' halves are what the search finds in the shared list
  trees_at_shared_test the clause

What is left. hb: the plan's eight sub-protocols; hR, hrun, hc, S, h9: the run's and the filling's;
hbk: the test on the book; hJ: the job is made; hA: onlineProverFromPublicFiles has returned.

Limits. A conditional with no member. The clause reads the input and the carried values: no later law
may take it as a hypothesis on a run and then speak of the random values as sampled anew. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FoundOwnAndShared
import Johnson.Desc.ProofFile.Honest.K12.TreesAtHeadUPub
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtFilling
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain Place K1.qAt)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14 (jobU jobOmega sendingPart liftSend sendPlace)

variable {W₀ : Type}

/-- No half of the kind's own stands at a sending's place. -/
theorem halves_not_sending (d : K14.Data) (wt : W₀ → Weights) (n : ℕ) :
    ∀ g ∈ (K14.proverSidesOfSharedRounds d wt : List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)),
      g.place ≠ sendPlace n := by
  intro g hg e
  unfold K14.proverSidesOfSharedRounds at hg
  rcases List.mem_append.1 hg with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [K14.place, sendPlace] at e
  · split at h
    · obtain rfl := List.mem_singleton.1 h
      simp [K14.place, sendPlace] at e
    · cases h

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The two sendings' halves are what the search finds.** -/
theorem sendings_found (h : P5J.AtMgA o Z D r₀ Zp Np cF x₀) (I : WiderIn W₀) (o₂ : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o Z.pol Z.lay Z.KL (onlineProverPartsInUse I o₂ S O) = .ok A) :
    (A.H.shared.find? fun g => g.place == sendPlace 2) = some ⟨sendPlace 2,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w => I.weights Zp w.w₀)
          (fun w => randAt (K1.qAt Zp Np) w.rc)) (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit)]⟩ ∧
    (A.H.shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf ⟨K1.qAt Zp Np, 0⟩ (fun w => I.weights Zp w.w₀)
          (fun w => randAt (K1.qAt Zp Np) w.rc)) (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)) :
        Part Empty (Common W₀ IndexCommitterCoins TableKey) Unit)]⟩ := by
  have eZ : A.Z = Zp := (atPure_at_laid h.laid hA).1
  subst eZ
  have h1 : nowSharedBy (I.weights A.Z) A.Z =
      .ok (K14.proverSidesOfSharedRounds { S := (K1.qAt A.Z Np).S, atPoint := 0, atZeta := 6 } (I.weights A.Z) ++
        K14.proverSidesOfSharedSendings { P := K1.qAt A.Z Np, atPoint := 0 } (I.weights A.Z)
          (K14.randNow (K1.qAt A.Z Np))) := K14.sixBody_at_head h _
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  have hs' : A.H.shared = sharedWithUO I A.Z := hs
  have e0 : sharedWithUO I A.Z =
      K14.proverSidesOfSharedRounds { S := (K1.qAt A.Z Np).S, atPoint := 0, atZeta := 6 } (I.weights A.Z) ++
        K14.proverSidesOfSharedSendings { P := K1.qAt A.Z Np, atPoint := 0 } (I.weights A.Z)
          (K14.randNow (K1.qAt A.Z Np)) ++
        halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z ++
        halfO (I.weights A.Z) A.Z := by
    show (match nowSharedBy (I.weights A.Z) A.Z with
      | .ok six =>
        six ++ halfU (I.weights A.Z) (fun w => Bind.ForProver.encW A.Z (I.weights A.Z w)) A.Z ++
          halfO (I.weights A.Z) A.Z
      | .error _ => []) = _
    rw [h1]
  have hn : ∀ n, (K14.proverSidesOfSharedRounds { S := (K1.qAt A.Z Np).S, atPoint := 0, atZeta := 6 } (I.weights A.Z) :
      List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)).find?
        (fun g => g.place == sendPlace n) = none := fun n =>
    List.find?_eq_none.2 fun g hg hb => halves_not_sending _ _ n g hg (beq_iff_eq.1 hb)
  rw [hs', e0, K14.sendHalves_eq]
  refine ⟨?_, ?_⟩
  · rw [List.find?_append, List.find?_append, List.find?_append, hn]
    rfl
  · rw [List.find?_append, List.find?_append, List.find?_append, hn]
    rfl

/-- **The clause trees at the test on G_u, at the job that the filling lays.** -/
theorem trees_at_shared_test (h : P5J.AtMgA o Z D r₀ Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (I : WiderIn W₀) (o₂ : SecondHashFunctionArgument) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o Z.pol Z.lay Z.KL (onlineProverPartsInUse I o₂ S' O) = .ok A) {Bk : ProverCoinCounts}
    {w₀ : W₀} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {r : RunC (P5J.F0T o Zp Np cF)}
    (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit)
    (hJ : realU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp = some J)
    (Js : SimJob TableKey)
    (hR : ready (P5J.F0T o Zp Np cF) Bk A.H w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (St' : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk A.H w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hbk : bookCutsU Bk ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U = true) :
    ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk A.H w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m)).map
          (·.1) = (fourOf Np).U.nums.first.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), (fourOf Np).U.nums.first[i]?
            = some o' →
          (J.trees₀ m.st.input (restFront J m) (stretches _ ca)
            (rowsAt J (stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt (storedShown (A.H.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).treeCols (ProofFile.Honest.srcOf 1
                  o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1 := by
  have eZ : A.Z = Zp := (atPure_at_laid h.laid hA).1
  have hJ' := realU_at_head h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb (I.weights Zp)
    (fun w => Bind.ForProver.encW Zp (I.weights Zp w))
  rw [hJ] at hJ'
  have hst : A.H.storedWords = fun w rc i y =>
      (Bind.ForProver.encW Zp (I.weights Zp w) rc i y).map (·.map OnBytes.Slice.ofF) := by
    funext w rc' i y
    rw [atPure_storedWords hA, eZ]
    rfl
  obtain ⟨hgU, hgO⟩ := sendings_found h I o₂ S' O hA
  refine trees_head_U_pub h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb (fun w => I.weights Zp w.w₀)
    (fun w => randAt (K1.qAt Zp Np) w.rc) J ?_ Js hR σ pre t St' h9 hrun hc hgU hgO hbk
  rw [hst]
  exact Option.some.inj hJ'

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.halves_not_sending
#print axioms ProofFile.Honest.K12.Sim2.sendings_found
#print axioms ProofFile.Honest.K12.Sim2.trees_at_shared_test
