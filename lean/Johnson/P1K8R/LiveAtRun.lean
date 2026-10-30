-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LiveAtRun.lean: THE SMALLNESS TEST: ALONG THE HONEST SIDE's OWN RUN (`runC`,
Johnson/Desc/ProofFile/Honest/Walk.lean) OF THE PROOF FILE's DESCRIPTION, THE STATE IN FRONT OF A
SEGMENT's BATCHING HAS A COLUMN THAT IS ALL 0 JUST IF THE MATRIX THAT THE LIST's OWN CHALLENGE AT
THE DRAW's ROUND SHOWS HAS ONE. A LEMMA; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding. An assembly: no new argument.

l < 25. Kd := 14 l + 6, or 343 at the head's: the number of the member that draws the matrix. K :=
14 l + 9, or 347: the batching's.
  **`live_at_run`**   in the goals' scope; Xl the built segment; at every book, prover, input, coins
      and challenges ρ: the run returns; `frontsOf` at its first view has an entry e at K; sz fits
      the place's parameters; ρ's challenge at the draw's round shows the list of entries of the
      typed matrix β: then e's state holds data tl with: `allLive tl = false` just if some column of
      β is all 0; and cols tl = sz.columns
By: `frontsOf_step`, `quiet_in_event` (Johnson/Desc/ProofFile/Honest/K8/FrontsStep.lean) ·
`frontsOf_between` (FrontsBetween.lean) · `matrix_at_batch` (Johnson/P1K8R/MatrixAtBatch.lean) ·
P1K8S.sitsAt_open (Johnson/P1K8R/OrderAtSeat.lean).
Limits. That a run returns, and that an entry K is listed, are premises. That sz fits is a premise.
-/
import Johnson.P1K8R.FallAtRun
import Johnson.P1K8R.MatrixAtBatch
import Johnson.Desc.ProofFile.Honest.K8.FrontsBetween

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws RunC runC frontsOf)
open ProofFile.Honest.K8 (allLive cols rnds)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The state in front of the batching against the list's own challenge at the draw's round.** -/
theorem live_at_run (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ Xl : LinkH, Bs.G₀.built[l]? = some Xl ∧
      ∀ {W₀ Rc Ky Tr X₀ X' : Type} (Bk : ProverCoinCounts) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X') (w₀ : W₀)
        (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk) (ρ : Draws) (r : RunC (descAt Z A₂ B₂ c))
        (e : Place × S × List Fmt.Drawn) (sz : Size) (β : Dr sz) (dr : Fmt.Drawn),
        runC (descAt Z A₂ B₂ c) Bk H w₀ rc x k ρ = .ok r →
        (frontsOf 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound r.run.views.1).rounds
          (withEmptySealRound r.run.views.1).opened)[14 * l + (if l = 24 then 11 else 9)]? = some e →
        Fits (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar sz →
        ρ.first[rnds (c.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2))]? = some dr →
        dr.trits.toArray = listOf β →
        ∃ tl, e.2.1.tl? = some tl ∧
          (allLive tl = false ↔ ∃ (μ : Fin sz.NM) (c' : Fin (sz.k μ)), ∀ u, (β μ u c').val = 0) ∧
          cols tl = sz.columns := by
  have hx : (l, if l = 24 then 5 else 4, if l = 24 then 3 else 2) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨b8, Xl, hf8, hXl, hmat⟩ := matrix_at_batch hS hR O _ hx
  obtain ⟨Lk, b8', Xl', -, -, hf8', -, -, -, -, hstep⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain rfl : b8 = b8' := Option.some.inj (hf8.symm.trans hf8')
  refine ⟨Xl, hXl, ?_⟩
  intro W₀ Rc Ky Tr X₀ X' Bk H w₀ rc x k ρ r e sz β dr hr he hfit hdr hβ
  have hK : 14 * l + (if l = 24 then 11 else 9) =
      14 * l + (if l = 24 then 5 else 4) + 2 + 1 + (if l = 24 then 3 else 2) := by
    split <;> omega
  rw [hK] at he
  obtain ⟨e₁, he₁⟩ := ProofFile.Honest.K8.frontsOf_earlier _ he
    (k := 14 * l + (if l = 24 then 5 else 4) + 2 + 1) (Nat.le_add_right _ _)
  obtain ⟨e₀, b, cols₀, m₀, -, g2, g3, g4⟩ := ProofFile.Honest.K8.frontsOf_step 0 _ _ _ _ _ e₁ he₁
  obtain rfl : b8 = b := Option.some.inj (hf8.symm.trans g2)
  have h1 : b8.rounds.length = 1 := by
    obtain ⟨r', hr', -⟩ := (hstep 0 _ _ _ _ _).1 g4
    rw [← g3, hr']
    rfl
  have hbD : (descAt Z A₂ B₂ c).first.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]? = some b8 := hf8
  obtain ⟨zs, r₀, cols₁, m₁, -, q2, q3⟩ := ProofFile.Honest.K8.quiet_in_event hr hbD h1 he₁
  have hr₀ : r₀.drawn = dr := Option.some.inj (q2.symm.trans hdr)
  obtain ⟨rs', cols', r₂, c₂, hfold⟩ := ProofFile.Honest.K8.frontsOf_between 0 _ _ _ _ _ _ e₁ e he₁ he
  obtain ⟨tl, t1, -, t2, t3⟩ :=
    hmat 0 zs.2 e₁.2.1 r₀ cols₁ m₁ rs' cols' _ sz β hfit q3 (by rw [hr₀]; exact hβ) hfold
  exact ⟨tl, t1, t2, t3⟩

end

end P1K8

#print axioms P1K8.live_at_run
