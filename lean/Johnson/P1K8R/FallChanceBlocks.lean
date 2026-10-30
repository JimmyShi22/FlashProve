-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallChanceBlocks.lean: THE SMALLNESS TEST: THE CHANCE OF
Johnson/P1K8R/FallChanceAll.lean AT THE SAMPLER's LAYER: THE BATCHING ROUND's CHALLENGE IS WHAT THE
FORMAT's SAMPLER MAKES OF UNIFORM HASH BLOCKS. Lemmas; none of the library's goals. No prover stands
in them; nothing on completeness, soundness or hiding. An assembly: no new argument.

The law is that of Johnson/Desc/K8/Honest/ChanceOfCounts.lean. Round j's challenges are strings of
hash blocks (through an injective view: A j := the strings of blocks and view := id is meant; the
other rounds' types are free letters, meant as the other rounds' blocks); the typed challenge is the
block sampler's value (Run.bsRound … .φ, Run/PlanDraws.lean), and the step is asked at a round whose
challenge is that value's untyped view.
  `blocks_fib`   at most w strings of blocks give one field element, w the sampler's number
  **`fall_chance_blocks`**   `fall_chance_all` there: the bound is nU[2] * d * w / (the number of
      round j's challenges)
  **`fall_chance_sampled`**   where round j's challenges are as many as the strings of blocks: the
      bound is kapSl 128 ^ (the draws' exponent) * (nU[2] * d) / (the number of the round's typed
      challenges): the sampler's bias is paid at round j alone
By: `fall_chance_all` · `shows_chi`, `elems_inj`, `oneElem_bat`
(Johnson/Desc/K8/Honest/ChiTyped.lean) · bsRound_good_ex (OnBytes/Slice/RatesEx.lean).
Limits: those of FallChanceAll.lean: front IS A LETTER. Nothing here speaks of the test of work:
that over each string of blocks just one written verifier message passes it is the library's
GChal.cnt_pass (Iop/GrindProofs.lean); that a prover's round is uniform on the messages that pass is
not said. That a random oracle's answers along a run are such a list is not said.

-/
import Johnson.P1K8R.FallChanceAll
import OnBytes.Slice.RatesEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open Iop
open scoped ENNReal

/-- At most w strings of blocks give one field element. -/
theorem blocks_fib (p : K9.Where) (k : Fmt.Kind) (h5 : k ≠ .seeds) (h6 : k ≠ .sealed)
    (x : Cb.Gl.E) :
    Prob.cnt (fun u : Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256 =>
      elOf (K9.entry p) k ((Run.bsRound .two (K9.entry p) k).φ u) = x) ≤
      (Run.bsRound .two (K9.entry p) k).w := by
  have hg := bsRound_good_ex (K9.entry p) k (Nat.zero_le _)
  by_cases hv : ∃ v, elOf (K9.entry p) k v = x
  · obtain ⟨v, hv⟩ := hv
    exact (Prob.cnt_mono fun u hu =>
      elems_inj _ (oneElem_bat p k h5 h6) _ _ (hu.trans hv.symm)).trans (hg.fib v)
  · rw [Prob.cnt_false fun u hu => hv ⟨_, hu⟩]
    exact Nat.zero_le _

/-- **The chance at the sampler's layer.** -/
theorem fall_chance_blocks {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (k : Fmt.Kind) (_ : k ≠ .seeds) (_ : k ≠ .sealed)
        (view : A j → (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (_ : Function.Injective view)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : ∀ f a, front (Function.update f j a) = front f)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn = Run.drawnOf .two (K9.entry p) k
                ((Run.bsRound .two (K9.entry p) k).φ (view (f j))) ∧
              b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d * (Run.bsRound .two (K9.entry p) k).w : ℕ) : ℝ≥0∞) /
            Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_all hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j k h5 h6 view hview front hfree hreach d hd
  have h1 := oneElem_bat p k h5 h6
  have hw : ∀ x, Prob.cnt (fun a =>
      elOf (K9.entry p) k ((Run.bsRound .two (K9.entry p) k).φ (view a)) = x) ≤
      (Run.bsRound .two (K9.entry p) k).w := fun x => by
    have h := Prob.cnt_comp_le view (w := 1)
      (fun u => Prob.cnt_le_one fun a a' ha ha' => hview (ha.trans ha'.symm))
      (fun u => elOf (K9.entry p) k ((Run.bsRound .two (K9.entry p) k).φ u) = x)
    rw [Nat.mul_one] at h
    exact h.trans (blocks_fib p k h5 h6 x)
  have h := hall j
    (fun a => elOf (K9.entry p) k ((Run.bsRound .two (K9.entry p) k).φ (view a))) _ hw front hfree
    hreach d hd
  refine (Prob.pr_mono _ fun f hf => ?_).trans h
  obtain ⟨zs, hz, r, cols, t, m, hr, hst, hzu⟩ := hf
  refine ⟨zs, hz, r, cols, t, m, ?_, hst, hzu⟩
  rw [hr, shows_chi _ k h1]
  rfl

/-- **The same, with the sampler's bias in the place of its number.** -/
theorem fall_chance_sampled {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (k : Fmt.Kind) (_ : k ≠ .seeds) (_ : k ≠ .sealed)
        (view : A j → (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (_ : Function.Injective view)
        (_ : Fintype.card (A j) =
          Fintype.card (Fin (Run.bsRound .two (K9.entry p) k).b → Dig 256))
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : ∀ f a, front (Function.update f j a) = front f)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn = Run.drawnOf .two (K9.entry p) k
                ((Run.bsRound .two (K9.entry p) k).φ (view (f j))) ∧
              b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          kapSl 128 ^ Run.exAll (Fmt.dsOf (K9.entry p) k) *
            (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d : ℕ) : ℝ≥0∞) /
            (Nat.card (Run.Ch .two (K9.entry p) k) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_blocks hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j k h5 h6 view hview hcard front hfree hreach d hd
  refine (hall j k h5 h6 view hview front hfree hreach d hd).trans ?_
  have hr := (bsRound_good_ex (K9.entry p) k (Nat.zero_le _)).ratio
  rw [← hcard] at hr
  have hB0 : (Fintype.card (A j) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card (A j) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hV0 : (Nat.card (Run.Ch .two (K9.entry p) k) : ℝ≥0∞) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  have hVt : (Nat.card (Run.Ch .two (K9.entry p) k) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [Nat.cast_mul ((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d)]
  generalize (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d : ℕ) : ℝ≥0∞) = N
  generalize kapSl 128 ^ Run.exAll (Fmt.dsOf (K9.entry p) k) = κ at hr ⊢
  generalize ((Run.bsRound .two (K9.entry p) k).w : ℝ≥0∞) = w at hr ⊢
  generalize (Nat.card (Run.Ch .two (K9.entry p) k) : ℝ≥0∞) = V at hr hV0 hVt ⊢
  generalize (Fintype.card (A j) : ℝ≥0∞) = B at hr hB0 hBt ⊢
  have key : N * w * V ≤ κ * N * B := by
    calc N * w * V = N * (w * V) := by ring
      _ ≤ N * (κ * B) := mul_le_mul' le_rfl hr
      _ = κ * N * B := by ring
  calc N * w / B = N * w * V / V / B := by rw [ENNReal.mul_div_cancel_right hV0 hVt]
    _ ≤ κ * N * B / V / B := ENNReal.div_le_div_right (ENNReal.div_le_div_right key _) _
    _ = κ * N * V⁻¹ * (B * B⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ = κ * N / V := by rw [ENNReal.mul_inv_cancel hB0 hBt, mul_one, div_eq_mul_inv]

end P1K8

#print axioms P1K8.blocks_fib
#print axioms P1K8.fall_chance_blocks
#print axioms P1K8.fall_chance_sampled
