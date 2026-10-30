-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsBlocks.lean: THE SMALLNESS TEST: THE BOUND OF Johnson/P1K8R/UnitsTest.lean AT THE
KIT WHOSE CHALLENGES ARE STRINGS OF HASH BLOCKS (Run.ckP .two, Run/PlanPull.lean): THE FACTOR FOR
THE SAMPLER's BIAS WRITTEN OUT. Lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding. An assembly: no new argument.

At that kit a round's challenge is a string of hash blocks u; what it shows is what the format's
block sampler makes of u (Run.drawnOf … ((Run.bsRound …).φ u)). p: the size of the base field
(Fmt.Fld.two.p). kapSl 128 = 1 + (2 ^ 128)⁻¹ (Iop/DrawOf.lean).
  `exAll_one`   a round that draws one field element and nothing else has the exponent 3
  `blocks_el`   at such a round whose entry states positions of at most 64 bits: at most w strings
      give one field element, w the sampler's number
  `ratio_div`, `blocks_bound`   n * w / (the number of strings) is at most kapSl 128 ^ 3 * n / p ^ 3
  **`units_gate_blocks`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked
      Z`): in the goals' scope, at every segment l < 25, b the seated batching block, s reached at
      its number, d a round's data with the batching's entry: the measure (Iop.prRho, uniform on
      that one round's messages at Run.ckP .two) of the messages at which `unitsT b nU s` says yes
      of what is shown is at most kapSl 128 ^ 3 * (nU[2] * (p.rows - 1)) / p ^ 3
By: `units_gate_test`, `card_one_elem` · `shows_chi`, `elems_inj`, `oneElem_bat`
(Johnson/Desc/K8/Honest/ChiTyped.lean) · bsRound_good_ex (OnBytes/Slice/RatesEx.lean): BS.Good's fib
and ratio (Iop/Draw.lean).
Limits. Those of UnitsTest.lean: `RowsAsked Z` IS A PREMISE; one of the tests on the ledger's
weights. The uniform law on one round's strings of blocks is named, not derived: that a random
oracle's answers along a run are such blocks is not said. The bound is a product and a quotient of
extended non-negative reals: it is not written as a quotient of two naturals. No number is
evaluated.

-/
import Johnson.P1K8R.UnitsTest
import OnBytes.Slice.RatesEx
import Run.PlanPull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach)
open Iop
open scoped ENNReal

/-- A round that draws one field element has the exponent 3. -/
theorem exAll_one (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) :
    _root_.Run.exAll (Fmt.dsOf e k) = 3 := by
  have e0 : Fmt.dsOf e k = [.elem, .trits 0] := h
  rw [e0]
  rfl

/-- At most w strings of blocks give one field element. -/
theorem blocks_el (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) (hlog : e.logN ≤ 64)
    (x : Cb.Gl.E) :
    Prob.cnt (fun u : Fin (_root_.Run.bsRound .two e k).b → Dig 256 =>
      elOf e k ((_root_.Run.bsRound .two e k).φ u) = x) ≤ (_root_.Run.bsRound .two e k).w := by
  have hg := bsRound_good_ex e k hlog
  by_cases hv : ∃ v, elOf e k v = x
  · obtain ⟨v, hv⟩ := hv
    exact (Prob.cnt_mono fun u hu => elems_inj _ h _ _ (hu.trans hv.symm)).trans (hg.fib v)
  · rw [Prob.cnt_false fun u hu => hv ⟨_, hu⟩]
    exact Nat.zero_le _

/-- Arithmetic. -/
theorem ratio_div (N w V B κ : ℝ≥0∞) (hr : w * V ≤ κ * B) (hB0 : B ≠ 0) (hBt : B ≠ ⊤)
    (hV0 : V ≠ 0) (hVt : V ≠ ⊤) : N * w / B ≤ κ * N / V := by
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

/-- The count times the sampler's number, over the number of strings. -/
theorem blocks_bound (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) (hlog : e.logN ≤ 64)
    (n : ℕ) :
    ((n * (_root_.Run.bsRound .two e k).w : ℕ) : ℝ≥0∞) /
        (Nat.card ((_root_.Run.ckP .two).Ch e k) : ℝ≥0∞) ≤
      kapSl 128 ^ 3 * (n : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  have hr := (bsRound_good_ex e k hlog).ratio
  rw [exAll_one e k h] at hr
  have hV : Nat.card (_root_.Run.Vals .two (Fmt.dsOf e k)) = Fmt.Fld.two.p ^ 3 :=
    card_one_elem e k h
  rw [hV] at hr
  have hB : Nat.card ((_root_.Run.ckP .two).Ch e k) =
      Fintype.card (Fin (_root_.Run.bsRound .two e k).b → Dig 256) := Nat.card_eq_fintype_card
  rw [hB, Nat.cast_mul]
  have hp : Fmt.Fld.two.p ^ 3 ≠ 0 := by
    rw [← hV, Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hB0 : Fintype.card (Fin (_root_.Run.bsRound .two e k).b → Dig 256) ≠ 0 :=
    (Fintype.card_pos_iff.2 ⟨fun _ _ => false⟩).ne'
  exact ratio_div _ _ _ _ _ hr (by exact_mod_cast hB0)
    (ENNReal.natCast_ne_top _) (by exact_mod_cast hp) (ENNReal.natCast_ne_top _)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **At strings of hash blocks.** -/
theorem units_gate_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          unitsT b (ProofFile.k8NU Bs.G₀ X) s (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤
          kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate_test hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 z s hr
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have hlog : d.entry.logN ≤ 64 := by
    rw [he]
    exact Nat.zero_le _
  have k := h (_root_.Run.ckP .two) d
    (fun u => elOf d.entry d.kind ((_root_.Run.bsRound .two d.entry d.kind).φ u))
    (_root_.Run.bsRound .two d.entry d.kind).w (blocks_el _ _ h1 hlog)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind
        ((_root_.Run.bsRound .two d.entry d.kind).φ a)).elems = _
      rw [shows_chi _ _ h1]
      rfl) z s hr
  exact k.trans (blocks_bound _ _ h1 hlog _)

end

end P1K8

#print axioms P1K8.exAll_one
#print axioms P1K8.blocks_el
#print axioms P1K8.ratio_div
#print axioms P1K8.blocks_bound
#print axioms P1K8.units_gate_blocks
