-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/UnitsGate.lean: THE SMALLNESS TEST: THE COUNT OF Johnson/P1K8R/BoundAtBatch.lean AS A
BOUND ON THE LIBRARY's MEASURE OVER THE BATCHING's ONE ROUND's MESSAGES (Iop.prRho over Iop.Rho (uLT
C [d])), AT EVERY STATE REACHED IN FRONT OF THE BATCHING. Lemmas; none of the library's goals. No
prover stands in them; nothing on completeness, soundness or hiding. An assembly: no new argument.

EACH BEGINS: IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked Z`). C: a kit of
verifier's messages; d: the data of one round; el: the field element that a challenge of the kit at
d's entry and kind shows, in reduced words, at most w challenges to one element.
  **`units_gate`**   in the goals' scope, at every segment l < 25, at every state s reached at the
      batching's number K: the measure of the round's messages such that the seated batching block's
      step says yes from s, at some round that has drawn what the message shows, and `selfUnits`
      says no at the state that the step returns, is at most nU[2] * (p.rows - 1) * w / (the number
      of the kit's challenges)
  **`units_gate_typed`**   at the kit of typed challenges (Run.ck .two, Run/PlanDrawsQ.lean) and a
      round with the batching's entry K9.entry p: w = 1
By: `fall_at_step_rows` · `prRho_elem_le` (Johnson/Desc/K8/Honest/CountToRho.lean) · `shows_chi`,
`elOf_one`, `oneElem_bat` (ChiTyped.lean).
Limits. `RowsAsked Z` IS A PREMISE: nothing gives it from the goals' scope. ONE of the tests on the
ledger's weights behind the adding. The event is a sentence with "at some round and columns", no
test with code. The uniform law on one round's messages: that the messages of any run have it is not
said. No number is evaluated. No state is shown to be reached.

-/
import Johnson.P1K8R.BoundAtBatch
import Johnson.Desc.K8.Honest.CountToRho
import Run.PlanDrawsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The local bound at the batching's round.** -/
theorem units_gate (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (C : CK) (d : RDT) (el : C.Ch d.entry d.kind → Cb.Gl.E) (w : ℕ)
        (_ : ∀ y, Prob.cnt (fun a => el a = y) ≤ w)
        (_ : ∀ a, (C.dr d.entry d.kind a).elems = [Slice.ofE (el a)])
        (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Iop.prRho {ρ : Iop.Rho (uLT C [d]) | ∃ dr, drawnT C [d] ρ = [dr] ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
            b.step 0 s [r] cols = .ok (t, m) ∧ zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) /
            (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, hcount⟩ := fall_at_step_rows hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro C d el w hw hel z s hr
  refine prRho_elem_le C d el w hw hel _
    (fun x => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
        zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ?_ _ (hcount z s hr)
  rintro dr x ⟨r, cols, t, m, rfl, h1, h2⟩ hx
  exact ⟨r, cols, t, m, hx, h1, h2⟩

/-- **At typed challenges.** -/
theorem units_gate_typed (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          ∃ dr, drawnT (_root_.Run.ck .two) [d] ρ = [dr] ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat), r.drawn = dr ∧
            b.step 0 s [r] cols = .ok (t, m) ∧ zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
            (Nat.card (_root_.Run.Ch .two d.entry d.kind) : ℝ≥0∞) := by
  obtain ⟨b, p, X, hb, hp, hX, h⟩ := units_gate hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 z s hr
  have h1 : OneElem d.entry d.kind := by
    rw [he]
    exact oneElem_bat p d.kind h5 h6
  have k := h (_root_.Run.ck .two) d (elOf d.entry d.kind) 1 (elOf_one _ _ h1)
    (fun a => by
      show (_root_.Run.drawnOf .two d.entry d.kind a).elems = _
      rw [shows_chi _ _ h1]
      rfl) z s hr
  rwa [Nat.mul_one] at k

end

end P1K8

#print axioms P1K8.units_gate
#print axioms P1K8.units_gate_typed
