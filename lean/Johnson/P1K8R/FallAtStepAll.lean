-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallAtStepAll.lean: THE SMALLNESS TEST: THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean AT THE SEATED BATCHING BLOCK's STEP, AT ALL 25 SEGMENTS.
Lemmas; none of the library's goals. No prover stands in them; nothing on completeness, soundness or
hiding. An assembly: no new argument.

The like of Johnson/P1K8R/FallAtStep.lean (feed-forward segments). The letters are those of an
opening of the description (IM.Open).
  `step_count`   from the count at the decision to the count at the step, at a block that seats the
      batching block alone
  `fall_at_reached_step_att`, `fall_at_reached_step_head`   at an attention segment; at the head's
  **`fall_at_step_all`**   in the goals' scope, at every segment l < 25, k := 14 l + 9, or 347 at
      the head's: at every state s reached at number k of the flat list, for every d with (the
      number of claims that the ledger holds as the plan's) + (the indices of the smallness test's
      equations) ≤ d + 1 at whatever s holds: at most nU[2] * d field elements x are such that the
      block's step says yes at some round that has drawn x in reduced words and `selfUnits` says no
      at the state that the step returns
By: `step_chi` (FallAtStep.lean) · `fall_at_reached` (UnitsAtBatch.lean) · `fall_at_reached_att`,
`fall_at_reached_head` (UnitsAtBatchAll.lean).
Limits: those of FallAtStep.lean. That any state is reached there is not said. No number is
evaluated.

-/
import Johnson.P1K8R.FallAtStep
import Johnson.P1K8R.UnitsAtBatchAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-- From the count at the decision to the count at the step. -/
theorem step_count {same : S → S → Bool} {b : Block S Claim} {p : K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (K9.batch K9.atS p g) name a) (hk : a.kind ≠ KindName.K7)
    (nU : Array Nat) (s : S) (m : Nat)
    (h : Prob.cnt (fun x : Cb.Gl.E =>
      askBehind (fun t rs => b.decide t rs []) (zeroUnitAt nU) s [chiAt x] = true) ≤ m) :
    Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
        zeroUnitAt nU t = true) ≤ m := by
  refine (Prob.cnt_mono fun x hx => ?_).trans h
  obtain ⟨r, cols, t, k, hel, hst, hz⟩ := hx
  have hdec := step_chi hb hk 0 s t r cols k x hel hst
  unfold askBehind
  simp only [List.map_cons, List.map_nil]
  rw [hdec]
  exact hz

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The count at the step, at an attention segment. -/
theorem fall_at_reached_step_att (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (hsub : IM.subAt l = .attention) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + 9]? = some b ∧ IM.k9At Z l = some p ∧ Bs.G₀.built.toList[l]? = some X ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ≤ (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, hcount⟩ := fall_at_reached_att hS hR O hl hsub
  obtain ⟨Lk', p', w, T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  exact ⟨_, p, X, hflat, e2, hX, fun z s d hr hd =>
    step_count (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne _ s _ (hcount z s d hr hd)⟩

/-- The count at the step, at the head's segment. -/
theorem fall_at_reached_step_head (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[347]? = some b ∧ IM.k9At Z 24 = some p ∧ Bs.G₀.built.toList[24]? = some X ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat), Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ≤ (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  obtain ⟨Lk, p, X, e1, e2, hX, hflat, hcount⟩ := fall_at_reached_head hS hR O
  obtain ⟨Lk', p', w, T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  exact ⟨_, p, X, hflat, e2, hX, fun z s d hr hd =>
    step_count (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne _ s _ (hcount z s d hr hd)⟩

/-- **The count at the step, at all 25 segments.** -/
theorem fall_at_step_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (z : ProofFile.InstPub) (s : S) (d : Nat),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        (∀ tl F funs, s.tl? = some tl → s.fork? = some F → s.funs? = some funs →
          F.planClaimsF + topOf tl funs ≤ d + 1) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ≤ (ProofFile.k8NU Bs.G₀ X).getD 2 0 * d := by
  by_cases h24 : l = 24
  · subst h24
    exact fall_at_reached_step_head hS hR O
  · rw [if_neg h24]
    by_cases he : l % 2 = 0
    · exact fall_at_reached_step hS hR O hl (by unfold IM.subAt; rw [if_neg h24, if_pos he])
    · exact fall_at_reached_step_att hS hR O hl (by unfold IM.subAt; rw [if_neg h24, if_neg he])

end

end P1K8

#print axioms P1K8.step_count
#print axioms P1K8.fall_at_reached_step_att
#print axioms P1K8.fall_at_reached_step_head
#print axioms P1K8.fall_at_step_all
