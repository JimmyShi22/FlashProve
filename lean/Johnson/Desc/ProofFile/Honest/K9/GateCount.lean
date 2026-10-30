-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GateCount.lean: K9's COUNT, AS A COUNT OF FIELD ELEMENTS AT ROUNDS THAT HAVE DRAWN
THEM IN REDUCED WORDS. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.
NO PROBABILITY IS IN THIS FILE, AND NO TYPED CHALLENGE.

K9's fall is laid at a member WITHOUT A ROUND (the frame's block behind the batching): its chance is the batching's
round's, through the state that the batching's step returns. Honest/K9/AtStep.lean counts the READINGS of the words
drawn in a round at which the seated block's step says yes and K9's test speaks behind (`StepFalls`). Here the same
count is said of the field elements x themselves, at rounds that have drawn x in reduced words (`Slice.ofE x`): the
form of part 1's `fall_at_reached_step` (Johnson/P1K8R/FallAtStep.lean).
  `read_ofE`        the reading of the element of words `Slice.ofE x` is x
  `GateSpeaks ft b s n k4 x`   at the state s in front and the field element x: the seated block's step says yes at
      SOME round that has drawn just `Slice.ofE x` (whatever it shows, whatever the sealed digest and the columns),
      and the quiet seat's test speaks at the state that the step returns
  `gate_sub`        where it speaks, x is counted in `StepFalls`
  **`gate_few`**, **`gate_few_seated`**   the counts of `free_at_step` (feed-forward, "good" as `GoodLayers`) and
      `free_at_step_seated` (any segment of which `SeatedFree` holds, "good" as `goodS`), said of `GateSpeaks`: at
      most n * (the state's ledger's plan's number of claims - 1) field elements x
No member; called by no line.
WHAT IS NOT CLAIMED. WHICH TYPED CHALLENGES OF THE LIBRARY's SPACES SHOW AS `Slice.ofE x`, AND HOW MANY SHOW ONE x:
the alphabet of that round is not the field (by a reader's look: a letter of the challenge kit; at one named kit three
residues; at another hash blocks through a sampler; with the entry's proof of work, bits more): so from this count to
a chance a law on the kit is owed. That a state is good. That n and the state's plan's number are the public
parameters'. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- What is shown in reduced words is read back. -/
theorem read_ofE (x : Cb.Gl.E) : Reading.gl.val (E.ofTriple (Slice.ofE x)) = x := by
  show Slice.toE (E.ofTriple (Slice.ofE x)).triple = x
  rw [E.triple_ofTriple, Slice.toE_ofE]

/-- At the state in front and a field element: some round that has drawn it in reduced words falls. -/
def GateSpeaks (ft : ℕ) (b : Block S Claim) (s : S) (n : ℕ) (k4 : Option ℕ) (x : Cb.Gl.E) : Prop :=
  ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : ℕ), r.drawn.elems = [Slice.ofE x] ∧
    b.step ft s [r] cols = .ok (t, k) ∧ (quietFallTest n k4 (fun _ => none) t []).isSome = true

theorem gate_sub (ft : ℕ) (b : Block S Claim) (s : S) (n : ℕ) (k4 : Option ℕ) (x : Cb.Gl.E)
    (h : GateSpeaks ft b s n k4 x) : StepFalls ft b s n k4 x := by
  obtain ⟨r, cols, t, k, hx, hy, hq⟩ := h
  exact ⟨r, cols, t, k, Slice.ofE x, hx, read_ofE x, hy, hq⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The count of field elements, at a feed-forward segment.** -/
theorem gate_few (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par),
      c.blocksInOrder[14 * l + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ l = some p4 ∧
      ∀ (s : S) (a₀ : LayOwn) (n : ℕ), s.here = .lay a₀ → GoodLayers p4 s a₀ n →
        ∀ (k4 : Option ℕ) (ft : ℕ), (k4 = none ∨ k4 = some n) →
          Prob.cnt (GateSpeaks ft b s n k4) ≤ n * (a₀.F.planClaimsF - 1) := by
  obtain ⟨b, p4, f9, hp4, h⟩ := free_at_step hS hR O l hl hsub
  exact ⟨b, p4, f9, hp4, fun s a₀ n hs good k4 ft hk =>
    (Prob.cnt_mono fun x hx => gate_sub ft b s n k4 x hx).trans (h s a₀ n hs good k4 ft hk)⟩

/-- **The count of field elements, at a segment of which `SeatedFree` holds.** -/
theorem gate_few_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (k : ℕ)
    (Lk : Link S Claim) (p : Desc.K9.Where) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere)
    (Sd : SeatedFree c Z l k Lk p w) (s : S) (a0 : Desc.K9.Part) (n : ℕ)
    (ha0 : Desc.K9.atS.get? s = some a0)
    (hg : goodS p (claimsInBy Lk.each Lk.hear Lk.order) s n) (ft : ℕ) :
    Prob.cnt (GateSpeaks ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n none) ≤
      n * (a0.F.planClaimsF - 1) :=
  (Prob.cnt_mono fun x hx => gate_sub ft _ s n none x hx).trans
    (free_at_step_seated hS hR O l hl k Lk p w Sd s a0 n ha0 hg ft)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.read_ofE
#print axioms ProofFile.Honest.K9.gate_sub
#print axioms ProofFile.Honest.K9.gate_few
#print axioms ProofFile.Honest.K9.gate_few_seated
#print axioms ProofFile.Honest.K9.GateSpeaks
