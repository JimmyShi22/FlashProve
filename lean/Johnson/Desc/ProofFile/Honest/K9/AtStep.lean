-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/AtStep.lean: K9's COUNT AT THE SEATED BATCHING BLOCK's STEP. Lemmas ON THE VERIFIER's
TEXT; no prover is in this file, and no goal is stated.

A chain goes on by a block's step (`Block.step`, Johnson/Desc/Block.lean): a test on the rounds' shape, a test on the
columns, then the block's decision at the rounds without the sealed digest and at the columns in groups. The counts of
Honest/K9/AtSeat.lean and AtSeatAll.lean stand at the decision, at no column and at the round that `drawnOne` gives.
After part 1's `step_chi` (Johnson/P1K8R/FallAtStep.lean), over its `seated_reads`.
  `falls_of_seated_step`   a yes of the step of a block that seats K9's batching alone, at ONE round, whatever it shows,
      that has drawn the one element of words tr, with whatever columns and first tree's number; and the quiet seat's
      test speaks at the state that the step returns: then that element is counted (`FallsAt`, Honest/K9/QuietMore.lean)
  `seated_step_shape`   every yes of such a block's step is at ONE round that has drawn ONE element: so `StepFalls`
      leaves out no yes of the step
  `StepFalls ft b s n k4 z`   the set that is counted at the step (ft: the step's first tree's number: any): the field
      elements z that are the reading of the words drawn in some such round
  `step_few`        a bound on the readings of `FallsAt` is a bound on `StepFalls`
  **`free_at_step`**, **`free_at_step_seated`**   WHEREVER THE DESCRIPTION CAN BE OPENED IN THE GOALS' SCOPE: the
      counts of `free_at_seat` (feed-forward) and of `SeatedFree.few` (each of the 25 segments), said of `StepFalls`
      at the description's own block
One way alone (from the step to the decision): a bound from above asks no more. (Through Honest/K9/AtSeatAll.lean this
file stands over part 1's three files on the ledger's core as well.) `seated_step_shape` is called at a
member in Honest/K9/YesToy.lean (`shapeC`); `free_at_step` and `free_at_step_seated` are ends: no line calls them.
WHAT IS NOT CLAIMED. What Honest/K9/AtSeat.lean and AtSeatAll.lean do not claim, but for "the decision, not the step".
That the words drawn are below the prime: of the drawn elements the step's test on the rounds' shape asks their number
alone: two lists of words can have one reading: THE COUNT IS OF READINGS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtSeat
import Johnson.Desc.ProofFile.Honest.K9.AtSeatAll
import Johnson.P1K8R.FallAtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- From the seated block's step to the set that is counted. -/
theorem falls_of_seated_step {same : S → S → Bool} {b : Block S Claim} {p : Desc.K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (Desc.K9.batch Desc.K9.atS p g) name a) (hk : a.kind ≠ KindName.K7) (ft : ℕ)
    (s t : S) (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (k : ℕ) (tr : UInt64 × UInt64 × UInt64)
    (hx : r.drawn.elems = [tr]) (hy : b.step ft s [r] cols = .ok (t, k)) (n : ℕ) (k4 : Option ℕ)
    (hq : (quietFallTest n k4 (fun _ => none) t []).isSome = true) : FallsAt b s n k4 (E.ofTriple tr) := by
  have h4 := ((Sound.step_ok_iff ft b s t [r] cols k).1 hy).2.2.2
  exact ⟨t, P1K8.seated_reads hb hk s t (noDigest r) ⟨[], drawnOne (E.ofTriple tr)⟩ _ [] hx h4, hq⟩

/-- **Every yes of the seated block's step is at one round that has drawn one element.** -/
theorem seated_step_shape {same : S → S → Bool} {b : Block S Claim} {p : Desc.K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (Desc.K9.batch Desc.K9.atS p g) name a) (ft : ℕ) (s t : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (k : ℕ) (hy : b.step ft s rs cols = .ok (t, k)) :
    ∃ r tr, rs = [r] ∧ r.drawn.elems = [tr] := by
  have h1 := ((Sound.step_ok_iff ft b s t rs cols k).1 hy).1
  rw [IM.alone_rounds hb] at h1
  have hr : (Desc.K9.batch Desc.K9.atS p g).rounds = [{ entry := Desc.K9.entry p }] := rfl
  rw [hr] at h1
  match rs, h1 with
  | [], h1 => exact nomatch h1
  | _ :: _ :: _, h1 =>
    simp only [roundsFit, Bool.and_false] at h1
    exact nomatch h1
  | [r], h1 =>
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h1
    have hl : r.drawn.elems.length = 1 := h1.1.1.1.1.1.1.2
    match he : r.drawn.elems, hl with
    | [tr], _ => exact ⟨r, tr, rfl, he⟩

/-- The set that is counted at the step. -/
def StepFalls (ft : ℕ) (b : Block S Claim) (s : S) (n : ℕ) (k4 : Option ℕ) (z : Cb.Gl.E) : Prop :=
  ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : ℕ) (tr : UInt64 × UInt64 × UInt64),
    r.drawn.elems = [tr] ∧ Reading.gl.val (E.ofTriple tr) = z ∧ b.step ft s [r] cols = .ok (t, k) ∧
      (quietFallTest n k4 (fun _ => none) t []).isSome = true

/-- A bound on the readings of `FallsAt` is a bound on `StepFalls`. -/
theorem step_few {same : S → S → Bool} {b : Block S Claim} {p : Desc.K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (Desc.K9.batch Desc.K9.atS p g) name a) (hk : a.kind ≠ KindName.K7) (ft : ℕ)
    (s : S) (n : ℕ) (k4 : Option ℕ) (N : ℕ)
    (h : Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧ FallsAt b s n k4 x) ≤ N) :
    Prob.cnt (StepFalls ft b s n k4) ≤ N := by
  refine (Prob.cnt_mono fun z hz => ?_).trans h
  obtain ⟨r, cols, t, k, tr, hx, hv, hy, hq⟩ := hz
  exact ⟨E.ofTriple tr, hv, falls_of_seated_step hb hk ft s t r cols k tr hx hy n k4 hq⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The count at the step, at a feed-forward segment.** -/
theorem free_at_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (b : Block S Claim) (p4 : OnBytes.Desc.First.K4.Par),
      c.blocksInOrder[14 * l + 9]? = some b ∧ LPFK9.k4ParAt Z Bs.G₀ l = some p4 ∧
      ∀ (s : S) (a₀ : LayOwn) (n : ℕ), s.here = .lay a₀ → GoodLayers p4 s a₀ n →
        ∀ (k4 : Option ℕ) (ft : ℕ), (k4 = none ∨ k4 = some n) →
          Prob.cnt (StepFalls ft b s n k4) ≤ n * (a₀.F.planClaimsF - 1) := by
  obtain ⟨Lk, p, p4, X, w, e1, e2, hp4, -, -, f9, -, -, -, hfew, -⟩ := free_at_seat hS hR O l hl hsub
  obtain ⟨Lk', p', w', T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  exact ⟨_, p4, f9, hp4, fun s a₀ n hs good k4 ft hk =>
    step_few (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne ft s n k4 _ (hfew s a₀ n hs good k4 hk)⟩

/-- **The count at the step, at a segment of which `SeatedFree` holds.** -/
theorem free_at_step_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (k : ℕ)
    (Lk : Link S Claim) (p : Desc.K9.Where) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere)
    (Sd : SeatedFree c Z l k Lk p w) (s : S) (a0 : Desc.K9.Part) (n : ℕ)
    (ha0 : Desc.K9.atS.get? s = some a0)
    (hg : goodS p (claimsInBy Lk.each Lk.hear Lk.order) s n) (ft : ℕ) :
    Prob.cnt (StepFalls ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s n none) ≤
      n * (a0.F.planClaimsF - 1) := by
  obtain ⟨Lk', p', w', T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (Sd.link.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (Sd.numbers.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  exact step_few (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne ft s n none _
    (Sd.few s a0 n ha0 hg)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.falls_of_seated_step
#print axioms ProofFile.Honest.K9.seated_step_shape
#print axioms ProofFile.Honest.K9.step_few
#print axioms ProofFile.Honest.K9.free_at_step
#print axioms ProofFile.Honest.K9.free_at_step_seated
#print axioms ProofFile.Honest.K9.StepFalls
