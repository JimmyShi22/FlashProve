-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingReturns.lean: the sender's text in the job of the first
chain's closing proximity test returns, at every input's public instance that the closing's public
test passes, at every list of challenges and at every stretch of coins. So the job's rows are never
the zeros of a refusal at such an instance: whether they are is a question on the public instance
alone, not on a coin or on the witness.

  `carried_past`   past the end of the list no stretch is given
  `exists_carried`   any stretches, cut to a list of counts, are coins for that list
  `carryRows_eq`     the job's text, at those coins
  `carryRows_returns`  it returns at the lot's own closing

By what. `returnsLaw` (Honest/K2/Law/SegmentAlike.lean): the closing returns, at every input, list of
challenges and carried coins, just where `publicOk` says yes at the instance, at a place that passes
`closingOk`. `messageRows_returns` (Honest/K2/Law/Laid.lean), `messageDue_laid` (Honest/K2/Law/Counts.lean).

Hypotheses of `carryRows_returns`. hok: the public test at the place. hpub: the public test at the
instance. H: the carrying message's shape passes the shared sending's public test.

Limits.
- hpub reads the instance: whoever wants the text to return at a stand of a thread owes that the
  thread's valid inputs pass it.
- Nothing says what the rows are.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K2.Honest (mainRows zeroG)
open Johnson.Prover.Send (Rows)

variable {W₀ Rc Xi Tr : Type}

/-- Past the end of the list no stretch is given. -/
theorem carried_past : ∀ (l : List (String × Due)) (c : CsAll l) (n : ℕ), l[n]? = none →
    K2.Stretch.carried l c n = .error "a stretch is asked beyond the list"
  | [], _, _, _ => rfl
  | _ :: _, _, 0, h => by simp at h
  | _ :: l, c, n + 1, h => by
    simp only [K2.Stretch.carried]
    exact carried_past l c.2 n (by simpa using h)

/-- **Any stretches, cut to a list of counts, are coins for that list.** -/
theorem exists_carried : ∀ (l : List (String × Due)) (mem : ℕ → Stretch), ∃ ca : CsAll l,
    ∀ n x, l[n]? = some x → K2.Stretch.carried l ca n = .ok (asK2 x.2 (mem n))
  | [], _ => ⟨(), fun n x h => by simp at h⟩
  | d :: l, mem => by
    obtain ⟨ca, h⟩ := exists_carried l fun n => mem (n + 1)
    refine ⟨(⟨fun i => (mem 0).f i, fun i => (mem 0).e i⟩, ca), fun n x hx => ?_⟩
    cases n with
    | zero =>
      have e : d = x := by simpa using hx
      subst e
      rfl
    | succ n =>
      simp only [K2.Stretch.carried]
      exact h n x (by simpa using hx)

/-- **The job's text at those coins.** -/
theorem carryRows_eq (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn)
    (mem : ℕ → Stretch) (ca : CsAll p.carries)
    (hc : ∀ n x, p.carries[n]? = some x → K2.Stretch.carried p.carries ca n = .ok (asK2 x.2 (mem n))) :
    carryRows D readers closing p w heard mem =
      (closing p (D w.x) (readers w) heard (K2.Stretch.carried p.carries ca)).bind fun Wl =>
        K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none
          (mainRows p.sizes Wl (fun _ _ _ => zeroG) 0)
          (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem p.front.length)) := by
  unfold carryRows
  refine congrArg (fun a => Except.bind a _)
    (congrArg (closing p (D w.x) (readers w) heard) (funext fun n => ?_))
  cases hn : p.front[n]? with
  | none =>
    exact (carried_past p.carries ca n (by simp [K2.SwitchPlace.carries, hn])).symm
  | some x =>
    exact (hc n (carriedName x.1 x.2.1 ⟨p.place, 0⟩, x.2.2)
      (by simp [K2.SwitchPlace.carries, hn])).symm

/-- **The sender's text returns**, at the lot's own closing. -/
theorem carryRows_returns (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) (mem : ℕ → Stretch)
    (hok : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hpub : K2.publicOk D lay p (segs.take p.link) w.x = true)
    (H : K2.ShapeFits p.sizes.codes (shapeL p) none) :
    ∃ R, carryRows D readers (K2.lotClosingAt lay segs) p w heard mem = .ok R := by
  obtain ⟨ca, hc⟩ := exists_carried p.carries mem
  rw [carryRows_eq D readers _ p w heard mem ca hc]
  have e := K2.Law.returnsLaw D readers lay segs p hok w heard ca
  rw [hpub] at e
  cases hcl : K2.lotClosingAt lay segs p (D w.x) (readers w) heard
      (K2.Stretch.carried p.carries ca) with
  | error m =>
    rw [hcl] at e
    cases e
  | ok Wl =>
    exact K2.messageRows_returns K2.freshTable _ H (K2.messageDue_laid H)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carried_past
#print axioms ProofFile.Honest.K12.AtProof.exists_carried
#print axioms ProofFile.Honest.K12.AtProof.carryRows_eq
#print axioms ProofFile.Honest.K12.AtProof.carryRows_returns
