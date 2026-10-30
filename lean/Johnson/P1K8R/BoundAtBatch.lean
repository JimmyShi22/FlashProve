-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/BoundAtBatch.lean: THE SMALLNESS TEST: THE COUNT AND THE CHANCE OF
Johnson/P1K8R/FallAtStepAll.lean AND FallChanceAgree.lean WITH THE NUMBER d TIED TO THE PLAN: d :=
(THE ROWS OF THE BATCHING's DECLARED ROUND) - 1, UNDER ONE TEST WITH CODE ON THE PUBLIC PART.
Lemmas; none of the library's goals. No prover stands in them; nothing on completeness, soundness or
hiding. An assembly: no new argument.

IT STANDS ON THE LIBRARY's `rows_fit_layers`, `rows_fit_att`, `rows_fit_head`
(Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean): under `RowsAsked Z` (at each of the 25 segments the
test `rowsFitB`, Johnson/Desc/First/Link/K9RowsAsk.lean, accepts the built segment: the plan's
number of claims, the indices that the ties take and the indices that the reads take are together at
most the rows that the batching's declared round has), in the goals' scope, at every state reached
in front of a batching: (the number of claims that the ledger holds as the plan's) + (the indices of
the smallness test's equations) is at most p.rows, p the batching's numbers (IM.k9At Z l). EACH OF
THE THREE BEGINS: IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL 25 SEGMENTS (`RowsAsked Z`).
  **`bound_at_batch`**   that, at all 25 segments in one statement, in the letters of
      FallAtStepAll.lean
  **`fall_at_step_rows`**   `fall_at_step_all` without the letter d and its premise: at every state
      reached in front of the seated batching block at most nU[2] * (p.rows - 1) field elements x
      are such that the block's step says yes at some round that has drawn x in reduced words and
      `selfUnits` says no at the state that the step returns
  **`fall_chance_rows`**   `fall_chance_agree` without d and its premise on d: for every front that
      meets `Agree` and whose values are reached: the chance is at most nU[2] * (p.rows - 1) * w /
      (the number of round j's challenges)
Limits. `RowsAsked Z` IS A PREMISE: nothing here or in the files named gives it from the goals'
scope; that the test accepts at any public files is not shown. K9RowsAskLaw.lean is not reviewed.
p.rows and nU[2] are evaluated nowhere. For the rest those of FallAtStepAll.lean and
FallChanceAgree.lean: front is a letter; the law is named, not derived; one segment, one of the
tests behind the adding; no state is shown to be reached.

-/
import Johnson.P1K8R.FallChanceAgree
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.Desc.First.Batch.Law.ShutYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked rows_fit_layers rows_fit_att rows_fit_head)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The exponents are below the rows of the batching's declared round.** -/
theorem bound_at_batch (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ p : K9.Where, IM.k9At Z l = some p ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        ∀ tl F' funs, s.tl? = some tl → s.fork? = some F' → s.funs? = some funs →
          F'.planClaimsF + topOf tl funs ≤ p.rows := by
  have key : ∀ (K : ℕ), (∀ (z : ProofFile.InstPub) (s : S), Reach 0 c.blocksInOrder (ProofFile.startS Z) K (z, s) →
      ∃ G funs tl p, s.fork? = some G ∧ s.funs? = some funs ∧ s.tl? = some tl ∧
        IM.k9At Z l = some p ∧
        ∀ tl', LinkJoin.rowsRead tl' = LinkJoin.rowsRead tl →
          G.planClaimsF + K9L.top8 tl' funs ≤ p.rows) →
      ∀ p : K9.Where, IM.k9At Z l = some p → ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) K (z, s) →
        ∀ tl F' funs, s.tl? = some tl → s.fork? = some F' → s.funs? = some funs →
          F'.planClaimsF + topOf tl funs ≤ p.rows := by
    intro K H p hp z s hr tl F' funs h1 h2 h3
    obtain ⟨G, funs', tl', p', a1, a2, a3, a4, a5⟩ := H z s hr
    obtain rfl : G = F' := Option.some.inj (a1.symm.trans h2)
    obtain rfl : funs' = funs := Option.some.inj (a2.symm.trans h3)
    obtain rfl : tl' = tl := Option.some.inj (a3.symm.trans h1)
    obtain rfl : p' = p := Option.some.inj (a4.symm.trans hp)
    exact a5 tl' rfl
  obtain ⟨-, p, -, -, -, hp, -⟩ := (IM.k9_of hS hR O).2 l hl
  refine ⟨p, hp, ?_⟩
  by_cases h24 : l = 24
  · subst h24
    exact key 347 (fun z s hr => rows_fit_head hE hS hR O hr) p hp
  · rw [if_neg h24]
    by_cases he : l % 2 = 0
    · obtain ⟨g, hg, rfl⟩ : ∃ g, g < 12 ∧ l = 2 * g := ⟨l / 2, by omega, by omega⟩
      refine key _ (fun z s hr => rows_fit_layers hE hS hR O hg (z := z) ?_) p hp
      rwa [show 28 * g + 9 = 14 * (2 * g) + 9 by omega]
    · obtain ⟨g, hg, rfl⟩ : ∃ g, g < 12 ∧ l = 2 * g + 1 := ⟨l / 2, by omega, by omega⟩
      exact key _ (fun z s hr => rows_fit_att hE hS hR O hg hr) p hp

/-- **The count at the step, at all 25 segments, with the plan's number.** -/
theorem fall_at_step_rows (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (z : ProofFile.InstPub) (s : S),
        Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s) →
        Prob.cnt (fun x : Cb.Gl.E => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (k : Nat),
          r.drawn.elems = [Slice.ofE x] ∧ b.step 0 s [r] cols = .ok (t, k) ∧
            zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true) ≤
          (ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) := by
  obtain ⟨b, p, X, hb, hp, hX, hcount⟩ := fall_at_step_all hS hR O hl
  obtain ⟨p', hp', hbound⟩ := bound_at_batch hE hS hR O hl
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  refine ⟨b, p, X, hb, hp, hX, fun z s hr => hcount z s (p.rows - 1) hr ?_⟩
  intro tl F' funs h1 h2 h3
  have h := hbound z s hr tl F' funs h1 h2 h3
  omega

/-- **The chance, with the plan's number.** -/
theorem fall_chance_rows (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
        (_ : ∀ x, Prob.cnt (fun a => el a = x) ≤ w)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : Agree j front)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn.elems = [Slice.ofE (el (f j))] ∧ b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) * w : ℕ) : ℝ≥0∞) /
            Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_agree hS hR O hl
  obtain ⟨p', hp', hbound⟩ := bound_at_batch hE hS hR O hl
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j el w hw front hagree hreach
  refine hall j el w hw front hagree hreach (p.rows - 1) ?_
  intro f zs hz tl F' funs h1 h2 h3
  have h := hbound zs.1 zs.2 (hreach f zs hz) tl F' funs h1 h2 h3
  omega

end

end P1K8

#print axioms P1K8.bound_at_batch
#print axioms P1K8.fall_at_step_rows
#print axioms P1K8.fall_chance_rows
