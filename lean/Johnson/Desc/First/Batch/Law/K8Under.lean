-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Under.lean
(kind K9's soundness lemma; the tie of three of its runs' laws to the text that a seat calls):
THEOREMS: THE SMALLNESS TEST's OWN BLOCK (Johnson/Desc/First/K8/Whole.lean: K8.whole
p, which its lot lays at the kind's places) STATES THREE RUNS UNDER THE DRIVER's NAMES, AND EACH YES
OF SUCH A RUN IS A YES, WITH THE SAME RETURN, OF THE RUN OF WHICH K9's LAW SPEAKS (texts written
anew in Law/K8Run.lean, K8Step.lean, K8Tests.lean).
  part_get, part_set   the kind's part of the record: what it reads, what its writing is.
  putFork_back  the ledger laid back as it was changes nothing.
  k8_equations_under   "K8.equations": looked up in (K8.whole p).claims: its yes is k8Run's.
  k8_lsTail_under      "K8.lsTail": looked up in (K8.whole p).after: its yes is k8LsTail's.
  k8_tests_under       "K8.tests": the like: its yes is k8Tests p.nU's.
ONE DIRECTION: the kind's own runs refuse besides where the link's list of tables is not laid.
So RunOk, QuietOk, the door's, the book's, the mark's and the number's duties, which are shown of
the law's three texts and start from a yes, pass to the block's own runs, and on to the same runs
behind a seat's guard.
Not claimed: that the block at the kind's place in a description is K8.whole at these numbers (the
kind's own row). Over Johnson/Desc/Block.lean alone, in its form with runs behind the batching.

-/
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S tlForkP tlP forkP)
open VerifiableInference.Desc.First.K8 (whole ParW atRecord)
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP equations testsP)

/-- What the kind's part reads of the record. -/
theorem part_get (s : S) (q : K8Part) (h : k8PartP.get? s = some q) :
    s.tl? = some q.tl ∧ s.fork? = some q.F ∧ s.funs? = some q.funs := by
  simp only [k8PartP, tlForkP, Part.pair, tlP, forkP] at h
  cases h1 : s.tl? <;> cases h2 : s.fork? <;> cases h3 : S.funs? s <;> simp_all
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- Its writing. -/
theorem part_set (s : S) (q : K8Part) : k8PartP.set s q = (s.putTl q.tl).putFork q.F := rfl

/-- The ledger laid back as it was. -/
theorem putFork_back (s : S) (tl : HTailF2) (G : Fork) (h : s.fork? = some G) :
    (s.putTl tl).putFork G = s.putTl tl := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl : x.F = G := Option.some.inj h
    rfl
  | att x =>
    obtain rfl : x.F = G := Option.some.inj h
    rfl
  | head x =>
    by_cases ho : x.opened = true
    · have e : x.F = G := by simpa [S.fork?, ho] using h
      subst e
      simp [S.putTl, S.putFork, ho]
    · simp [S.fork?, ho] at h
  | between => simp [S.fork?] at h
  | fin x => simp [S.fork?] at h
  | mem x => simp [S.fork?] at h

/-- A yes behind a map. -/
theorem map_ok {ε α β : Type} {g : α → β} {x : Except ε α} {y : β} (h : x.map g = .ok y) :
    ∃ z, x = .ok z ∧ g z = y := by
  cases x with
  | error e => cases h
  | ok z => exact ⟨z, rfl, Except.ok.inj h⟩

/-- A yes of a run at the part, lifted to the record. -/
theorem atRecord_ok {α : Type} (f : K8Part → Except String (α × K8Part)) (s : S) (y : α × S)
    (h : atRecord f s = .ok y) :
    ∃ q x, k8PartP.get? s = some q ∧ f q = .ok x ∧ y = (x.1, k8PartP.set s x.2) := by
  unfold atRecord at h
  cases hq : k8PartP.get? s with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    obtain ⟨x, hx, hy⟩ := map_ok h
    exact ⟨q, x, rfl, hx, hy.symm⟩

/-- **"K8.equations".** -/
theorem k8_equations_under (p : ParW) :
    ∃ r, (whole p).claims.lookup "K8.equations" = some r ∧
      ∀ n e c e₁, r n e = .ok (c, e₁) → k8Run.2 n e = .ok (c, e₁) := by
  refine ⟨_, rfl, fun n e c e₁ h => ?_⟩
  obtain ⟨q, x, hq, hx, hy⟩ := atRecord_ok _ e (c, e₁) h
  obtain ⟨h1, h2, h3⟩ := part_get e q hq
  obtain ⟨z, hz, rfl⟩ := map_ok hx
  simp only [k8Run, h1, h2, h3, K9.there, bind, Except.bind, pure, Except.pure, hz]
  rw [hy]
  rfl

/-- **"K8.lsTail".** -/
theorem k8_lsTail_under (p : ParW) :
    ∃ r, (whole p).after.lookup "K8.lsTail" = some r ∧
      ∀ e e₁, r e = .ok e₁ → k8LsTail e = .ok e₁ := by
  refine ⟨_, rfl, fun e e₁ h => ?_⟩
  obtain ⟨y, ha, rfl⟩ := map_ok h
  obtain ⟨q, x, hq, hx, rfl⟩ := atRecord_ok _ e y ha
  obtain ⟨h1, h2, _⟩ := part_get e q hq
  obtain ⟨q', hq', rfl⟩ := map_ok hx
  obtain rfl := Except.ok.inj hq'
  simp only [k8LsTail, h1, h2, K9.there, bind, Except.bind, pure, Except.pure]
  exact congrArg Except.ok (putFork_back e _ q.F h2).symm

/-- **"K8.tests".** -/
theorem k8_tests_under (p : ParW) :
    ∃ r, (whole p).after.lookup "K8.tests" = some r ∧
      ∀ e e₁, r e = .ok e₁ → k8Tests p.nU e = .ok e₁ := by
  refine ⟨_, rfl, fun e e₁ h => ?_⟩
  obtain ⟨y, ha, rfl⟩ := map_ok h
  obtain ⟨q, x, hq, hx, rfl⟩ := atRecord_ok _ e y ha
  obtain ⟨h1, h2, _⟩ := part_get e q hq
  obtain ⟨q', hq', rfl⟩ := map_ok hx
  obtain ⟨G, hG, rfl⟩ := map_ok hq'
  simp only [k8Tests, h1, h2, K9.there, bind, Except.bind, pure, Except.pure, hG]
  rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k8_equations_under
#print axioms VerifiableInference.Desc.K9L.k8_lsTail_under
#print axioms VerifiableInference.Desc.K9L.k8_tests_under
