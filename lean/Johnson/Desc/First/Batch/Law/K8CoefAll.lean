-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8CoefAll.lean
(kind K9's soundness lemma; a debt of K8's files): THEOREMS: THE LAST RUN
BEHIND THE BATCHING LEAVES JUST THE LIBRARY's LEDGER coefAll tl g F
(OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean), tl the smallness test's record and F the ledger in front
of that run, g what the lookup heard.
  fork_put      the ledger read behind a writing of the record and the ledger is the ledger written.
  k8_tests_coefAll   a yes of the law's text k8Tests nU (Law/K8Tests.lean): the record behind is the
                record in front with coefAll tl g F laid, and that is the ledger read there.
  k8_whole_coefAll   the same of the run that the kind's own block K8.whole p states under the
                driver's name "K8.tests" (Law/K8Under.lean).
By k8Tests_ok and coefBody_all (First/TailClaims/CoefficientsAll.lean: the two texts
unfold to one term).
Not claimed: what F is (the ledger behind the adding and "K8.lsTail"); that "K8.tests" stands last
in a link's order behind the batching (the driver's table). From a yes alone.

-/
import Johnson.Desc.First.Batch.Law.K8Under
import Johnson.Desc.First.TailClaims.CoefficientsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (whole ParW)
open VerifiableInference.Desc.First.TailClaims.Law (coefBody_all)

/-- The ledger read behind a writing of the record and the ledger. -/
theorem fork_put (s : S) (tl : HTailF2) (F G : Fork) (h : s.fork? = some F) :
    ((s.putTl tl).putFork G).fork? = some G := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.putFork, S.fork?, ho]
    · simp [S.fork?, ho] at h
  | between => simp [S.fork?] at h
  | fin x => simp [S.fork?] at h
  | mem x => simp [S.fork?] at h

/-- **A yes of the law's text leaves coefAll.** -/
theorem k8_tests_coefAll (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    ∃ F tl g, e.fork? = some F ∧ e.tl? = some tl ∧ tl.heard = some g ∧
      e₁ = (e.putTl tl).putFork (Fo.coefAll tl g F) ∧ e₁.fork? = some (Fo.coefAll tl g F) := by
  obtain ⟨F, tl, g, h1, h2, h3, _, _, h6⟩ := k8Tests_ok nU e e₁ h
  rw [coefBody_all] at h6
  exact ⟨F, tl, g, h1, h2, h3, h6, by rw [h6]; exact fork_put e tl F _ h1⟩

/-- **So does a yes of the kind's own block's run of that name.** -/
theorem k8_whole_coefAll (p : ParW) :
    ∃ r, (whole p).after.lookup "K8.tests" = some r ∧ ∀ e e₁, r e = .ok e₁ →
      ∃ F tl g, e.fork? = some F ∧ e.tl? = some tl ∧ tl.heard = some g ∧
        e₁ = (e.putTl tl).putFork (Fo.coefAll tl g F) ∧
        e₁.fork? = some (Fo.coefAll tl g F) := by
  obtain ⟨r, hr, hu⟩ := k8_tests_under p
  exact ⟨r, hr, fun e e₁ h => k8_tests_coefAll p.nU e e₁ (hu e e₁ h)⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k8_tests_coefAll
#print axioms VerifiableInference.Desc.K9L.k8_whole_coefAll
