-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PoweredRests.lean: THE SMALLNESS TEST: THE SENTENCE "THE TEST's DATA ARE
THERE, AND THEIR VECTORS OF POWERS ARE THE POWERS OF θ" (`PowAt θ`: the library's `Powered`,
OnBytes/Tie/Pv/Tail/EndClosed.lean, at the state's data) IS LAID BY AN ACCEPTING CALL OF THE RUN
"K8.equations" WHEREVER THE OPEN LEDGER's BATCHING ELEMENT IS θ, AND IS HANDED ON BY AN ACCEPTING
CALL OF EACH RUN THAT THE LIBRARY's `RunRests` NAMES (Johnson/Desc/First/Link/Law/RunRel.lean: its
eight fields on runs). With Johnson/Desc/K8/Honest/ThetaRests.lean: for the tests behind the adding,
which compare these vectors with the powers of the element of the ledger at which they are called.
Lemmas on the library's own text; none of its goals.

  `PowAt θ e`   ∃ tl, e.tl? = some tl ∧ Powered tl θ
  `tl_puts`, `tl_put`, `tl_wrote`, `tl_head`   what four writings leave of the state's data of the
                   test
  **`eq_lays`**   k8Run.2 n e = .ok (c, e₁) → HasFork (·.theta = θ) e → PowAt θ e₁: by
                   `powered_of_yes` (Johnson/Desc/K8/Honest/PoweredOfYes.lean)
  **`rests_pow`**   RunRests fun e e₁ => HasFork (·.theta = θ) e → PowAt θ e → PowAt θ e₁
Limits. THE RUNS THAT `RunRests` NAMES ALONE: a lookup's runs are not among them. NOTHING ON THE
ADDING OF THE CLAIMS, which stands between the gatherer's runs and the tests; nothing on the draw.
That the run "K8.equations" has been called in front of a given state is not said here: a fold over
a link's order is wanted for that.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ThetaRests
import Johnson.Desc.K8.Honest.PoweredOfYes
import Johnson.Desc.First.Link.Law.NumRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote blockAtC frontAtC_pays backAtC_pays)
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.LinkJoin (HasFork RunRests)

/-- The test's data are there, and their vectors of powers are the powers of θ. -/
def PowAt (θ : E) (e : S) : Prop := ∃ tl, e.tl? = some tl ∧ Powered tl θ

/-- Behind a laying of the data and then of a ledger the data are those laid. -/
theorem tl_puts (e : S) (t : HTailF2) (ht : e.tl? = some t) (tl : HTailF2) (G : Fork) :
    ((e.putTl tl).putFork G).tl? = some tl := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.putFork, S.tl?, ho]
    · simp [S.tl?, ho] at ht
  | _ => exact nomatch ht

/-- Behind a laying of the data the data are those laid. -/
theorem tl_put (e : S) (t : HTailF2) (ht : e.tl? = some t) (tl : HTailF2) :
    (e.putTl tl).tl? = some tl := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [S.putTl, S.tl?, ho]
    · simp [S.tl?, ho] at ht
  | _ => exact nomatch ht

/-- A run's writing of a ledger into a feed-forward link's own part leaves the data. -/
theorem tl_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) :
    e₁.tl? = e.tl? := by
  obtain ⟨h1, rfl⟩ := hw
  simp [S.tl?, h1]

/-- The like into the head's. -/
theorem tl_head {e : S} {a : First.HeadOwn} {G : Fork} (h1 : e.here = .head a) :
    ({ e with here := .head { a with F := G } } : S).tl? = e.tl? := by
  simp [S.tl?, h1]

/-- **The run "K8.equations" lays the sentence.** -/
theorem eq_lays (θ : E) (n : Nat) (e e₁ : S) (c : List Claim) (hr : k8Run.2 n e = .ok (c, e₁))
    (hθ : HasFork (fun G => G.theta = θ) e) : PowAt θ e₁ := by
  obtain ⟨F, tl, funs, tl', F1, hF, ht, -, he, rfl⟩ := k8Run_ok n e e₁ c hr
  obtain ⟨G, hG, rfl⟩ := hθ
  obtain rfl : G = F := Option.some.inj (hG.symm.trans hF)
  exact ⟨tl', tl_puts e tl ht tl' F1, powered_of_yes he⟩

/-- **Each run that `RunRests` names hands the sentence on.** -/
theorem rests_pow (θ : E) :
    RunRests fun e e₁ => HasFork (fun G => G.theta = θ) e → PowAt θ e → PowAt θ e₁ where
  refl _ _ h := h
  front p r h0 n e c e₁ hr _ h := by
    obtain ⟨a, _, G, _, hw, _, _, _⟩ := frontAtC_pays h0 hr
    obtain ⟨tl, ht, hP⟩ := h
    exact ⟨tl, (tl_wrote hw).trans ht, hP⟩
  back p r h0 n e c e₁ hr _ h := by
    obtain ⟨a, _, G, _, hw, _, _, _⟩ := backAtC_pays h0 hr
    obtain ⟨tl, ht, hP⟩ := h
    exact ⟨tl, (tl_wrote hw).trans ht, hP⟩
  free p r h0 e e₁ hr _ h := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    obtain ⟨tl, ht, hP⟩ := h
    exact ⟨tl, (tl_wrote hw).trans ht, hP⟩
  merge n e c e₁ hr _ h := by
    obtain ⟨a, wo, G, h1, _, rfl, _, _⟩ := claim_inv hr
    obtain ⟨tl, ht, hP⟩ := h
    exact ⟨tl, (tl_head h1).trans ht, hP⟩
  join h iU3 p n e c e₁ hr _ k := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    obtain ⟨tl, ht, hP⟩ := k
    exact ⟨tl, (tl_head h1).trans ht, hP⟩
  eq n e c e₁ hr hθ _ := eq_lays θ n e e₁ c hr hθ
  ls e e₁ hr _ h := by
    obtain ⟨G, tl, _, ht, rfl⟩ := k8LsTail_ok e e₁ hr
    obtain ⟨tl₀, ht₀, hP⟩ := h
    obtain rfl : tl₀ = tl := Option.some.inj (ht₀.symm.trans ht)
    exact ⟨_, tl_put e tl₀ ht _, ⟨hP.vp, hP.vt, hP.rowX, hP.loX, hP.eqFirst, hP.shape⟩⟩
  tests nU e e₁ hr _ h := by
    obtain ⟨G, tl, g, _, ht, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    obtain ⟨tl₀, ht₀, hP⟩ := h
    obtain rfl : tl₀ = tl := Option.some.inj (ht₀.symm.trans ht)
    exact ⟨tl₀, tl_puts e tl₀ ht tl₀ _, hP⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tl_puts
#print axioms VerifiableInference.Desc.First.K8.Honest.tl_put
#print axioms VerifiableInference.Desc.First.K8.Honest.tl_wrote
#print axioms VerifiableInference.Desc.First.K8.Honest.tl_head
#print axioms VerifiableInference.Desc.First.K8.Honest.eq_lays
#print axioms VerifiableInference.Desc.First.K8.Honest.rests_pow
