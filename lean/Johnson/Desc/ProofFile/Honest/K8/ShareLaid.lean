-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/ShareLaid.lean: THE SMALLNESS TEST: ITS SHARE OF THE TESTS BEHIND
THE ADDING (`k8Share`, Johnson/Desc/ProofFile/Honest/K8/Share.lean) SAYS THE SAME IN FRONT OF THE
RUN "K8.lsTail" AND BEHIND IT. Lemmas on the verifier's own text and this library's definitions;
none of its goals.

  `share_at`   the share at a state, of the test's data and the ledger there
  **`share_slot`**   two states with one ledger, whose data of the test differ in the field lsTail
                   alone, have one share
  **`share_lsTail`**   AT THE RUN THAT THE KIND's BLOCK LISTS under "K8.lsTail": run s = .ok s' →
                   k8Share nU s' = k8Share nU s: by the library's `sits_lsTail`
                   (Johnson/Desc/First/TailClaims/K8Sits.lean): the run turns that one field and
                   nothing else of the data or the ledger
By `k8First_slot`, `k8Second_slot` (Johnson/Desc/ProofFile/Honest/K8/ShareSlot.lean).
Limits. PAST THAT ONE RUN ALONE: at a layers' segment another kind's run stands between it and
"K8.tests": what that run turns of the ledger is not looked at. Nothing on whether the share is
silent anywhere.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ShareSlot
import Johnson.Desc.First.TailClaims.K8Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP)
open VerifiableInference.Desc.First.TailClaims.Law (partOf sits_lsTail)

/-- The share at a state, of the test's data and the ledger there. -/
theorem share_at (nU : Array Nat) {s : S} {tl : HTailF2} {F : Fork} (ht : s.tl? = some tl)
    (hF : s.fork? = some F) : k8Share nU s = (k8First tl nU F).or (k8Second tl F) := by
  have e : tlForkP.get? s = some (tl, F) := by
    show ((s.tl?).bind fun p => (s.fork?).map fun q => (p, q)) = _
    rw [ht, hF]
    rfl
  unfold k8Share
  rw [e]
  rfl

/-- **One ledger, and data that differ in the field lsTail alone: one share.** -/
theorem share_slot (nU : Array Nat) {s z : S} {tl : HTailF2} {F : Fork} {x : Array E}
    (ht : s.tl? = some tl) (hF : s.fork? = some F) (hz : z.tl? = some { tl with lsTail := x })
    (hzF : z.fork? = some F) : k8Share nU z = k8Share nU s := by
  rw [share_at nU ht hF, share_at nU hz hzF, k8First_slot, k8Second_slot]

/-- **Across the run "K8.lsTail".** -/
theorem share_lsTail (nU : Array Nat) (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.lsTail", run) ∈ (K8.whole p).after) (s s' : S) (hy : run s = .ok s') :
    k8Share nU s' = k8Share nU s := by
  obtain ⟨q, hq, rfl⟩ := (sits_lsTail p run h s s').1 hy
  have hg : tlForkP.get? s = some (q.tl, q.F) := by
    unfold partOf k8PartP at hq
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨fs, -, rfl⟩ := Option.map_eq_some_iff.1 h2
    exact hx
  have hs : tlForkP.get? (k8PartP.set s
      { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } }) =
      some ({ q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB }, q.F) :=
    tlForkP_lawful.get_set s _ _ hg
  unfold k8Share
  rw [hg, hs]
  show (k8First _ nU q.F).or (k8Second _ q.F) = (k8First q.tl nU q.F).or (k8Second q.tl q.F)
  rw [k8First_slot, k8Second_slot]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.share_at
#print axioms ProofFile.Honest.K8.share_slot
#print axioms ProofFile.Honest.K8.share_lsTail
