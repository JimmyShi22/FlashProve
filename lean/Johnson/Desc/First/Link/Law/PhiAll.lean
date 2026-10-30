-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PhiAll.lean: ONE CLOSED φ FOR THE PAYERS AT THE RUNS: WHAT OF THE
CARRIED RECORD IS FIXED BEFORE THE BATCHING's DRAW, BESIDE THE SNAPSHOT OF THE BATCHING's OWN PART.
A definition, its projections, and the kinds' premises on φ, proved TOGETHER.

Why. The batching kind's law at the carried record (Johnson/Desc/First/Batch/Law/FitsAtS.lean) has a
letter φ : S → α, which all kinds share.
Each payer at a run asks two things of it: hπ: a projection π reads out of φ what that kind has
heard; hkeep: the run's writing leaves φ as it is.
The batching's own law asks hφ: φ does not see what the batching's lens writes.

What is said.
  `Phi β`: a record: the layers' own heard record; what the head's merge has left; the smallness
    test's record with its written fields blanked; the tables' functions; and a field of a free type
    β for what further kinds have heard. `phiAll u ψ`: **the closed φ**, over a letter ψ : S → β for
    that field.
  `Rests u ψ`: the five laws that ψ owes: it does not see a writing of the ledger; of what the
    batching's lens writes; of the smallness test's record WHERE THE BLANKED RECORDS AGREE (so ψ may
    read what the digits' lookup has left in that record); of a run of the layers'; of the merge's
    run. `rests_unit`: the ψ that reads nothing has them.
  PROVED OF `phiAll u ψ`, for every ψ that rests: `phi_set` (the batching's hφ) · `phi_k8_pi`,
    `phi_k8_keep`, `phi_k8_keepT` (the smallness test's run and its run behind the batching) ·
    `phi_k4_pi`, `phi_k4_keep` (the layers' two runs) · `phi_k11_pi`, `phi_k11_keep` (the merge's
    run).

Limits. φ ALONE. The letters Ok and Fu, and the premises on them (hOk, hFu), are not touched:
whether they can be met together with this φ is open. The lookups' and their callers' premises are
not here: they are to come in by ψ. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K4Run
import Johnson.Desc.First.Link.Law.K11Run
import Johnson.Desc.First.Batch.Law.K8Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S LayOwn HeadOwn)
open VerifiableInference.Desc.First.TailClaims.Law (blank)

/-- **What is fixed before the draw, beside the batching's own snapshot.** -/
structure Phi (β : Type) where
  /-- what a layers' link's own rounds returned -/
  own : Option Own
  /-- what the head's merge has left -/
  wo : Option WsForkOut
  /-- the smallness test's record, its written fields blanked -/
  tl : Option HTailF2
  /-- the tables' functions -/
  funs : Option (Array HFun)
  /-- what further kinds have heard -/
  more : β

/-- The layers' own heard record, off the carried record. -/
def ownOf (s : S) : Option Own :=
  match s.here with
  | .lay a => a.own
  | _ => none

/-- What the head's merge has left, off the carried record. -/
def woOf (s : S) : Option WsForkOut :=
  match s.here with
  | .head a => a.wo
  | _ => none

variable {β : Type}

/-- **THE CLOSED φ.** u: the record at whose values the written fields are blanked. -/
def phiAll (u : HTailF2) (ψ : S → β) (s : S) : Phi β :=
  ⟨ownOf s, woOf s, s.tl?.map (blank u), s.funs?, ψ s⟩

/-- What the further letter owes: it rests under the writings behind the draw. -/
structure Rests (u : HTailF2) (ψ : S → β) : Prop where
  fork : ∀ s F, ψ (s.putFork F) = ψ s
  set : ∀ s a, ψ (atS.set s a) = ψ s
  /-- asked only of a writing that keeps the record but for its fourteen written fields: so ψ may
  read what the digits' lookup has left in that record -/
  tl : ∀ s tl tl', s.tl? = some tl → blank u tl' = blank u tl → ψ (s.putTl tl') = ψ s
  wrote : ∀ s a G s', Wrote s a G s' → ψ s' = ψ s
  head : ∀ (s : S) (a : HeadOwn) (G : Fork), s.here = .head a →
    ψ { s with here := .head { a with F := G } } = ψ s

theorem rests_unit (u : HTailF2) : Rests u fun _ : S => () :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

variable (u : HTailF2) (ψ : S → β)

/-- A writing of the ledger leaves φ. -/
theorem phi_putFork (hψ : Rests u ψ) (s : S) (F : Fork) :
    phiAll u ψ (s.putFork F) = phiAll u ψ s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  have e := hψ.fork ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ F
  cases here with
  | head x =>
    by_cases ho : x.opened = true <;>
      simp_all [phiAll, ownOf, woOf, S.putFork, S.tl?, S.funs?]
  | _ => simp_all [phiAll, ownOf, woOf, S.putFork, S.tl?, S.funs?]

/-- The four readers of φ do not see what the batching's lens writes. -/
theorem four_set (s : S) (a : K9.Part) :
    (ownOf (atS.set s a), woOf (atS.set s a), (atS.set s a).tl?, (atS.set s a).funs?) =
      (ownOf s, woOf s, s.tl?, s.funs?) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true <;>
      simp [atS, S.putLink, S.putFork, ownOf, woOf, S.tl?, S.funs?, ho]
  | _ => rfl

/-- **The batching's hφ**: φ does not see what the batching's lens writes. -/
theorem phi_set (hψ : Rests u ψ) (s : S) (a : K9.Part) :
    phiAll u ψ (atS.set s a) = phiAll u ψ s := by
  have h := four_set s a
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold phiAll
  rw [h1, h2, h3, h4, hψ.set]

/-- A writing of the smallness test's record leaves φ, where the blanked records agree. -/
theorem phi_k8_keepT (hψ : Rests u ψ) (s : S) (tl tl' : HTailF2) (h : s.tl? = some tl)
    (hb : blank u tl' = blank u tl) : phiAll u ψ (s.putTl tl') = phiAll u ψ s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  have e := hψ.tl ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ tl tl' h hb
  cases here with
  | head x =>
    by_cases ho : x.opened = true <;>
      simp_all [phiAll, ownOf, woOf, S.putTl, S.tl?, S.funs?]
  | _ => simp_all [phiAll, ownOf, woOf, S.putTl, S.tl?, S.funs?]

/-- The smallness test's hπ. -/
theorem phi_k8_pi (s : S) :
    (fun x : Phi β => (x.tl, x.funs)) (phiAll u ψ s) = (s.tl?.map (blank u), s.funs?) := rfl

/-- The smallness test's hkeep. -/
theorem phi_k8_keep (hψ : Rests u ψ) (s : S) (tl tl' : HTailF2) (F1 : Fork) (h : s.tl? = some tl)
    (hb : blank u tl' = blank u tl) : phiAll u ψ ((s.putTl tl').putFork F1) = phiAll u ψ s := by
  rw [phi_putFork u ψ hψ, phi_k8_keepT u ψ hψ s tl tl' h hb]

/-- The layers' hπ. -/
theorem phi_k4_pi (s : S) (a : LayOwn) (h : s.here = .lay a) : (phiAll u ψ s).own = a.own := by
  show ownOf s = _
  unfold ownOf
  rw [h]

/-- The layers' hkeep. -/
theorem phi_k4_keep (hψ : Rests u ψ) (s : S) (a : LayOwn) (G : Fork) (s' : S)
    (h : Wrote s a G s') : phiAll u ψ s' = phiAll u ψ s := by
  have e := hψ.wrote s a G s' h
  obtain ⟨h1, rfl⟩ := h
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .lay a := h1
  simp_all [phiAll, ownOf, woOf, S.tl?, S.funs?]

/-- The merge's hπ. -/
theorem phi_k11_pi (s : S) (a : HeadOwn) (h : s.here = .head a) : (phiAll u ψ s).wo = a.wo := by
  show woOf s = _
  unfold woOf
  rw [h]

/-- The merge's hkeep. -/
theorem phi_k11_keep (hψ : Rests u ψ) (s : S) (a : HeadOwn) (G : Fork) (h : s.here = .head a) :
    phiAll u ψ { s with here := .head { a with F := G } } = phiAll u ψ s := by
  have e := hψ.head s a G h
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .head a := h
  simp_all [phiAll, ownOf, woOf, S.tl?, S.funs?]

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.rests_unit
#print axioms VerifiableInference.Desc.PhiAll.phi_putFork
#print axioms VerifiableInference.Desc.PhiAll.four_set
#print axioms VerifiableInference.Desc.PhiAll.phi_set
#print axioms VerifiableInference.Desc.PhiAll.phi_k8_keepT
#print axioms VerifiableInference.Desc.PhiAll.phi_k8_pi
#print axioms VerifiableInference.Desc.PhiAll.phi_k8_keep
#print axioms VerifiableInference.Desc.PhiAll.phi_k4_pi
#print axioms VerifiableInference.Desc.PhiAll.phi_k4_keep
#print axioms VerifiableInference.Desc.PhiAll.phi_k11_pi
#print axioms VerifiableInference.Desc.PhiAll.phi_k11_keep
