-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/CallerFenced.lean: the kind "lookup" (K3), for the batching kind's law (K9): THE
CALLER's CLAUSE OF Johnson/Top/H/Keep/RunsPlain.lean ("the worth of the caller's form, read at the
state of the run, in the world of any full later state, is a function of the fixed part and the
data") FROM THREE PLAINER SENTENCES, THE FIRST OF THEM FENCED AND READ OFF THE WHOLE FIXED PART.
Definitions, statements and proofs. A law file; no running text imports it.

KIN, AND WHY A TWIN. It follows, name for name, Johnson/Top/H/Keep/RunsWorth.lean
(CallerForms · refVal · caller_worth · planes_plainOk_of · join_plainOk_of). There the sentence
"read" binds EVERY state and sees φ alone: fOf i e = fQ i (φ e). Both callers' readers look at the
live ledger (the reads' array's number of columns; attention's points), and the closed φ of the
link's law is blind to the ledger: so that sentence cannot be met there (found
by Lean). Here: read : ∀ i q e, Fx9 φ Ok q e → fOf i e = fQ i q: only at a state that goes on from
q, and off ALL of q: φ's share AND the snapshot. The two others are CallerForms', at fQ i q.

  CallerFormsQ φ Ok Fu fOf fQ ent   the three · refValQ fQ ent i q y   the form's worth in the world
  that q's snapshot names · caller_worthQ   the caller's clause at bv q y i := refValQ fQ ent i q y
  (by worth_filled, Johnson/Desc/First/Link/Law/WorthAtS.lean) ·
  planes_plainOk_ofQ, join_plainOk_ofQ   RunsPlain.lean's two, with the clause so paid ·
  CallerForms.toQ   CallerForms gives the fenced one: SO THE FENCED ONE ASKS NO MORE. AT
  THE CLOSED φ AND THE TWO CALLERS' READERS ITS PREMISE CANNOT BE MET (see above): THERE IT IS A
  RULE FROM AN UNPAYABLE PREMISE: NOBODY MAY SPEND IT THERE.
Limits. The three sentences are shown of no reader here. Nothing on soundness.

-/
import Johnson.Top.H.Keep.RunsWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (worldAt Bound PlainOk Pub9 Fx9 O9)
open VerifiableInference.Desc.K4Values (refWorld)

variable {α ι : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)

/-- The three sentences on a family of the caller's forms; the first fenced. -/
structure CallerFormsQ (fOf : ι → S → Aff) (fQ : ι → α × Option Pub9 → Aff)
    (ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE) : Prop where
  read : ∀ i q e, Fx9 φ Ok q e → fOf i e = fQ i q
  filled : ∀ i q u, Ok q → q.2 = some u → ∀ x ∈ (fQ i q).slots.toList, Filled u.F x.1
  pinned : ∀ i q t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
    ∀ x ∈ (fQ i q).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx

/-- The form's worth in the world that q's snapshot names. -/
def refValQ (fQ : ι → α × Option Pub9 → Aff)
    (ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE) (i : ι) (q : α × Option Pub9)
    (y : Bound GE) : GE :=
  match q.2 with
  | some u => (fQ i q).value Reading.gl (refWorld Reading.gl u.F [] (ent q y) y)
  | none => 0

/-- **The caller's clause.** -/
theorem caller_worthQ {fOf : ι → S → Aff} {fQ : ι → α × Option Pub9 → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE} (H : CallerFormsQ φ Ok Fu fOf fQ ent)
    (i : ι) (q : α × Option Pub9) (e t : S) (b : Desc.K9.Part) (y : Bound GE)
    (he : Fx9 φ Ok q e) (ht : Fx9 φ Ok q t) (hfu : Fu t) (hb : atS.get? t = some b) :
    (fOf i e).value Reading.gl (worldAt Reading.gl b.L b.F y) = refValQ fQ ent i q y := by
  rw [H.read i q e he]
  obtain ⟨k0, _, u, _, hu, _, _⟩ := he
  unfold refValQ
  rw [hu]
  exact Desc.WorthAtS.worth_filled Reading.gl φ Ok q t b u ht hb hu (fQ i q) (ent q y) y
    (H.filled i q u k0 hu) (H.pinned i q t b y ht hfu hb)

/-- CallerForms gives the fenced one. Where it cannot be met (the closed φ, the two
callers' readers) this says nothing. -/
theorem CallerForms.toQ {fOf : ι → S → Aff} {fQ : ι → α → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE} (H : CallerForms φ Ok Fu fOf fQ ent) :
    CallerFormsQ φ Ok Fu fOf (fun i q => fQ i q.1) ent where
  read := fun i q e he => by rw [H.read i e, he.2.1]
  filled := H.filled
  pinned := H.pinned

section
variable (hd : α → Option Heard) (lm jLK : ℕ) (seat : Seat S Desc.Claim) (hA : AtS2 seat)
  (hs : SeatFits seat (·.form)) (hφp : ∀ s G, φ (s.putFork G) = φ s)
  (hφh : ∀ s, seat.heard s = hd (φ s)) (hOk : ∀ q, Ok q → K3Ok hd lm jLK q)
include hA hs hφp hφh hOk

/-- **"planes"**, with the caller's clause paid by the three sentences on its bit and pin forms. -/
theorem planes_plainOk_ofQ (readers : Readers S) {bQ : ℕ × ℕ → α × Option Pub9 → Aff}
    {pQ : ℕ → α × Option Pub9 → Aff} {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HB : CallerFormsQ φ Ok Fu (fun (i : ℕ × ℕ) e => bitOf readers e i.1 i.2) bQ ent)
    (HP : CallerFormsQ φ Ok Fu (fun (col : ℕ) e => pinOf readers e col) pQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (planesRun seat lm readers)
      (plVals hd lm jLK (fun q y k col => refValQ bQ ent (k, col) q y)
        (fun q y col => refValQ pQ ent col q y)) (pickLen hd lm jLK 3) :=
  planes_plainOk φ Ok Fu hd lm jLK seat hA hs hφp hφh hOk readers _ _
    (fun q e t b y he ht hfu hb k col => caller_worthQ φ Ok Fu HB (k, col) q e t b y he ht hfu hb)
    (fun q e t b y he ht hfu hb col => caller_worthQ φ Ok Fu HP col q e t b y he ht hfu hb)

/-- **"join"**, with the caller's clause paid by the three sentences on its key forms. -/
theorem join_plainOk_ofQ (keys : S → Option (Array Aff)) {kQ : ℕ → α × Option Pub9 → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HK : CallerFormsQ φ Ok Fu
      (fun (k : ℕ) e => (keysOf keys e).getD k (Aff.ofConst zeroE)) kQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (joinRun seat keys)
      (jnVals hd lm jLK fun q y k => refValQ kQ ent k q y) (pickLen hd lm jLK 1) :=
  join_plainOk φ Ok Fu hd lm jLK seat hA hs hφp hφh hOk keys _
    (fun q e t b y he ht hfu hb k => caller_worthQ φ Ok Fu HK k q e t b y he ht hfu hb)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.caller_worthQ
#print axioms VerifiableInference.OnPublicFiles.CallerForms.toQ
#print axioms VerifiableInference.OnPublicFiles.planes_plainOk_ofQ
#print axioms VerifiableInference.OnPublicFiles.join_plainOk_ofQ
