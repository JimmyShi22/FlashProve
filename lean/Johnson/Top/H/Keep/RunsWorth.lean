-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsWorth.lean: The kind "lookup" (K3): THE CALLER's CLAUSE OF
Johnson/Top/H/Keep/RunsPlain.lean ("the worth of the caller's form, read at the record of the run,
in the world of any full later record, is a function of the fixed part and the data") FROM THREE
PLAINER SENTENCES ON THE CALLER's FORMS, by the tool worth_filled
(Johnson/Desc/First/Link/Law/WorthAtS.lean). Definitions, statements and proofs.

The three, of a family of forms fOf i e (i: an index; e: the record):
  read: the form is read off what was heard: fOf i e = fQ i (φ e).
  filled: every slot that fQ i q.1 names is filled in the snapshot's ledger, where Ok q.
  pinned: at every full state that goes on from q each entry of a virtual row that fQ i q.1 names
    is worth ent q y there.

Main names:
  CallerForms φ Ok Fu fOf fQ ent: the three.
  refVal fQ ent i q y: the form's worth in the world that q's snapshot names; 0 without a snapshot.
  caller_worth: the caller's clause, at bv q y i := refVal fQ ent i q y.
  planes_plainOk_of, join_plainOk_of: RunsPlain.lean's two, with the clause so paid.

Limits. The three sentences are the calling kinds'; shown of no reader here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsPlain
import Johnson.Desc.First.Link.Law.WorthAtS

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

/-- The three sentences on a family of the caller's forms. -/
structure CallerForms (fOf : ι → S → Aff) (fQ : ι → α → Aff)
    (ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE) : Prop where
  read : ∀ i e, fOf i e = fQ i (φ e)
  filled : ∀ i q u, Ok q → q.2 = some u → ∀ x ∈ (fQ i q.1).slots.toList, Filled u.F x.1
  pinned : ∀ i q t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
    ∀ x ∈ (fQ i q.1).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx

/-- The form's worth in the world that q's snapshot names. -/
def refVal (fQ : ι → α → Aff) (ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE) (i : ι)
    (q : α × Option Pub9) (y : Bound GE) : GE :=
  match q.2 with
  | some u => (fQ i q.1).value Reading.gl (refWorld Reading.gl u.F [] (ent q y) y)
  | none => 0

/-- **The caller's clause.** -/
theorem caller_worth {fOf : ι → S → Aff} {fQ : ι → α → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE} (H : CallerForms φ Ok Fu fOf fQ ent)
    (i : ι) (q : α × Option Pub9) (e t : S) (b : Desc.K9.Part) (y : Bound GE)
    (he : Fx9 φ Ok q e) (ht : Fx9 φ Ok q t) (hfu : Fu t) (hb : atS.get? t = some b) :
    (fOf i e).value Reading.gl (worldAt Reading.gl b.L b.F y) = refVal fQ ent i q y := by
  obtain ⟨k0, f1, u, _, hu, _, _⟩ := he
  rw [H.read i e, f1]
  unfold refVal
  rw [hu]
  exact Desc.WorthAtS.worth_filled Reading.gl φ Ok q t b u ht hb hu (fQ i q.1) (ent q y) y
    (H.filled i q u k0 hu) (H.pinned i q t b y ht hfu hb)

section
variable (hd : α → Option Heard) (lm jLK : ℕ) (seat : Seat S Desc.Claim) (hA : AtS2 seat)
  (hs : SeatFits seat (·.form)) (hφp : ∀ s G, φ (s.putFork G) = φ s)
  (hφh : ∀ s, seat.heard s = hd (φ s)) (hOk : ∀ q, Ok q → K3Ok hd lm jLK q)
include hA hs hφp hφh hOk

/-- **"planes"**, with the caller's clause paid by the three sentences on its bit and pin forms. -/
theorem planes_plainOk_of (readers : Readers S) {bQ : ℕ × ℕ → α → Aff} {pQ : ℕ → α → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HB : CallerForms φ Ok Fu (fun (i : ℕ × ℕ) e => bitOf readers e i.1 i.2) bQ ent)
    (HP : CallerForms φ Ok Fu (fun (col : ℕ) e => pinOf readers e col) pQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (planesRun seat lm readers)
      (plVals hd lm jLK (fun q y k col => refVal bQ ent (k, col) q y)
        (fun q y col => refVal pQ ent col q y)) (pickLen hd lm jLK 3) :=
  planes_plainOk φ Ok Fu hd lm jLK seat hA hs hφp hφh hOk readers _ _
    (fun q e t b y he ht hfu hb k col => caller_worth φ Ok Fu HB (k, col) q e t b y he ht hfu hb)
    (fun q e t b y he ht hfu hb col => caller_worth φ Ok Fu HP col q e t b y he ht hfu hb)

/-- **"join"**, with the caller's clause paid by the three sentences on its key forms. -/
theorem join_plainOk_of (keys : S → Option (Array Aff)) {kQ : ℕ → α → Aff}
    {ent : α × Option Pub9 → Bound GE → ℕ → ℕ → ℕ → GE}
    (HK : CallerForms φ Ok Fu
      (fun (k : ℕ) e => (keysOf keys e).getD k (Aff.ofConst zeroE)) kQ ent) :
    PlainOk Reading.gl atS (O9 (K := GE) φ Ok Fu) (Fx9 φ Ok) (joinRun seat keys)
      (jnVals hd lm jLK fun q y k => refVal kQ ent k q y) (pickLen hd lm jLK 1) :=
  join_plainOk φ Ok Fu hd lm jLK seat hA hs hφp hφh hOk keys _
    (fun q e t b y he ht hfu hb k => caller_worth φ Ok Fu HK k q e t b y he ht hfu hb)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.caller_worth
#print axioms VerifiableInference.OnPublicFiles.planes_plainOk_of
#print axioms VerifiableInference.OnPublicFiles.join_plainOk_of
