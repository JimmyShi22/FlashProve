-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsInTObjects.lean: The kind "lookup" (K3): THE PUBLIC TEST formsInT
(Johnson/Desc/First/Batch/FormsIn.lean: the test of the sentence "formsT", in front of the
segment's second sending) AT THE LOOKUP's OWN RUNS "objects" AND "guests" (without a guest), at the
state behind the lookup's accept. Statements and proofs: the sisters, at formsInT, of
objects_formsIn and guests_formsIn (Johnson/Top/H/Keep/FormsInObjects.lean).

OBJECT: K9.formsInT at K9.readersOfLink H l.
Used by Johnson/Desc/Sound/MgAt/K3CallsObjInPc.lean and Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean.
LETTERS: H, l, pr, own, seat, pass, s, a, g free.
Compiled with the whole library.

Main names:
  objects_formsInT, guests_formsInT.

Limits. THE PREMISES OF objects_formsIn, TO THE LETTER: hA (the seat's ledger is the state's, its
mark is putFork) · pass, hpass, hfind (the link states a run "objects" that answers what objectsRun
answers) · ha, hg · hN (every kept row is bare, and names filled slots below the number of slots:
Johnson/Top/H/Keep/K3Named.lean gives it behind an accept) · hS · hmask (the mask row has a seat in
own) · hmerge (no kept row names the slot of the merge's end value). A kept row names no entry: so
the two tests part in nothing here.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsInObjects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles segAt? formsInT affInT slotIn
  lateOk maskSeat mergeOf)
open VerifiableInference.Desc.Sound (fork_of_segAt)
open _root_.Fo.Tp (NamedAll bare_ents)

section
variable (H : LinkHoles) (l : Link S Claim) (pr : ℕ) (own : List (ℕ × ℕ))

/-- **The public test of "formsT" at "objects".** -/
theorem objects_formsInT (seat : Seat S Claim) (hA : AtS2 seat) (pass : S → S → Prop)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun seat))
    {s : S} {a : Desc.K9.Part} {g : Heard} (ha : segAt? s = some a) (hg : seat.heard s = some g)
    (hN : NamedAll a.F g.rows) (hS : Sized a.F) (hmask : (maskSeat own a).isSome = true)
    (hmerge : ∀ f ∈ g.rows.toList, ∀ x ∈ f.slots.toList, mergeOf s ≠ some x.1) :
    formsInT (readersOfLink H l) own pr "objects" s = true := by
  have hR := link_answers H l pr (by decide)
    (objects_answers seat hA pass hpass hfind (fork_of_segAt ha) hg fun f hf => (hN f hf).1)
  unfold formsInT
  rw [ha, hR]
  show (lateOk [] a && g.rows.toList.all fun f => affInT own (mergeOf s) [] a f) = true
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨rfl, List.all_eq_true.2 fun f hf => ?_⟩
  unfold affInT
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, List.all_eq_true.2 fun x hx => ?_⟩
  · rw [bare_ents (hN f hf).1]
    rfl
  · obtain ⟨h1, h2⟩ := (hN f hf).2 x hx
    have h3 : a.F.gotF.getD x.1 false = true := h2
    have h4 : x.1 < a.F.vp.size := by rw [hS.1]; exact h1
    have h5 : x.1 < a.F.mf.size := by rw [hS.2.1]; exact h1
    have h6 : (mergeOf s != some x.1) = true := bne_iff_ne.2 (hmerge f hf x hx)
    unfold slotIn
    rw [decide_eq_true h1, hmask, h6, h3, decide_eq_true h4, decide_eq_true h5]
    simp

/-- **The public test of "formsT" at "guests" without a guest.** -/
theorem guests_formsInT (pass : S → S → Prop) (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest S Claim))))
    {s : S} {a : Desc.K9.Part} (ha : segAt? s = some a) :
    formsInT (readersOfLink H l) own pr "guests" s = true := by
  have hR := link_answers H l pr (by decide) (guests_answers pass hsame hfind (fork_of_segAt ha))
  unfold formsInT
  rw [ha, hR]
  rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_formsInT
#print axioms VerifiableInference.OnPublicFiles.guests_formsInT
