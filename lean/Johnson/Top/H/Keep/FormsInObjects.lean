-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsInObjects.lean: The kind "lookup" (K3): THE PUBLIC TEST formsIn
(Johnson/Desc/First/Batch/FormsIn.lean) AT THE LOOKUP's RUNS "objects"
AND "guests", AT A LINK's READERS: true at every state of the verifier at which something was heard
whose rows name no entry and filled slots alone. With it THE READER's WAY BACK: at such a state the
reader answers, and its answer is the forms g.rows and no late slot. Statements and proofs.

OBJECT: K9.readerOf, K9.readersOfLink, K9.formsIn; objectsRun, guestsRun.
Used by Johnson/Top/H/Keep/FormsInTObjects.lean, Johnson/Desc/Sound/MgAt/K3DigitsObjIn.lean,
  Johnson/Top/H/Keep/FormsObjectsLink.lean and 4 more.
LETTERS: states | H, l; b | pr; seat (with AtS2); own; s, a, g free; run: what the link states under
  the name: the bare run inside a wrapper; pass: what the wrapper's guard asks (RunOver,
  Johnson/Top/H/Keep/RunUnder.lean).
Compiled with the whole library.

Main names:
  objects_answers: readerOf states b "objects" s = some (g.rows.toList, no late slot).
  guests_answers: the like at "guests" without a guest: no form, no late slot.
  objects_formsIn, guests_formsIn: the test is true.

Limits. PREMISES THAT STAY: hfind: which run block pr states under the name, and that it says yes
wherever the bare run does and the guard passes · hpass | hsame: the guard passes where the state
is turned by putFork alone | not at all · hN: the rows name no entry and slots alone that are there
and filled (NamedAll: behind the block's yes: Johnson/Top/H/Keep/K3Named.lean's decide_named; at a
later ledger: NamedAll.later) · hS: the ledger has its sizes · hmask: the segment's mask row's
message has a seat among own: NOT THE LOOKUP's: a fact on the state's frame and book · hmerge: no
row names the slot of the merge's end value: NOT THE LOOKUP's. "guests" with guests: not here.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunUnder
import Johnson.Top.H.Keep.FormsObjects
import Johnson.Top.H.Keep.PadNamed
import Johnson.Top.H.Keep.K3Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf readersOfLink statesOfLink lateOf
  LinkHoles ownRow formsIn affIn slotIn lateOk lateAt maskSeat mergeOf segAt?)
open VerifiableInference.Desc.Sound (fork_of_segAt)
open _root_.Fo.Tp (NamedAll bare_ents)

/-- **The reader's way back, at "objects".** -/
theorem objects_answers {states : ℕ → List (RunOf S)} {b : ℕ} (seat : Seat S Claim)
    (hA : AtS2 seat) (pass : S → S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (states b).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun seat))
    {s : S} {F : Fork} {g : Heard} (hF : s.fork? = some F) (hg : seat.heard s = some g)
    (hb : ∀ f ∈ g.rows.toList, Bare f) :
    readerOf states b "objects" s = some { forms := g.rows.toList, late := [] } := by
  obtain ⟨nm, run, hf, hO⟩ := hfind
  have hr0 : objectsRun seat 0 s =
      .ok (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) := by
    unfold objectsRun
    rw [(hA.fork s).trans hF, hg]
    rfl
  have hr : run 0 s =
      .ok (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) :=
    hO 0 s _ hr0 (by
      show pass s (seat.mark s (F.paid g.owedObjects))
      rw [hA.mark]
      exact hpass _ _)
  have hG : (seat.mark s (F.paid g.owedObjects)).fork? = some (F.paid g.owedObjects) := by
    rw [hA.mark]
    exact fork_putFork s F _ hF
  have hall : ((g.rows.toList.map seat.claim).all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hm, rfl⟩ := List.mem_map.1 hc
    rw [hA.runs, hA.eqs, hA.form, bare_ents (hb f hm)]
    simp
  have hforms : (g.rows.toList.map seat.claim).map (·.form) = g.rows.toList := by
    rw [List.map_map]
    exact (List.map_congr_left fun a _ => hA.form a).trans (List.map_id _)
  unfold readerOf
  rw [hf]
  simp only [Option.bind, hr, hF, hG, hall, hforms, if_true]
  rw [lateOf_same F (F.paid g.owedObjects) rfl]

/-- The like at "guests" without a guest. -/
theorem guests_answers {states : ℕ → List (RunOf S)} {b : ℕ} (pass : S → S → Prop)
    (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (states b).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest S Claim))))
    {s : S} {F : Fork} (hF : s.fork? = some F) :
    readerOf states b "guests" s = some { forms := [], late := [] } := by
  obtain ⟨nm, run, hf, hO⟩ := hfind
  have hr : run 0 s = .ok ([], s) := hO 0 s ([], s) rfl (hsame s)
  unfold readerOf
  rw [hf]
  simp only [Option.bind, hr, hF, List.all_nil, List.map_nil, if_true, lateOf_same F F rfl]

section
variable (H : LinkHoles) (l : Link S Claim) (pr : ℕ) (own : List (ℕ × ℕ))

/-- A link's reader hands on what the run's reader answers. -/
theorem link_answers {name : String} {s : S} {R : Read}
    (hn : (name == "K8.equations") = false) (h : readerOf (statesOfLink l) pr name s = some R) :
    (readersOfLink H l).forms pr name s = some R := by
  show (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) pr name s with
        | some R => some R
        | Option.none => H.silent pr name s) = some R
  rw [hn, h]
  rfl

/-- **The public test at "objects".** -/
theorem objects_formsIn (seat : Seat S Claim) (hA : AtS2 seat) (pass : S → S → Prop)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun seat))
    {s : S} {a : Desc.K9.Part} {g : Heard} (ha : segAt? s = some a) (hg : seat.heard s = some g)
    (hN : NamedAll a.F g.rows) (hS : Sized a.F) (hmask : (maskSeat own a).isSome = true)
    (hmerge : ∀ f ∈ g.rows.toList, ∀ x ∈ f.slots.toList, mergeOf s ≠ some x.1) :
    formsIn (readersOfLink H l) own pr "objects" s = true := by
  have hR := link_answers H l pr (by decide)
    (objects_answers seat hA pass hpass hfind (fork_of_segAt ha) hg fun f hf => (hN f hf).1)
  unfold formsIn
  rw [ha, hR]
  show (lateOk [] a && g.rows.toList.all fun f => affIn own (mergeOf s) [] a f) = true
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨rfl, List.all_eq_true.2 fun f hf => ?_⟩
  unfold affIn
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

/-- **The public test at "guests" without a guest.** -/
theorem guests_formsIn (pass : S → S → Prop) (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest S Claim))))
    {s : S} {a : Desc.K9.Part} (ha : segAt? s = some a) :
    formsIn (readersOfLink H l) own pr "guests" s = true := by
  have hR := link_answers H l pr (by decide) (guests_answers pass hsame hfind (fork_of_segAt ha))
  unfold formsIn
  rw [ha, hR]
  rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_answers
#print axioms VerifiableInference.OnPublicFiles.guests_answers
#print axioms VerifiableInference.OnPublicFiles.objects_formsIn
#print axioms VerifiableInference.OnPublicFiles.guests_formsIn
