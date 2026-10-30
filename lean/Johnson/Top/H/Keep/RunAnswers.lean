-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/RunAnswers.lean: The kind "lookup" (K3): PAYERS OF hr, THE PREMISE OF
Johnson/Top/H/Keep/FormsPassRun.lean ("the run itself answers at the state in front"), AT THE RUNS
"objects" AND "guests": FROM THE LINK's READER's OWN ANSWER AT THAT STATE (which the public test
formsIn, true there, holds), AT THE HOLES THAT THE DESCRIPTION LAYS (K9.holesAt,
Johnson/Desc/First/Batch/ReadersAt.lean). Statements and proofs.

OBJECT: K9.readerOf; K9.readersOfLink; K9.holesAt; Kinds.Head.Law.k6Silent, withTables
  (Johnson/Desc/Kinds/Law/K6SilentCode.lean); objectsRun.
Used by Johnson/Desc/Sound/MgAt/K3DigitsFormsKept.lean, Johnson/P5J/K03RunAnswersHeadAt.lean and
  Johnson/Desc/Sound/MgAt/K3DigitsFormsPlanes.lean.
LETTERS: H, l, b, seat, s, R; X, mH, m; claim.
Compiled with the whole library.

Why. "objects" reads of the state the open ledger and what was heard at its seat, and nothing else.
The second hole's filling at the head's link is the run itself at the state WITH THE TABLES LAID:
that state has the same ledger and the same heard value. So where the hole answers at "objects",
the run answers at the state itself: the hole is never asked.

Main names:
  objects_hr: from hsil: "whatever the second hole answers at 'objects' is the run's own reader's
    answer at a state with the same ledger and the same heard value".
  withTables_same: laying the tables leaves S.fork? and S.lookHeard?. k6Silent_is: so k6Silent
    meets hsil.
  objects_hr_holesAt: THE END AT "objects": at K9.holesAt, at the calls' seat.
  formsIn_some: the test, where true, holds an answer of the reader.
  objects_hr_of_formsIn: THE SAME FROM THE PUBLIC TEST.
  objects_hr_of_bare, guests_hr: by objects_answers | guests_answers
    (Johnson/Top/H/Keep/FormsInObjects.lean), with hfind in the form RunOver.

Limits. "planes" and "join": nothing here: these runs read what the calling kind's readers answer,
and at the head's link these read the tables.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassRun
import Johnson.Desc.First.Batch.ReadersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls)
open VerifiableInference.Desc.K9 (Read RunOf readerOf readersOfLink statesOfLink LinkHoles formsIn
  holesAt segAt?)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent withTables)

/-- **"objects": the run itself answers wherever the link's reader does.** -/
theorem objects_hr (H : LinkHoles) (l : Link S Claim) (b : ℕ) (seat : Seat S Claim)
    (hA : AtS2 seat) {s : S}
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun seat)
    (hsil : ∀ R, H.silent b "objects" s = some R →
      ∃ t, readerOf (statesOfLink l) b "objects" t = some R ∧ t.fork? = s.fork? ∧
        seat.heard t = seat.heard s)
    {R : Read} (h : (readersOfLink H l).forms b "objects" s = some R) :
    (readerOf (statesOfLink l) b "objects" s).isSome = true := by
  cases e : readerOf (statesOfLink l) b "objects" s with
  | some R0 => rfl
  | none =>
    exfalso
    have h' : (if "objects" == "K8.equations" then H.small s
        else match readerOf (statesOfLink l) b "objects" s with
          | some R => some R
          | Option.none => H.silent b "objects" s) = some R := h
    rw [show ("objects" == "K8.equations") = false by decide] at h'
    simp only [e] at h'
    have h2 : H.silent b "objects" s = some R := h'
    obtain ⟨t, ht, hf, hh⟩ := hsil R h2
    obtain ⟨nm, run, cl, t', F, G, hfd, hr, hF, hG, htest, _⟩ := reader_test ht
    obtain rfl := hfind nm run hfd
    obtain ⟨F2, g, e1, e2, _⟩ := objects_cut seat hr
    obtain rfl : F = F2 := Option.some.inj (hF.symm.trans ((hA.fork t).symm.trans e1))
    have hrt : objectsRun seat 0 t =
        .ok (g.rows.toList.map seat.claim, seat.mark t (F.paid g.owedObjects)) := by
      unfold objectsRun
      rw [e1, e2]
      rfl
    have ecl : cl = g.rows.toList.map seat.claim :=
      congrArg Prod.fst (Except.ok.inj (hr.symm.trans hrt))
    have hFs : s.fork? = some F := hf.symm.trans hF
    have hrs : objectsRun seat 0 s = .ok (cl, seat.mark s (F.paid g.owedObjects)) := by
      rw [ecl]
      unfold objectsRun
      rw [(hA.fork s).trans hFs, hh.symm.trans e2]
      rfl
    have hGs : (seat.mark s (F.paid g.owedObjects)).fork? = some (F.paid g.owedObjects) := by
      rw [hA.mark]
      exact fork_putFork s F _ hFs
    have hmk := reader_make hfd hrs hFs hGs htest
    rw [e] at hmk
    exact nomatch hmk

/-- Laying the tables leaves the open ledger and what the lookup on the calls heard. -/
theorem withTables_same {P : Desc.K8.ReadsQuiet.PH} {s t : S} (h : withTables P s = some t) :
    t.fork? = s.fork? ∧ t.lookHeard? = s.lookHeard? := by
  unfold withTables at h
  cases hh : s.here with
  | head a =>
    simp only [hh] at h
    obtain ⟨tb, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨by simp [S.fork?, hh], by simp [S.lookHeard?, hh]⟩
  | between => simp [hh] at h
  | fin _ => simp [hh] at h
  | mem _ => simp [hh] at h
  | lay _ => simp [hh] at h
  | att _ => simp [hh] at h

/-- So the head's filling of the second hole answers as the run's own reader does, at a state with
the same ledger and the same heard value. -/
theorem k6Silent_is {P : Desc.K8.ReadsQuiet.PH} {states : ℕ → List (RunOf S)} {b : ℕ}
    {name : String} {s : S} {R : Read} (h : k6Silent P states b name s = some R) :
    ∃ t, readerOf states b name t = some R ∧ t.fork? = s.fork? ∧ t.lookHeard? = s.lookHeard? := by
  unfold k6Silent at h
  obtain ⟨t, ht, hR⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨t, hR, withTables_same ht⟩

/-- **THE END AT "objects"**: at the holes that the description lays, at the calls' seat. -/
theorem objects_hr_holesAt (X : Verify.Public) (mH m : ℕ) (l : Link S Claim) (b : ℕ)
    (claim : Aff → Claim) (hA : AtS2 (seatCalls claim)) {s : S}
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun (seatCalls claim))
    {R : Read} (h : (readersOfLink (holesAt X mH m l) l).forms b "objects" s = some R) :
    (readerOf (statesOfLink l) b "objects" s).isSome = true := by
  refine objects_hr (holesAt X mH m l) l b (seatCalls claim) hA hfind (fun R' hR' => ?_) h
  have h1 : (if m == mH then k6Silent (Desc.K9.phAt X m) (statesOfLink l)
      else fun _ _ _ => none) b "objects" s = some R' := hR'
  cases hm : m == mH with
  | true =>
    rw [hm] at h1
    exact k6Silent_is h1
  | false =>
    rw [hm] at h1
    exact nomatch h1

/-- The test, where true, holds an answer of the reader. -/
theorem formsIn_some {Rd : Desc.K9.Readers} {own : List (ℕ × ℕ)} {piece : ℕ} {run : String} {s : S}
    (h : formsIn Rd own piece run s = true) : ∃ R, Rd.forms piece run s = some R := by
  unfold formsIn at h
  cases hR : Rd.forms piece run s with
  | some R => exact ⟨R, rfl⟩
  | none =>
    cases ha : segAt? s with
    | none => simp [ha, hR] at h
    | some a => simp [ha, hR] at h

/-- **The same from the public test.** -/
theorem objects_hr_of_formsIn (X : Verify.Public) (mH m : ℕ) (l : Link S Claim) (b : ℕ)
    (own : List (ℕ × ℕ)) (claim : Aff → Claim) (hA : AtS2 (seatCalls claim)) {s : S}
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun (seatCalls claim))
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "objects" s = true) :
    (readerOf (statesOfLink l) b "objects" s).isSome = true := by
  obtain ⟨R, hR⟩ := formsIn_some hin
  exact objects_hr_holesAt X mH m l b claim hA hfind hR

/-- By the reader's way back, where the kept rows are bare. -/
theorem objects_hr_of_bare (l : Link S Claim) (b : ℕ) (seat : Seat S Claim) (hA : AtS2 seat)
    (pass : S → S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l b).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun seat))
    {s : S} {F : Fork} {g : Heard} (hF : s.fork? = some F) (hg : seat.heard s = some g)
    (hb : ∀ f ∈ g.rows.toList, Bare f) :
    (readerOf (statesOfLink l) b "objects" s).isSome = true := by
  rw [objects_answers seat hA pass hpass hfind hF hg hb]
  rfl

/-- "guests" without a guest answers wherever a ledger is open. -/
theorem guests_hr (l : Link S Claim) (b : ℕ) (pass : S → S → Prop) (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (statesOfLink l b).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest S Claim))))
    {s : S} {F : Fork} (hF : s.fork? = some F) :
    (readerOf (statesOfLink l) b "guests" s).isSome = true := by
  rw [guests_answers pass hsame hfind hF]
  rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_hr
#print axioms VerifiableInference.OnPublicFiles.withTables_same
#print axioms VerifiableInference.OnPublicFiles.k6Silent_is
#print axioms VerifiableInference.OnPublicFiles.objects_hr_holesAt
#print axioms VerifiableInference.OnPublicFiles.formsIn_some
#print axioms VerifiableInference.OnPublicFiles.objects_hr_of_formsIn
#print axioms VerifiableInference.OnPublicFiles.objects_hr_of_bare
#print axioms VerifiableInference.OnPublicFiles.guests_hr
