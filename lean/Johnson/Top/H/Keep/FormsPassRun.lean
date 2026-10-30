-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsPassRun.lean: The kind "lookup" (K3): THE PUBLIC TESTS formsIn ON THE RUNS
OF THE LOOKUP ON A LINK's CALLS PASS A K3Pass: THE THEOREMS OF
Johnson/Top/H/Keep/FormsPassOurs.lean AGAIN, WITH ONE PREMISE EXCHANGED: in the place of hs ("the
link's second hole is silent at the run, at the state in front") stands hr: THE RUN ITSELF ANSWERS
AT THE STATE IN FRONT: (readerOf (statesOfLink l) b name s).isSome = true. Statements and proofs:
joinings: each calls its elder at the letters with the second hole emptied.

WHY. By reading: at the output head's link the description fills the second hole with k6Silent
(Johnson/Desc/First/Batch/ReadersAt.lean: holesAt; Johnson/Desc/Kinds/Law/K6SilentCode.lean): "the
run itself, at the state with the tables laid", AT EVERY BLOCK AND NAME. From the head's own rounds
on it should answer wherever the run does: so hs should be false in front of the head's lookup on
the digits, and the elder theorems could not fire there. At the 24 links in front the hole is empty
and hs holds outright. readersOfLink asks the hole only where the run is silent: so hr does without
a word on the hole.

OBJECT: K9.readersOfLink H l at the names "objects", "guests", "planes", "join"; K9.formsIn.
Used by Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean, Johnson/Top/H/Keep/AttOwnSame.lean,
  Johnson/Desc/Sound/MgAt/K3DigitsFormsJoinAtt.lean and 5 more.
LETTERS: those of FormsPassOurs.lean.
Compiled with the whole library.

Main names:
  noSilent H: the letters H with the second hole emptied.
  forms_run: under hr a link's reader's answer IS the run's own reader's, whatever the holes.
  link_reader_r, link_fwd_r: the sisters of link_reader and link_fwd.
  formsIn_holes: under hr the test does not read the holes. hr_fwd: hr goes forward.
  pass_of_noSilent: THE TRANSFER.
  guests_ | objects_ | join_ | planes_formsIn_pass_r: THE ENDS (join and planes in the forward
    form).

Limits. hr IS A FACT ON THE STATE IN FRONT: NOT PAID HERE. hfind stays an equation of runs.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassOurs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat planesRun joinRun)
open VerifiableInference.Desc.K9 (Read readerOf readersOfLink statesOfLink LinkHoles formsIn)
open VerifiableInference.Reads.Pass (Fwd)

/-- The letters with the second hole emptied. -/
def noSilent (H : LinkHoles) : LinkHoles := ⟨H.small, fun _ _ _ => none⟩

/-- **Where the run itself answers, a link's reader's answer is the run's own reader's.** -/
theorem forms_run (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String} {s : S}
    (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true) :
    (readersOfLink H l).forms b name s = readerOf (statesOfLink l) b name s := by
  show (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = readerOf (statesOfLink l) b name s
  rw [hn]
  cases e : readerOf (statesOfLink l) b name s with
  | none =>
    rw [e] at hr
    exact nomatch hr
  | some R0 => rfl

theorem link_reader_r {H : LinkHoles} {l : Link S Claim} {b : ℕ} {name : String} {s : S}
    {R : Read} (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true)
    (h : (readersOfLink H l).forms b name s = some R) :
    readerOf (statesOfLink l) b name s = some R := by
  rw [forms_run H l b hn hr] at h
  exact h

/-- **Fwd at a link's readers, with no word on the holes.** -/
theorem link_fwd_r (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String} {s s' : S}
    (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true)
    (h : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r s s') :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  have h2 := reader_fwd h R (link_reader_r hn hr hR)
  rw [forms_run H l b hn (by rw [h2]; rfl)]
  exact h2

/-- Under hr the test does not read the holes. -/
theorem formsIn_holes (H H' : LinkHoles) (l : Link S Claim) (own : List (ℕ × ℕ)) (b : ℕ)
    {name : String} {s : S} (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true) :
    formsIn (readersOfLink H l) own b name s = formsIn (readersOfLink H' l) own b name s := by
  unfold formsIn
  rw [forms_run H l b hn hr, forms_run H' l b hn hr]

/-- hr goes forward. -/
theorem hr_fwd (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String} {s s' : S}
    (hn : (name == "K8.equations") = false)
    (hf : Fwd (readersOfLink (noSilent H) l) b name s s')
    (hr : (readerOf (statesOfLink l) b name s).isSome = true) :
    (readerOf (statesOfLink l) b name s').isSome = true := by
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hr
  have h1 : (readersOfLink (noSilent H) l).forms b name s = some R := by
    rw [forms_run (noSilent H) l b hn hr]
    exact hR
  rw [link_reader (H := noSilent H) hn rfl (hf R h1)]
  rfl

/-- **THE TRANSFER**: what passes at the letters with the second hole emptied passes at H. -/
theorem pass_of_noSilent (H : LinkHoles) (l : Link S Claim) (own : List (ℕ × ℕ)) (b : ℕ)
    {name : String} {s s' : S} (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true)
    (hf : Fwd (readersOfLink (noSilent H) l) b name s s')
    (hp : formsIn (readersOfLink (noSilent H) l) own b name s = true →
      formsIn (readersOfLink (noSilent H) l) own b name s' = true)
    (hin : formsIn (readersOfLink H l) own b name s = true) :
    formsIn (readersOfLink H l) own b name s' = true := by
  rw [formsIn_holes H (noSilent H) l own b hn hr] at hin
  rw [formsIn_holes H (noSilent H) l own b hn (hr_fwd H l b hn hf hr)]
  exact hp hin

section
variable (H : LinkHoles) (l : Link S Claim) (b : ℕ) (own : List (ℕ × ℕ)) (seat : Seat S Claim)
  (hA : AtS2 seat) {s s' : S} {F G : Fork} (P : K3Pass s s' F G)
  (hh : seat.heard s' = seat.heard s)

include P in
/-- **"guests" without a guest.** -/
theorem guests_formsIn_pass_r
    (hr : (readerOf (statesOfLink l) b "guests" s).isSome = true)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "guests") = some (nm, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest S Claim)))
    (hin : formsIn (readersOfLink H l) own b "guests" s = true) :
    formsIn (readersOfLink H l) own b "guests" s' = true :=
  pass_of_noSilent H l own b (by decide) hr (guests_fwd (noSilent H) l b P rfl hfind)
    (guests_formsIn_pass (noSilent H) l b own P rfl hfind) hin

include hA P hh

/-- **"objects".** -/
theorem objects_formsIn_pass_r
    (hr : (readerOf (statesOfLink l) b "objects" s).isSome = true)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun seat)
    (hin : formsIn (readersOfLink H l) own b "objects" s = true) :
    formsIn (readersOfLink H l) own b "objects" s' = true :=
  pass_of_noSilent H l own b (by decide) hr
    (objects_fwd (noSilent H) l b seat hA P hh rfl hfind)
    (objects_formsIn_pass (noSilent H) l b own seat hA P hh rfl hfind) hin

/-- **"join", in the forward form.** -/
theorem join_formsIn_pass_r (keys : S → Option (Array Aff))
    (hkeys : ∀ KF, keys s = some KF → keys s' = some KF)
    (hr : (readerOf (statesOfLink l) b "join" s).isSome = true)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys)
    (hin : formsIn (readersOfLink H l) own b "join" s = true) :
    formsIn (readersOfLink H l) own b "join" s' = true :=
  pass_of_noSilent H l own b (by decide) hr
    (join_fwd' (noSilent H) l b seat hA P hh keys hkeys rfl hfind)
    (join_formsIn_pass' (noSilent H) l b own seat hA P hh keys hkeys rfl hfind) hin

/-- **"planes", in the forward form.** -/
theorem planes_formsIn_pass_r (lm : ℕ) (readers : Desc.K3.Readers S)
    (hread : ∀ r, readers s = some r → readers s' = some r)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
    (hr : (readerOf (statesOfLink l) b "planes" s).isSome = true)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers)
    (hin : formsIn (readersOfLink H l) own b "planes" s = true) :
    formsIn (readersOfLink H l) own b "planes" s' = true :=
  pass_of_noSilent H l own b (by decide) hr
    (planes_fwd' (noSilent H) l b seat hA P hh lm readers hread hwin rfl hfind)
    (planes_formsIn_pass' (noSilent H) l b own seat hA P hh lm readers hread hwin rfl hfind) hin

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.forms_run
#print axioms VerifiableInference.OnPublicFiles.link_reader_r
#print axioms VerifiableInference.OnPublicFiles.link_fwd_r
#print axioms VerifiableInference.OnPublicFiles.formsIn_holes
#print axioms VerifiableInference.OnPublicFiles.hr_fwd
#print axioms VerifiableInference.OnPublicFiles.pass_of_noSilent
#print axioms VerifiableInference.OnPublicFiles.guests_formsIn_pass_r
#print axioms VerifiableInference.OnPublicFiles.objects_formsIn_pass_r
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass_r
#print axioms VerifiableInference.OnPublicFiles.planes_formsIn_pass_r
