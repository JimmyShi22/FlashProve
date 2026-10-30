-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsPassOurs.lean: The kind "lookup" (K3): THE PUBLIC TEST formsIn AT THE
LOOKUP's OWN FOUR RUNS ("objects", "guests" without a guest, "planes", "join") PASSES A K3Pass
(Johnson/Top/H/Keep/FormsPassK3.lean): true in front, true behind; and the reader's way forward
(Fwd), with which k3_forms_back carries the sentence "forms" back. Statements: joinings of
Johnson/Top/H/Keep/FormsPassK3.lean, K3PassOf.lean, RunsSame.lean and LateLow.lean.

OBJECT: K9.formsIn at K9.readersOfLink H l.
Used by Johnson/Top/H/Keep/FormsPassRun.lean, Johnson/Desc/Sound/MgAt/K3DigitsFormsOurs.lean,
  Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean and others.
LETTERS: H, l, b, own; seat: the seat OF THE RUNS (not of the sub-protocol that is passed); s, s',
  F, G.
Compiled with the whole library.

Main names:
  guests_runSame. objects_fwd, guests_fwd, join_fwd, planes_fwd: Fwd.
  objects_formsIn_pass, guests_formsIn_pass, join_formsIn_pass, planes_formsIn_pass: THE ENDS.
  join_fwd', planes_fwd', join_formsIn_pass', planes_formsIn_pass': the same where
    the caller's keys | readers need only answer behind WHAT THEY ANSWERED in front; the unprimed
    ones are their corollaries.

Limits. PREMISES, EACH BY ITS RUN: hs (the link's second hole is silent at the run, at s) · hfind
(the run that the link states under the name is the lookup's run itself) · hh (what was heard at
the runs' seat is the same at both states) · hkeys | hread (THE CALLING KIND's: its keys | readers
answer the same at both states) · hwin (at "planes": the window of the sumcheck over the leaves is
free in F, ends at or below F.next, and F.next is at or below the number of slots).

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsSame
import Johnson.Top.H.Keep.LateLow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat planesRun joinRun)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles formsIn lateOf)
open VerifiableInference.Reads.Pass (Fwd)

/-- "guests" without a guest answers nothing, everywhere. -/
theorem guests_runSame {s s' : S} {F G : Fork} (P : K3Pass s s' F G) :
    RunSame (guestsRun ([] : List (Desc.First.Look.Guest S Claim))) s s' := by
  intro cl t F1 G1 hr hF1 hG1
  have e : (([] : List Claim), s) = (cl, t) := Except.ok.inj hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain rfl : F1 = G1 := Option.some.inj (hF1.symm.trans hG1)
  obtain rfl : F = F1 := Option.some.inj (P.front.symm.trans hF1)
  exact ⟨s', G, G, rfl, P.behind, P.behind, by rw [lateOf_same G G rfl, lateOf_same F F rfl],
    P.trees⟩

section
variable (H : LinkHoles) (l : Link S Claim) (b : ℕ) (own : List (ℕ × ℕ)) (seat : Seat S Claim)
  (hA : AtS2 seat) {s s' : S} {F G : Fork} (P : K3Pass s s' F G)
  (hh : seat.heard s' = seat.heard s)

include P in
theorem guests_fwd (hs : H.silent b "guests" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "guests") = some (nm, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest S Claim))) :
    Fwd (readersOfLink H l) b "guests" s s' :=
  link_fwd H l b (by decide) hs fun nm r hf => by
    rw [hfind nm r hf]
    exact guests_runSame P

include P in
/-- **"guests" without a guest.** -/
theorem guests_formsIn_pass (hs : H.silent b "guests" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "guests") = some (nm, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest S Claim)))
    (hin : formsIn (readersOfLink H l) own b "guests" s = true) :
    formsIn (readersOfLink H l) own b "guests" s' = true :=
  k3_formsIn_fwd P (readersOfLink H l) own b "guests" (guests_fwd H l b P hs hfind)
    (fun R hR x hx => by
      obtain ⟨nm, run, cl, t, F1, G1, hf, hr, hF1, hG1, _, rfl⟩ :=
        reader_test (link_reader (by decide) hs hR)
      rw [hfind nm run hf] at hr
      have e : (([] : List Claim), s) = (cl, t) := Except.ok.inj hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain rfl : F1 = G1 := Option.some.inj (hF1.symm.trans hG1)
      have hx' : x ∈ lateOf F1 F1 := hx
      rw [lateOf_same F1 F1 rfl] at hx'
      exact absurd hx' List.not_mem_nil) hin

include hA P hh

theorem objects_fwd (hs : H.silent b "objects" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun seat) : Fwd (readersOfLink H l) b "objects" s s' :=
  link_fwd H l b (by decide) hs fun nm r hf => by
    rw [hfind nm r hf]
    exact objects_same seat hA P hh

/-- **"objects".** -/
theorem objects_formsIn_pass (hs : H.silent b "objects" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun seat)
    (hin : formsIn (readersOfLink H l) own b "objects" s = true) :
    formsIn (readersOfLink H l) own b "objects" s' = true :=
  k3_formsIn_fwd P (readersOfLink H l) own b "objects" (objects_fwd H l b seat hA P hh hs hfind)
    (fun R hR x hx => by
      rw [objects_low H l b seat hA hs hfind hR] at hx
      exact absurd hx List.not_mem_nil) hin

theorem join_fwd' (keys : S → Option (Array Aff))
    (hkeys : ∀ KF, keys s = some KF → keys s' = some KF) (hs : H.silent b "join" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys) : Fwd (readersOfLink H l) b "join" s s' :=
  link_fwd H l b (by decide) hs fun nm r hf => by
    rw [hfind nm r hf]
    exact join_runSame' seat hA P hh keys hkeys

theorem join_fwd (keys : S → Option (Array Aff)) (hkeys : keys s' = keys s)
    (hs : H.silent b "join" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys) : Fwd (readersOfLink H l) b "join" s s' :=
  join_fwd' H l b seat hA P hh keys (fun _ h => hkeys.trans h) hs hfind

/-- **"join"**, where the caller's keys answer behind what they answered in front. -/
theorem join_formsIn_pass' (keys : S → Option (Array Aff))
    (hkeys : ∀ KF, keys s = some KF → keys s' = some KF) (hs : H.silent b "join" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys)
    (hin : formsIn (readersOfLink H l) own b "join" s = true) :
    formsIn (readersOfLink H l) own b "join" s' = true :=
  k3_formsIn_fwd P (readersOfLink H l) own b "join"
    (join_fwd' H l b seat hA P hh keys hkeys hs hfind)
    (fun R hR x hx => by
      rw [join_low H l b seat hA keys hs hfind hR] at hx
      exact absurd hx List.not_mem_nil) hin

/-- **"join".** -/
theorem join_formsIn_pass (keys : S → Option (Array Aff)) (hkeys : keys s' = keys s)
    (hs : H.silent b "join" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys)
    (hin : formsIn (readersOfLink H l) own b "join" s = true) :
    formsIn (readersOfLink H l) own b "join" s' = true :=
  join_formsIn_pass' H l b own seat hA P hh keys (fun _ h => hkeys.trans h) hs hfind hin

theorem planes_fwd' (lm : ℕ) (readers : Desc.K3.Readers S)
    (hread : ∀ r, readers s = some r → readers s' = some r)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
    (hs : H.silent b "planes" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers) : Fwd (readersOfLink H l) b "planes" s s' :=
  link_fwd H l b (by decide) hs fun nm r hf => by
    rw [hfind nm r hf]
    exact planes_runSame' seat hA P hh lm readers hread hwin

theorem planes_fwd (lm : ℕ) (readers : Desc.K3.Readers S) (hread : readers s' = readers s)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧ F.next ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
    (hs : H.silent b "planes" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers) : Fwd (readersOfLink H l) b "planes" s s' :=
  planes_fwd' H l b seat hA P hh lm readers (fun _ h => hread.trans h)
    (fun g hg => ⟨(hwin g hg).1, Nat.le_trans (hwin g hg).1 (hwin g hg).2.1, (hwin g hg).2.2⟩) hs
    hfind

/-- **"planes"**, where the caller's readers answer behind what they answered in front. -/
theorem planes_formsIn_pass' (lm : ℕ) (readers : Desc.K3.Readers S)
    (hread : ∀ r, readers s = some r → readers s' = some r)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
    (hs : H.silent b "planes" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers)
    (hin : formsIn (readersOfLink H l) own b "planes" s = true) :
    formsIn (readersOfLink H l) own b "planes" s' = true :=
  k3_formsIn_fwd P (readersOfLink H l) own b "planes"
    (planes_fwd' H l b seat hA P hh lm readers hread hwin hs hfind)
    (fun R hR => planes_low H l b seat hA lm readers hs hfind
      (fun F1 hF1 => by
        obtain rfl : F = F1 := Option.some.inj (P.front.symm.trans hF1)
        exact P.sizedF)
      (fun g hg => (hwin g hg).1) hR) hin

/-- **"planes".** -/
theorem planes_formsIn_pass (lm : ℕ) (readers : Desc.K3.Readers S)
    (hread : readers s' = readers s)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧ F.next ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
    (hs : H.silent b "planes" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers)
    (hin : formsIn (readersOfLink H l) own b "planes" s = true) :
    formsIn (readersOfLink H l) own b "planes" s' = true :=
  planes_formsIn_pass' H l b own seat hA P hh lm readers (fun _ h => hread.trans h)
    (fun g hg => ⟨(hwin g hg).1, Nat.le_trans (hwin g hg).1 (hwin g hg).2.1, (hwin g hg).2.2⟩) hs
    hfind hin

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.guests_formsIn_pass
#print axioms VerifiableInference.OnPublicFiles.objects_formsIn_pass
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass'
#print axioms VerifiableInference.OnPublicFiles.planes_formsIn_pass'
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass
#print axioms VerifiableInference.OnPublicFiles.planes_formsIn_pass
