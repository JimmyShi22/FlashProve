-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/RunUnder.lean: The kind "lookup" (K3): WHERE A LINK STATES A RUN OF CLAIMS
INSIDE A WRAPPER (a guard behind the run that can only refuse): what a link's reader answers is
still the bare run's answer. Definitions, statements and proofs.

OBJECT: K9.readersOfLink; objectsRun; any run r of the lookup's.
USER: Johnson/Top/H/Keep/FormsInObjects.lean (RunOver). Meant besides: the calling kinds' rows on
  "planes" and "join" (ranAt_under).
LETTERS: run: what the link states; r: the bare run; pass: what the wrapper's guard asks of the
  verifier's state in front of and behind the run.
Compiled with the whole library.

Main names:
  RunUnder run r: every yes of run is a yes of r, with the same answer.
  RunOver pass run r: every yes of r whose two states pass the guard is a yes of run, with the same
    answer.
  objects_readUnder: Cut at run, RunUnder run (objectsRun seat): no late slot; the forms are g.rows.
  objects_readerU: the premise hRd of Johnson/Top/H/Keep/FormsObjects.lean at a link's readers.
  ranAt_under: Cut at run and RunUnder run r give K3RanAt AT THE BARE RUN r.

Limits. That a given wrapper has RunUnder and RunOver is its own files' to show. objects_readerU
still asks that the link's second hole is silent at "objects" (hs):
Johnson/Top/H/Keep/FormsObjectsLink.lean does without.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.ReaderIsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat)
open VerifiableInference.Desc.K9 (Read RunOf readersOfLink statesOfLink LinkHoles)

/-- Every yes of run is a yes of r, with the same answer. -/
def RunUnder (run r : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n t y, run n t = .ok y → r n t = .ok y

/-- Every yes of r whose two states pass the guard is a yes of run, with the same answer. -/
def RunOver (pass : S → S → Prop) (run r : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n t y, r n t = .ok y → pass t y.2 → run n t = .ok y

theorem runUnder_refl (r : ℕ → S → Except String (List Claim × S)) : RunUnder r r :=
  fun _ _ _ h => h

theorem runOver_refl (pass : S → S → Prop) (r : ℕ → S → Except String (List Claim × S)) :
    RunOver pass r r := fun _ _ _ h _ => h

/-- **At "objects", under a wrapper.** -/
theorem objects_readUnder {states : ℕ → List (RunOf S)} {b : ℕ} {s : S} {R : Read}
    {run : ℕ → S → Except String (List Claim × S)} {cl : List Claim} {s' : S} {F G : Fork}
    (seat : Seat S Claim) (hA : AtS2 seat) (C : Cut states b "objects" s R run cl s' F G)
    (hU : RunUnder run (objectsRun seat)) (g : Heard) (hg : seat.heard s = some g) :
    R.late = [] ∧ R.forms = g.rows.toList := by
  have hf : seat.fork s = some F := (hA.fork s).trans C.front
  have hr := hU _ _ _ C.ran
  unfold objectsRun at hr
  rw [hf, hg] at hr
  have e : (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) = (cl, s') :=
    Except.ok.inj hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hG : G = F.paid g.owedObjects := by
    have h1 := C.behind
    rw [hA.mark, fork_putFork s F _ C.front] at h1
    exact (Option.some.inj h1).symm
  refine ⟨by rw [C.late, hG]; exact lateOf_same _ _ rfl, ?_⟩
  rw [C.forms, List.map_map]
  refine (List.map_congr_left fun a _ => ?_).trans (List.map_id _)
  exact hA.form a

theorem objects_readerU (H : LinkHoles) (l : Link S Claim) (pr : ℕ) (seat : Seat S Claim)
    (hA : AtS2 seat) (hs : ∀ s, H.silent pr "objects" s = none)
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunUnder run (objectsRun seat)) :
    ∀ s R g, (readersOfLink H l).forms pr "objects" s = some R → seat.heard s = some g →
      R.late = [] ∧ ∀ f ∈ g.rows.toList, f ∈ R.forms := by
  intro s R g hR hg
  obtain ⟨run, cl, s', F, G, C⟩ := link_cut (by decide) (hs s) hR
  obtain ⟨nm, run0, h1, hU⟩ := hfind
  obtain ⟨nm', h2⟩ := C.found
  obtain rfl : run0 = run := congrArg Prod.snd (Option.some.inj (h1.symm.trans h2))
  obtain ⟨e1, e2⟩ := objects_readUnder seat hA C hU g hg
  exact ⟨e1, fun f hf => by rw [e2]; exact hf⟩

/-- **The reader's answer gives "the BARE run said yes at this state".** -/
theorem ranAt_under {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s : S} {R : Read}
    {run r : ℕ → S → Except String (List Claim × S)} {cl : List Claim} {s' : S} {F G : Fork}
    (C : Cut states b name s R run cl s' F G) (hU : RunUnder run r) (heard : S → Option Heard)
    (g : Heard) (F0 : Fork) (hg : heard s = some g) (hL : _root_.Fo.Later F0 F) (hS : Sized F) :
    K3RanAt (fun s : S => s.fork?) heard g F0 r s cl G :=
  ⟨hg, ⟨F, C.front, hL, hS⟩, ⟨0, s', hU _ _ _ C.ran, C.behind⟩⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_readUnder
#print axioms VerifiableInference.OnPublicFiles.objects_readerU
#print axioms VerifiableInference.OnPublicFiles.ranAt_under
