-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/ReaderIsRun.lean: WHAT A LINK's READER ANSWERS AT A RUN OF CLAIMS IS THAT RUN's
OWN ANSWER: general in the run's name: of K9.readerOf and K9.readersOfLink
(Johnson/Desc/First/Batch/ReaderOf.lean, ReadersOfLink.lean). And,
for the kind "lookup" (K3): at "objects" the reader gives just the forms g.rows and no late slot;
at any run the reader's answer gives "the run said yes at this record" (K3RanAt,
Johnson/Top/H/K3OutStatement.lean). Statements and proofs.

OBJECT: K9.readerOf, K9.readersOfLink; objectsRun (Johnson/Top/H/K3RunsLaw.lean).
USER: Johnson/Top/H/Keep/FormsObjects.lean's premise hRd. Meant besides: the like premise of the
  calling kinds' rows at "planes" and "join".
LETTERS: states | H, l; b, name, s free.
Compiled with the whole library.

Main names:
  Cut states b name s R: a run of that name is the first that block b states; it returns (cl, s') at
    0 and s; ledgers F and G are open at s and s'; R.forms are the claims' forms and R.late the
    slots that are free in F and filled in G.
  reader_cut: readerOf states b name s = some R gives Cut.
  link_cut: the like of readersOfLink, where the name is not the smallness test's and the link's
    second hole is silent at (b, name, s).
  lateOf_same: no late slot where the marks are the same.
  ranAt_of_cut: Cut, what was heard, and a ledger later than F0 with its sizes give K3RanAt.
  objects_readIs: at objectsRun of a seat that reads the record's own ledger, lays by putFork and
    makes plain claims: R.late = [] and R.forms = g.rows.toList.
  objects_reader: (P2) OF FormsObjects.lean, at readersOfLink.

Limits. From the reader's answer to the run, NOT BACK: that the reader answers at all (the run
returns; its claims are plain; their entries name own rows) is not shown. Which run block b states
under the name is a premise (hfind): at the seated block: theStated_two
(Johnson/Top/H/Keep/RunsStated.lean). That the second hole is silent at the lookups' runs is a
premise on that letter.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Top.H.Keep.RunsAtS
import Johnson.Top.H.K3OutStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf readersOfLink statesOfLink lateOf
  LinkHoles)

/-- What the reader's answer is made of. -/
structure Cut (states : ℕ → List (RunOf S)) (b : ℕ) (name : String) (s : S) (R : Read)
    (run : ℕ → S → Except String (List Claim × S)) (cl : List Claim) (s' : S) (F G : Fork) :
    Prop where
  found : ∃ nm, (states b).find? (fun r => r.1 == name) = some (nm, run)
  ran : run 0 s = .ok (cl, s')
  front : s.fork? = some F
  behind : s'.fork? = some G
  forms : R.forms = cl.map (·.form)
  late : R.late = lateOf F G

/-- **The reader is the run itself.** -/
theorem reader_cut {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s : S} {R : Read}
    (h : readerOf states b name s = some R) :
    ∃ run cl s' F G, Cut states b name s R run cl s' F G := by
  unfold readerOf at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨nm, run⟩ := r
  cases hz : run 0 s with
  | error e => simp [hz] at h
  | ok z =>
    cases hF : s.fork? with
    | none => simp [hz, hF] at h
    | some F =>
      simp only [hz, hF] at h
      obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain rfl := Option.some.inj h
        exact ⟨run, z.1, z.2, F, G, ⟨nm, hr⟩, hz, hF, hG, rfl, rfl⟩
      · exact nomatch h

/-- The like of a link's readers. -/
theorem link_cut {H : LinkHoles} {l : Link S Claim} {b : ℕ} {name : String} {s : S} {R : Read}
    (hn : (name == "K8.equations") = false) (hs : H.silent b name s = none)
    (h : (readersOfLink H l).forms b name s = some R) :
    ∃ run cl s' F G, Cut (statesOfLink l) b name s R run cl s' F G := by
  have h' : (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := h
  rw [hn] at h'
  cases hr : readerOf (statesOfLink l) b name s with
  | none =>
    simp only [hr] at h'
    have h2 : H.silent b name s = some R := h'
    rw [hs] at h2
    exact nomatch h2
  | some R0 =>
    simp only [hr] at h'
    have h2 : some R0 = some R := h'
    obtain rfl := Option.some.inj h2
    exact reader_cut hr

/-- No late slot where the marks are the same. -/
theorem lateOf_same (F G : Fork) (h : G.gotF = F.gotF) : lateOf F G = [] := by
  unfold lateOf
  rw [List.filterMap_eq_nil_iff]
  intro j _
  rw [h]
  cases F.gotF.getD j false <;> rfl

/-- **The reader's answer gives "the run said yes at this record".** -/
theorem ranAt_of_cut {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s : S} {R : Read}
    {run : ℕ → S → Except String (List Claim × S)} {cl : List Claim} {s' : S} {F G : Fork}
    (C : Cut states b name s R run cl s' F G) (heard : S → Option Heard) (g : Heard) (F0 : Fork)
    (hg : heard s = some g) (hL : _root_.Fo.Later F0 F) (hS : Sized F) :
    K3RanAt (fun s : S => s.fork?) heard g F0 run s cl G :=
  ⟨hg, ⟨F, C.front, hL, hS⟩, ⟨0, s', C.ran, C.behind⟩⟩

/-- **At "objects".** -/
theorem objects_readIs {states : ℕ → List (RunOf S)} {b : ℕ} {s : S} {R : Read}
    {cl : List Claim} {s' : S} {F G : Fork} (seat : Seat S Claim) (hA : AtS2 seat)
    (C : Cut states b "objects" s R (objectsRun seat) cl s' F G) (g : Heard)
    (hg : seat.heard s = some g) : R.late = [] ∧ R.forms = g.rows.toList := by
  have hf : seat.fork s = some F := (hA.fork s).trans C.front
  have hr := C.ran
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

/-- **(P2) at a link's readers.** -/
theorem objects_reader (H : LinkHoles) (l : Link S Claim) (pr : ℕ) (seat : Seat S Claim)
    (hA : AtS2 seat) (hs : ∀ s, H.silent pr "objects" s = none)
    (hfind : ∃ nm, (statesOfLink l pr).find? (fun r => r.1 == "objects") =
      some (nm, objectsRun seat)) :
    ∀ s R g, (readersOfLink H l).forms pr "objects" s = some R → seat.heard s = some g →
      R.late = [] ∧ ∀ f ∈ g.rows.toList, f ∈ R.forms := by
  intro s R g hR hg
  obtain ⟨run, cl, s', F, G, C⟩ := link_cut (by decide) (hs s) hR
  obtain ⟨nm, h1⟩ := hfind
  obtain ⟨nm', h2⟩ := C.found
  obtain rfl : objectsRun seat = run := congrArg Prod.snd (Option.some.inj (h1.symm.trans h2))
  obtain ⟨e1, e2⟩ := objects_readIs seat hA C g hg
  exact ⟨e1, fun f hf => by rw [e2]; exact hf⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.reader_cut
#print axioms VerifiableInference.OnPublicFiles.link_cut
#print axioms VerifiableInference.OnPublicFiles.ranAt_of_cut
#print axioms VerifiableInference.OnPublicFiles.objects_readIs
#print axioms VerifiableInference.OnPublicFiles.objects_reader
