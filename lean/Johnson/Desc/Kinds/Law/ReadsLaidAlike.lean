-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsLaidAlike.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on what a run answers: for the output head's own three
runs Law/RunsFixed.lean (letters_alike, run_fixed) goes on from "Alike"; for "join" and "planes"
nothing is said here. THAT THE TWO YESES ARE THERE: premises. Nothing on the list of tables' closing
(the field tl, which the quiet step also lays): Alike does not read it.
LETTERS. Under "there is": cov, x, tt: pinned by s.covered ... = .ok cov, a.x = some x, tables ...
cov x = .ok tt · o': by s'.here = .head o'.
OBJECT. The place of the head's link that sends the reads: a sending (Desc/K1/AtS.lean: commitAtS)
and, behind it, the quiet step that makes the tables of reads (Desc/K8/ReadsQuiet.lean: head P).
USER. A reader of the output head's runs at the border in front of that place, where the runs
themselves are silent for want of the tables: whoever lays the tables "in thought" there.
WHAT IT IS. THE TABLES OF READS THAT THE QUIET STEP LAYS BEHIND THE SENDING ARE ALREADY A FUNCTION
OF THE RECORD IN FRONT OF THE SENDING; AND THAT RECORD, WITH THESE TABLES LAID AND NOTHING ELSE
TURNED, IS "ALIKE" TO THE RECORD BEHIND THE QUIET STEP, AND THAT ONE TO IT: as far as the output
head's readers see, each goes on from the other (the sending fills no slot: the two ledgers have the
same slots, not only later ones). The arrays' numbers of rows and the list of owed claims are the
same too.
  reads_laid_alike  the statement, at the two yeses.
  reads_laid_place  the same at the one block "the sending, then the quiet step".
  reads_laid_later  the same at that block as the link holds it (Desc/K1/Places.lean: laterAt).

-/
import Mathlib
import Johnson.Desc.K1.Places
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.Kinds.Law.SendingKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K1 (commitAtS)
open VerifiableInference.Desc.K8

/-- **THE RECORD IN FRONT, WITH THE TABLES LAID IN THOUGHT, IS ALIKE TO THE RECORD BEHIND.** -/
theorem reads_laid_alike {Cl : Type} {Q : K1.Par} {link moment : Nat}
    {arrays : Option (List Nat)} {P : ReadsQuiet.PH} {s s1 s' : S} {a : HeadOwn}
    {rs rs' : List Fmt.RoundView} {gs gs' : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h1 : (commitAtS (Cl := Cl) Q link moment arrays).decide s rs gs = .ok s1)
    (h2 : (ReadsQuiet.head P).decide s1 rs' gs' = .ok s') :
    ∃ cov x tt o', a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧ s'.here = .head o' ∧
      Alike { s with here := .head { a with t := some tt } } s' ∧
      Alike s' { s with here := .head { a with t := some tt } } ∧
      o'.F.trees.map (·.R) = a.F.trees.map (·.R) ∧ o'.F.owed = a.F.owed := by
  obtain ⟨o1, e1, k1, k2, k3, k4, k5, k6, k7, k8⟩ := sending_at ha h1
  obtain ⟨a1, cov, x, tt, tl', g1, g2, g3, g4, g5, _, rfl⟩ := ReadsQuiet.head_ok h2
  obtain rfl : o1 = a1 := by
    rw [e1] at g1
    injection g1
  have hc : s1.covered P.h.T P.h.V = s.covered P.h.T P.h.V := by
    unfold S.covered S.replyTok? S.coveredAt
    rw [k7, k6]
  refine ⟨cov, x, tt, _, k4 ▸ g2, hc ▸ g3, k1 ▸ g4, g5, rfl, ?_, ?_, k8.rows, k8.owed⟩
  · exact ⟨_, _, rfl, rfl, k1, k2, rfl, k4, k5, k6, k7, k8.slots.later, k8.cols⟩
  · exact ⟨_, _, rfl, rfl, k1.symm, k2.symm, rfl, k4.symm, k5.symm, k6.symm, k7.symm,
      (OnBytes.PscRun.SlotsSame.later ⟨k8.slots.ns.symm, k8.slots.next.symm, k8.slots.vp.symm,
        k8.slots.mf.symm, k8.slots.gotF.symm⟩), k8.cols.symm⟩

/-- **The same at the one block: the sending, then the quiet step.** -/
theorem reads_laid_place {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {P : ReadsQuiet.PH} {name : String} {s s' : S} {a : HeadOwn} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h : ((commitAtS Q link moment arrays : Block S Unit).andThen name
      (ReadsQuiet.head P)).decide s rs gs = .ok s') :
    ∃ cov x tt o', a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧ s'.here = .head o' ∧
      Alike { s with here := .head { a with t := some tt } } s' ∧
      Alike s' { s with here := .head { a with t := some tt } } ∧
      o'.F.trees.map (·.R) = a.F.trees.map (·.R) ∧ o'.F.owed = a.F.owed := by
  simp only [Block.andThen, Except.bind] at h
  split at h
  · cases h
  · rename_i s1 h1
    exact reads_laid_alike ha h1 h

/-- **The same at the block as the link holds it**: K1's "a segment's later moment" is that sending,
at numbers made of the public ones. -/
theorem reads_laid_later {q : Params.First} {gp : _root_.Desc.Plain.GPar} {link piece moment : Nat}
    {arrays : Option (List Nat)} {P : ReadsQuiet.PH} {name : String} {s s' : S} {a : HeadOwn}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h : ((K1.laterAt q gp link piece moment arrays : Block S Unit).andThen name
      (ReadsQuiet.head P)).decide s rs gs = .ok s') :
    ∃ cov x tt o', a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧ s'.here = .head o' ∧
      Alike { s with here := .head { a with t := some tt } } s' ∧
      Alike s' { s with here := .head { a with t := some tt } } ∧
      o'.F.trees.map (·.R) = a.F.trees.map (·.R) ∧ o'.F.owed = a.F.owed :=
  reads_laid_place ha h

end VerifiableInference.Desc.Kinds.Head.Law
