-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SilentIsRun.lean.
WHAT IT DOES NOT SHOW. No soundness. THE RUNS "join" AND "planes" ARE NOT HERE (Law/ReaderRides.lean
says why). THAT THE READER ANSWERS AT ALL, AT EITHER RECORD: not shown: the statement is an equation
of options: the two answers are one, or both readers are silent. The two yeses of the place, and the
three premises on which run stands in the link under the name (hf, fwd, bwd: see
Law/ReaderRides.lean), are premises.
LETTERS. Under "there is": cov, x, tt: pinned by s.covered ... = .ok cov, a.x = some x, tables ...
cov x = .ok tt.
OBJECT. The border right behind the output head's own block, in front of the place that sends the
reads; the reader of one of the head's three own runs (Desc/First/Batch/ReaderOf.lean: readerOf).
USER. A filling of the letter "the reader of a run where the run itself is silent"
(Desc/First/Batch/ReadersOfLink.lean: LinkHoles.silent) by "the run itself, at the record with the
tables of reads laid as the quiet step will lay them". FOR THREE OF THE FIVE RUNS THAT ARE SILENT
THERE, AND UNDER THE THREE PREMISES ON THE RUN, this law says that such a filling's answer is the
run's own answer one place later; for "join" and "planes" nothing says so.
WHAT IT IS. AT THAT BORDER THE RUN IS SILENT FOR WANT OF THE TABLES OF READS. LAY THEM IN THOUGHT,
AS A FUNCTION OF THE RECORD THERE: WHAT THE RUN's READER THEN ANSWERS IS WHAT IT ANSWERS OF ITSELF
BEHIND THE SENDING AND THE QUIET STEP: ONE VALUE, AS OPTIONS: the same forms and no late slot, or
nothing at both. (Both hold because the sending fills no
slot: Law/ReadsLaidAlike.lean has each record "alike" to the other.)
  silent_is_run_own    at the two yeses.
  silent_is_run_later  at the one block as the link holds it (K1.laterAt, then the quiet step).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsLaidAlike
import Johnson.Desc.Kinds.Law.ReaderRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K1 (commitAtS)
open VerifiableInference.Desc.K8
open VerifiableInference.Desc.K9 (readerOf RunOf)

/-- From what Law/ReadsLaidAlike.lean hands out to the reader's one answer: AN EQUATION OF OPTIONS:
where the one answers so does the other, the same; where the one is silent so is the other. -/
theorem rides_of_laid (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Par)
    {states : Nat → List (RunOf S)} {b : Nat} {name : String}
    {run run' : Nat → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == name) = some (name, run))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run')
    (fwd : ∀ k t y, run k t = .ok y → run' k t = .ok y)
    (bwd : ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    {s s' : S} {a o' : HeadOwn} {tt : Model.Head.Tables} (hop : a.opened = true)
    (ho' : s'.here = .head o') (al : Alike { s with here := .head { a with t := some tt } } s')
    (la : Alike s' { s with here := .head { a with t := some tt } })
    (hrow : o'.F.trees.map (·.R) = a.F.trees.map (·.R)) :
    readerOf states b name s' =
      readerOf states b name { s with here := .head { a with t := some tt } } := by
  have hop' : o'.opened = true := by
    obtain ⟨o, o2, e1, e2, _, _, _, e6, _⟩ := al
    rw [ho'] at e2
    injection e2 with e2
    injection e1 with e1
    rw [e2, e6, ← e1]
    exact hop
  have hF : ({ s with here := .head { a with t := some tt } } : S).fork? = some a.F := by
    unfold S.fork?
    simp [hop]
  have hF' : s'.fork? = some o'.F := by
    unfold S.fork?
    rw [ho']
    simp [hop']
  cases h1 : readerOf states b name { s with here := .head { a with t := some tt } } with
  | some R => exact reader_rides_own h iU3 l piece p hf hrun fwd bwd al hF hF' hrow h1
  | none =>
    cases h2 : readerOf states b name s' with
    | none => rfl
    | some R =>
      have h3 := reader_rides_own h iU3 l piece p hf hrun fwd bwd la hF' hF hrow.symm h2
      rw [h1] at h3
      cases h3

/-- **THE READER's ANSWER WITH THE TABLES LAID IN THOUGHT IS ITS OWN ANSWER BEHIND THE PLACE.** -/
theorem silent_is_run_own (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Par)
    {states : Nat → List (RunOf S)} {b : Nat} {name : String}
    {run run' : Nat → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == name) = some (name, run))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run')
    (fwd : ∀ k t y, run k t = .ok y → run' k t = .ok y)
    (bwd : ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    {Cl : Type} {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {P : ReadsQuiet.PH} {s s1 s' : S} {a : HeadOwn} {rs rs' : List Fmt.RoundView}
    {gs gs' : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (h1 : (commitAtS (Cl := Cl) Q link moment arrays).decide s rs gs = .ok s1)
    (h2 : (ReadsQuiet.head P).decide s1 rs' gs' = .ok s') :
    ∃ cov x tt, a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧
      readerOf states b name s' =
        readerOf states b name { s with here := .head { a with t := some tt } } := by
  obtain ⟨cov, x, tt, o', g1, g2, g3, g4, g5, g6, g6', g7, _⟩ := reads_laid_alike ha h1 h2
  exact ⟨cov, x, tt, g1, g2, g3, g4,
    rides_of_laid h iU3 l piece p hf hrun fwd bwd g1 g5 g6 g6' g7⟩

/-- **The same at the block as the link holds it.** -/
theorem silent_is_run_later (h : Model.Head.Shape) (iU3 l piece : Nat) (p : Par)
    {states : Nat → List (RunOf S)} {b : Nat} {name : String}
    {run run' : Nat → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == name) = some (name, run))
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run')
    (fwd : ∀ k t y, run k t = .ok y → run' k t = .ok y)
    (bwd : ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    {q : Params.First} {gp : _root_.Desc.Plain.GPar} {link pc moment : Nat}
    {arrays : Option (List Nat)} {P : ReadsQuiet.PH} {nm : String} {s s' : S} {a : HeadOwn}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (ha : s.here = .head a)
    (hy : ((K1.laterAt q gp link pc moment arrays : Block S Unit).andThen nm
      (ReadsQuiet.head P)).decide s rs gs = .ok s') :
    ∃ cov x tt, a.opened = true ∧ s.covered P.h.T P.h.V = .ok cov ∧ a.x = some x ∧
      ReadsQuiet.tables P.h P.L P.hp cov x = .ok tt ∧
      readerOf states b name s' =
        readerOf states b name { s with here := .head { a with t := some tt } } := by
  obtain ⟨cov, x, tt, o', g1, g2, g3, g4, g5, g6, g6', g7, _⟩ := reads_laid_later ha hy
  exact ⟨cov, x, tt, g1, g2, g3, g4,
    rides_of_laid h iU3 l piece p hf hrun fwd bwd g1 g5 g6 g6' g7⟩

end VerifiableInference.Desc.Kinds.Head.Law
