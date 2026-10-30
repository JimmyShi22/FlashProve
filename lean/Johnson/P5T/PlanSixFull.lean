-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSixFull.lean (kind K9): FIVE OF THE SEVEN PARTS OF THE CLOSED TEST `planFitsB` (Johnson/Desc/First/Link/Law/PlanFitsB.lean: «lengths · layoutOk · shapes · members · mask · answers · room») AT THE WRITTEN VALUES OF THE FULL SIZE, AT THE THREE BORDERS A SEGMENT WHERE K9's LAW ASKS IT: BY THE KERNEL. Definitions with
code, closed facts, statements.

Why. K9's fields inSeg · inRun · inTot fall to `InsideAt` at a reached state, and that to `PlanFits` (`insideAt_tied`): a sentence on public data alone, which part 5 rode true at 50 of 50 borders and nobody had as a theorem. Of its seven parts: layoutOk is a theorem at the constant already (`AtMg.layoutOk`); room reads the
planning program's number of slots of the BUILT segment, which no pin fixes: it stays. THE OTHER FIVE READ: the codes · the request's shape · the listed shapes M · the listed seats · the frames' lists own | keptBefore as the plan has them · the members · the segment's group · the table's count of messages: EACH IS PINNED.

What is said.
  `whereC`, `maskC`, `shapesC`, `membersC`, `maskBC`, `fiveC`: the five parts' own texts, with what they read of the structure of public numbers handed in piece by piece. `five_is`: they ARE the five parts, at any d: by rfl.
  `keptFull`: the frames' list keptBefore at the written values (`ownFull`: NotIxFull.lean beside this file).
  `bordersW`: 14 l + 9 | + 10 | + 11 (l < 24) and 347 | 348 | 349: 75 borders. `fiveAtW k`: the five at border k at the written values.
  `five_full` [BY THE KERNEL]: **true at all 75.** `five_off` [BY THE KERNEL; NEGATIVE]: with the listed shapes reversed: true at none.
  `five_at`: the same as a statement at one border.

Limits. The written values alone: that they are a verifier's is Johnson/P5J/PlanSixAtMg.lean's. The full size alone. One bent twin (the listed seats reversed: still accepted at 26 of 50 borders) says that the test is blind to something. Nothing on soundness.

-/
import Johnson.P5T.NotIxFull
import Johnson.Desc.First.Link.Law.PlanFitsB
import Johnson.Desc.First.Close.Law.AlikeFull
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Numbers ModelPart FoldData momentAt shiftAt)
open VerifiableInference.Desc.First.FillSent (ownAt keptAt)
open VerifiableInference.Desc.First.Close (mlFull)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)
open VerifiableInference.Desc.LinkJoin (shapesB membersB maskB)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2)

def whereC (sh : Params.ReqShape) (own : ℕ → ℕ → Array ℕ) (kept : ℕ → Array ℕ) (m t born j : ℕ) :
    Option ℕ :=
  if born == m then (own m t)[j]?
  else (((reqGroups sh).getD m {}).born.idxOf? (born, j)).bind fun i => (kept m)[i]?

def maskC (sh : Params.ReqShape) (own : ℕ → ℕ → Array ℕ) (kept : ℕ → Array ℕ) (m t : ℕ) :
    Option ℕ :=
  (((sh.link[m]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0).bind fun i => whereC sh own kept m t m i

def shapesC (sh : Params.ReqShape) (M : List OracleShape) (own : ℕ → ℕ → Array ℕ)
    (kept : ℕ → Array ℕ) (m t n : ℕ) : Bool :=
  sh.link.zipIdx.all fun L => L.1.messages.zipIdx.all fun x =>
    match whereC sh own kept m t L.2 x.2 with
    | some o => decide (o < n) && decide (M[o]? = some x.1.shape)
    | none => true

def membersC (M : List OracleShape) (places : List (ℕ × ℕ)) (ms : List Mem)
    (grp : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (List.range n).all fun o =>
    match M[o]?, places[o]? with
    | some sh, some x =>
      !grp.contains x ||
        match ms.find? fun y => decide (seatOf y = x) with
        | some y => decide ((y.1.l.get y.2).1 = sh)
        | none => true
    | _, _ => true

def maskBC (sh : Params.ReqShape) (M : List OracleShape) (own : ℕ → ℕ → Array ℕ)
    (kept : ℕ → Array ℕ) (m t n : ℕ) : Bool :=
  match maskC sh own kept m t with
  | some o =>
    decide (o < n) && (M[o]?).any fun s =>
      decide (s.maskRows = 1) && decide (s.maskCode = sh.maskCode) &&
        decide (s.answers = sh.answers)
  | none => true

/-- **The five parts, with what they read handed in piece by piece.** -/
def fiveC (cs : Codes) (sh : Params.ReqShape) (M : List OracleShape) (places : List (ℕ × ℕ))
    (own : ℕ → ℕ → Array ℕ) (kept : ℕ → Array ℕ) (ms : List Mem) (grp : List (ℕ × ℕ))
    (m t n : ℕ) : Bool :=
  cs.lengthsOk && shapesC sh M own kept m t n && membersC M places ms grp n &&
    maskBC sh M own kept m t n && decide (1 ≤ sh.answers)

/-- **They are the five parts of planFitsB, at any structure of public numbers.** -/
theorem five_is (d : FoldData) (ms : List Mem) (grp : List (ℕ × ℕ)) (m t n : ℕ) :
    (d.sent.codes.lengthsOk && shapesB d m t n && membersB d ms grp n && maskB d m t n &&
      decide (1 ≤ d.sent.shape.answers)) =
      fiveC d.sent.codes d.sent.shape d.M d.L.places d.ownAt d.keptAt ms grp m t n := rfl

/-- The frames' list keptBefore at the written values. -/
def keptFull (m : ℕ) : Array ℕ := keptAt shapeFull NFull P5J.At.links P5J.At.ps #[] m

/-- The 75 borders. -/
def bordersW : List ℕ :=
  ((List.range 24).flatMap fun l => [14 * l + 9, 14 * l + 10, 14 * l + 11]) ++ [347, 348, 349]

/-- The five at border k, at given listed shapes. -/
def fiveAtM (M : List OracleShape) (k : ℕ) : Bool :=
  match P5J.At.ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      fiveC codesFull2 shapeFull M LFull.places ownFull keptFull (msOf mlFull) (N0Full.group m) m
        (momentAt (shiftAt P5J.At.links m) p.piece) (NFull.msgsAt P5J.At.ps[k]?)
    | none => false
  | none => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(W) The five accept at all 75 borders.** -/
theorem five_full : (bordersW.all fun k => fiveAtM MFull k) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **(N)** With the listed shapes reversed they accept at none. -/
theorem five_off : (bordersW.any fun k => fiveAtM MFull.reverse k) = false := by decide +kernel

theorem five_at {k : ℕ} (hk : k ∈ bordersW) : fiveAtM MFull k = true :=
  List.all_eq_true.1 five_full k hk

end P5T

#print axioms P5T.five_is
#print axioms P5T.five_full
#print axioms P5T.five_off
#print axioms P5T.five_at
