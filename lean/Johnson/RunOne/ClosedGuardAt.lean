--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NO SOUNDNESS IS CLAIMED. ON HIDING: NOTHING.

Johnson/RunOne/ClosedGuardAt.lean: the request off the user's two files, behind the program's own
reader's test, AT EVERY P : Inst.Model.Params, with the three laws of
Johnson/RunOne/ClosedGuard.lean at that letter, and the equations by rfl that the landed small names
are these at sizesSmall.  Why. The proof file's check is wanted at two sizes. ClosedGuard.lean's
definitions name sizesSmall fifteen times (24 with the laws), and its laws' proofs unfold nothing
that is the small size's own: so one text serves every P. These names stand in Johnson.RunOne, at a
letter P; the files at the letter z (namespace Johnson.RunOne.AskZ) call them at z.P.

Main names. sizesOkAt, readerTakesAt, reqOfFilesAt, reqOfFilesGAt, xOfGAt; reqOfFilesGAt_bytes,
reqOfFilesGAt_some, xOfGAt_bytes; sizesOk_at, readerTakes_at, reqOfFiles_at, reqOfFilesG_at,
xOfG_at. Not here: guardP and guardAll, which stand on Closed.lean's data at a size.

Limits. «Every P» admits sizes at which the laws hold for nothing: at P.T = 0 or P.V = 0 the reader
takes no file, so reqOfFilesGAt is none everywhere. Of Params' fields sizesOkAt holds ten and the
reader's test reads T and V alone, as at the shipped size. xOfGAt's R is any type: what pins it is
the caller's. Else those of ClosedGuard.lean: what is shown is on the request alone: nothing on the
public files, nothing on the record, which is the parser's. Nothing on soundness.
Read once, hostile, in its second form (with the four files at z: A 1 · B 5 · C 11: laid here); this
form is unread.


-/
import Johnson.RunOne.ClosedGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne
open VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat

section
variable (P : Inst.Model.Params)

/-- **Are the sizes P the plan's?** P's ten numbers against those that sizesOf reads off the plan's
parameter lines, and the plan's own window. The acceptance policy: policyOk (ClosedGuard.lean),
which names no size. -/
def sizesOkAt (p : Model.Verify.Planned) : Bool :=
  p.X.T == P.T && (sizesOf p.X.P.h).T == P.T &&
    (sizesOf p.X.P.h).V == P.V && (sizesOf p.X.P.h).layers == P.layers &&
    (sizesOf p.X.P.h).d == P.d && (sizesOf p.X.P.h).nq == P.nq &&
    (sizesOf p.X.P.h).nkv == P.nkv && (sizesOf p.X.P.h).ch == P.ch &&
    (sizesOf p.X.P.h).f == P.f && (sizesOf p.X.P.h).fe == P.fe &&
    (sizesOf p.X.P.h).nexp == P.nexp

/-- The request at the sizes P off the user's two files, WITHOUT the reader's test: it returns at
files that the program's own reader refuses: a run takes reqOfFilesGAt. -/
def reqOfFilesAt (request y : ByteArray) : Option (ReqAt P) :=
  buildReqAt P (K.promptOf (stmOf request y), K.outputOf (stmOf request y))
    (K.auxOf (stmOf request y))

/-- **Does the program's own reader take the two files, at the sizes P?** Both are made of whole
words; the reader of request and reply (Head.stFromCall: T + 2 words and one; r < e ≤ T; the reply 0
where e < T) and the routine on the covered positions (Head.coveredOf: every token and the reply
below V) return, at P's window and vocabulary. -/
def readerTakesAt (request y : ByteArray) : Bool :=
  request.size % 4 == 0 && y.size % 4 == 0 &&
    match Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y)
        P.T with
    | .ok so => (Model.Head.coveredOf so P.T P.V).toBool
    | .error _ => false

/-- **The request at the sizes P off the user's two files**: nothing where the program's reader
refuses them; else the builder at the prompt, the output tokens and the further tokens. -/
def reqOfFilesGAt (request y : ByteArray) : Option (ReqAt P) :=
  if readerTakesAt P request y then
    reqOfFilesAt P request y
  else none

/-- **What reqOfFilesGAt returns says the user's two files, byte for byte**: two pairs of files
have two requests. The landed proof of reqOfFilesG_bytes with P for sizesSmall. -/
theorem reqOfFilesGAt_bytes {request y : ByteArray} {q : ReqAt P}
    (h : reqOfFilesGAt P request y = some q) :
    requestBytesOf q.val = request ∧ replyBytesOf q.val = y := by
  unfold reqOfFilesGAt at h
  split at h
  · rename_i t
    have h' : buildReqAt P
        (K.promptOf (stmOf request y), K.outputOf (stmOf request y))
        (K.auxOf (stmOf request y)) = some q := h
    unfold readerTakesAt at t
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    obtain ⟨⟨hr, hy⟩, t⟩ := t
    cases hs : Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y)
        P.T with
    | error e =>
      rw [hs] at t
      have t' : false = true := t
      cases t'
    | ok so =>
      rw [hs] at t
      have t1 : (Model.Head.coveredOf so P.T P.V).toBool = true := t
      cases hc : Model.Head.coveredOf so P.T P.V with
      | error e =>
        rw [hc] at t1
        have t' : false = true := t1
        cases t'
      | ok cov =>
        obtain ⟨i, g0, g1, g2⟩ :=
          insOf_bytes (P := P) (x := stmOf request y) hs hc hr hy
        have e : i = q.val := Option.some.inj (g0.symm.trans (buildReqAt_some h'))
        rw [← e]
        exact ⟨g1, g2⟩
  · cases h

/-- Where reqOfFilesGAt returns, reqOfFilesAt returns the same. -/
theorem reqOfFilesGAt_some {request y : ByteArray} {q : ReqAt P}
    (h : reqOfFilesGAt P request y = some q) : reqOfFilesAt P request y = some q := by
  unfold reqOfFilesGAt at h
  split at h
  · exact h
  · cases h

/-- **The instance**: the request off the user's files, behind the reader's test; the record, of
any type R, is the parser's. -/
def xOfGAt {R : Type} (request y : ByteArray) (rec : R) : Option (ReqAt P × R) :=
  (reqOfFilesGAt P request y).map fun q => (q, rec)

/-- **What xOfGAt returns says the user's two files, byte for byte**, and holds the record that was
handed over. -/
theorem xOfGAt_bytes {R : Type} {request y : ByteArray} {rec : R} {z : ReqAt P × R}
    (h : xOfGAt P request y rec = some z) :
    requestBytesOf z.1.val = request ∧ replyBytesOf z.1.val = y ∧ z.2 = rec := by
  unfold xOfGAt at h
  cases hq : reqOfFilesGAt P request y with
  | none =>
    rw [hq] at h
    have h' : (none : Option (ReqAt P × R)) = some z := h
    cases h'
  | some q =>
    rw [hq] at h
    have e : (q, rec) = z := Option.some.inj h
    subst e
    exact ⟨(reqOfFilesGAt_bytes P hq).1, (reqOfFilesGAt_bytes P hq).2, rfl⟩

end

/-! ## The landed small names are these at sizesSmall -/

theorem sizesOk_at : sizesOk = sizesOkAt sizesSmall := rfl
theorem readerTakes_at : readerTakes = readerTakesAt sizesSmall := rfl
theorem reqOfFiles_at : reqOfFiles = reqOfFilesAt sizesSmall := rfl
theorem reqOfFilesG_at : reqOfFilesG = reqOfFilesGAt sizesSmall := rfl
theorem xOfG_at : xOfG = xOfGAt (R := RecSmall) sizesSmall := rfl

end Johnson.RunOne

#print axioms Johnson.RunOne.reqOfFilesGAt_bytes
#print axioms Johnson.RunOne.reqOfFilesGAt_some
#print axioms Johnson.RunOne.xOfGAt_bytes
#print axioms Johnson.RunOne.xOfG_at
#print axioms Johnson.RunOne.sizesOk_at
#print axioms Johnson.RunOne.readerTakes_at
#print axioms Johnson.RunOne.reqOfFiles_at
#print axioms Johnson.RunOne.reqOfFilesG_at
#check @Johnson.RunOne.xOfGAt_bytes
#check @Johnson.RunOne.reqOfFilesGAt_bytes
