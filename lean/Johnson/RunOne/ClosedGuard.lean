-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/ClosedGuard.lean: tests that a run lays in front of the values of
Johnson/RunOne/Closed.lean, on the user's two files and on the planner's answer.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

  sizesOk p      the ten sizes that are typed in sizesSmall are those of the plan's parameter lines.
                 By reading, no test of guardP p on tokens sees another vocabulary: at the sample
                 of zeros they ask 0 < V alone; guardP at such a plan has not been evaluated.
  policyOk p     the plan's acceptance policy is exact match.
  guardAll p     guardP p, sizesOk p and policyOk p. WHO ASKS sizesOk BY NAME HAS NO TEST ON THE
                 POLICY: a run asks guardAll, or sizesOk and policyOk.
  readerTakes    the program's own reader of request and reply takes the two files, at the small
                 size's window and vocabulary.
  reqOfFilesG, xOfG   reqOfFiles and xOf behind that test. The builder alone returns at a request
                 file of fewer or more words, at e behind the window, at e before the window's end
                 with a reply that is not 0, at a file with a byte more, at a reply of no or two
                 words: there it makes the instance of other files.
  reqOfFilesG_bytes   what reqOfFilesG returns says the user's two files, byte for byte.
  reqOfFilesG_some    where reqOfFilesG returns, reqOfFiles returns the same.
  xOfG_bytes     the same of the instance that xOfG returns.

Limits. Nothing makes a caller call these tests. Nothing says that p is the planner's answer at the
user's public files. Nothing on the record, which is the parser's. Nothing on soundness.
The program does not import this file.

-/
import Johnson.RunOne.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne
open VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Flat

section
variable (p : Model.Verify.Planned)

/-- **Are the typed sizes the plan's?** The ten numbers of sizesSmall against those that sizesOf
reads off the plan's parameter lines, and the plan's own window. The acceptance policy: policyOk.
-/
def sizesOk : Bool :=
  p.X.T == sizesSmall.T && (sizesOf p.X.P.h).T == sizesSmall.T &&
    (sizesOf p.X.P.h).V == sizesSmall.V && (sizesOf p.X.P.h).layers == sizesSmall.layers &&
    (sizesOf p.X.P.h).d == sizesSmall.d && (sizesOf p.X.P.h).nq == sizesSmall.nq &&
    (sizesOf p.X.P.h).nkv == sizesSmall.nkv && (sizesOf p.X.P.h).ch == sizesSmall.ch &&
    (sizesOf p.X.P.h).f == sizesSmall.f && (sizesOf p.X.P.h).fe == sizesSmall.fe &&
    (sizesOf p.X.P.h).nexp == sizesSmall.nexp

/-- **Is the plan's acceptance policy exact match?** The test of sizesAt
(Johnson/Flat/Instance.lean: exactPolicy) at the plan's parameter lines. The policy is no part of
an instance, and the claims of Johnson/Flat/Claims.lean are those of exact match alone. -/
def policyOk : Bool := exactPolicy p.X.P.h

/-- The three tests on p. A RUN AT A p WHERE THIS SAYS NO SAYS NOTHING. -/
def guardAll : Bool := guardP p && sizesOk p && policyOk p

end

/-- **Does the program's own reader take the two files?** Both are made of whole words; the reader
of request and reply (Head.stFromCall: T + 2 words and one; r < e ≤ T; the reply 0 where e < T)
and the routine on the covered positions (Head.coveredOf: every token and the reply below V)
return, at the small size's window and vocabulary. -/
def readerTakes (request y : ByteArray) : Bool :=
  request.size % 4 == 0 && y.size % 4 == 0 &&
    match Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y)
        sizesSmall.T with
    | .ok so => (Model.Head.coveredOf so sizesSmall.T sizesSmall.V).toBool
    | .error _ => false

/-- **The request of the small size off the user's two files**: nothing where the program's reader
refuses them; else, as Flat.insReq at the full size, the builder at the prompt, the output tokens
and the further tokens. -/
def reqOfFilesG (request y : ByteArray) : Option (ReqAt sizesSmall) :=
  if readerTakes request y then
    reqOf (K.promptOf (stmOf request y), K.outputOf (stmOf request y)) (K.auxOf (stmOf request y))
  else none

/-- **What reqOfFilesG returns says the user's two files, byte for byte**: two pairs of files have
two requests. -/
theorem reqOfFilesG_bytes {request y : ByteArray} {q : ReqAt sizesSmall}
    (h : reqOfFilesG request y = some q) :
    requestBytesOf q.val = request ∧ replyBytesOf q.val = y := by
  unfold reqOfFilesG at h
  split at h
  · rename_i t
    have h' : buildReqAt sizesSmall
        (K.promptOf (stmOf request y), K.outputOf (stmOf request y))
        (K.auxOf (stmOf request y)) = some q := h
    unfold readerTakes at t
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    obtain ⟨⟨hr, hy⟩, t⟩ := t
    cases hs : Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y)
        sizesSmall.T with
    | error e =>
      rw [hs] at t
      have t' : false = true := t
      cases t'
    | ok so =>
      rw [hs] at t
      have t1 : (Model.Head.coveredOf so sizesSmall.T sizesSmall.V).toBool = true := t
      cases hc : Model.Head.coveredOf so sizesSmall.T sizesSmall.V with
      | error e =>
        rw [hc] at t1
        have t' : false = true := t1
        cases t'
      | ok cov =>
        obtain ⟨i, g0, g1, g2⟩ :=
          insOf_bytes (P := sizesSmall) (x := stmOf request y) hs hc hr hy
        have e : i = q.val := Option.some.inj (g0.symm.trans (buildReqAt_some h'))
        rw [← e]
        exact ⟨g1, g2⟩
  · cases h

/-- Where reqOfFilesG returns, reqOfFiles returns the same. -/
theorem reqOfFilesG_some {request y : ByteArray} {q : ReqAt sizesSmall}
    (h : reqOfFilesG request y = some q) : reqOfFiles request y = some q := by
  unfold reqOfFilesG at h
  split at h
  · exact h
  · cases h

/-- **The instance**: the request off the user's files, behind the reader's test; the record is the
parser's. -/
def xOfG (request y : ByteArray) (rec : RecSmall) : Option Yp :=
  (reqOfFilesG request y).map fun q => (q, rec)

/-- **What xOfG returns says the user's two files, byte for byte**, and holds the record that was
handed over. -/
theorem xOfG_bytes {request y : ByteArray} {rec : RecSmall} {z : Yp}
    (h : xOfG request y rec = some z) :
    requestBytesOf z.1.val = request ∧ replyBytesOf z.1.val = y ∧ z.2 = rec := by
  unfold xOfG at h
  cases hq : reqOfFilesG request y with
  | none =>
    rw [hq] at h
    have h' : (none : Option Yp) = some z := h
    cases h'
  | some q =>
    rw [hq] at h
    have e : (q, rec) = z := Option.some.inj h
    subst e
    exact ⟨(reqOfFilesG_bytes hq).1, (reqOfFilesG_bytes hq).2, rfl⟩

end Johnson.RunOne
