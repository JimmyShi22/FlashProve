-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InsReqWords.lean: at the reference sizes and exact match: where the Lean program says
yes, insReq returns; what it returns is a request that the program's reader takes, and what says it
(numbers, words, bytes, the hashed item) is what the program has read and made of the request file
and the reply file. Where the input's builder is buildReq that is the instance at the tie's slot.

Johnson/Flat/InsOf.lean and ItemOf.lean have the laws for buildOf at any sizes (insOf_words,
insOf_port_bytes). This file carries them to insReq (Johnson/Top/InsReq.lean), the instance of the
flat description at the full size, and to the field insOf of the tie's shape.

One record and six theorems.
  insReq_iff: insReq x returns q if and only if insOf ppref x returns q's instance.
  insReq_words: where the program's reader of request and reply and its routine on the covered
    positions return, at the reference's window and vocabulary: insReq x = some q, and
    requestWordsOf q.val, replyWordsOf q.val are the words of the two files; q's r, e, y are the
    reader's.
  InsAt F q: what ties a request q to a call's files F: the plan p of the three public files has the
    reference's window and vocabulary; the reader has returned so and the routine on the covered
    positions cov, on F's own words; q's r, e, y are so's; q's words and bytes are the two files';
    the item "request" at q is the one that the program makes of F's files. (r < e, and y = 0 if e
    is before the window's end, are q's own property.) Every letter under "there is" in it is the
    value of a function at F's bytes.
  insReq_port: PortYesAt (OnBytes/K/Top.lean), with "sizesAt reads the reference sizes off the
    parameter file", gives q with insReq (stmOf F o) = some q and InsAt F q.
  session_ins: so the first clause of the slot "session" (KeyProofPart, OnBytes/K/Parts.lean) holds
    at the shape of Johnson/Top/TieInnerCompiledVerifier.lean at innerCompilerInputFromDryRunAtFullSize T, where T's builder is buildReq:
    the shape's insOf returns q, with InsAt F q.
  session_ins_served: the same under the slot's own premise "the statement is served", where what
    is served at the tie is served at three public files Z (servedAt, OnBytes/K/Served.lean) and the
    test sizesRefB (Johnson/Top/SizesRef.lean) says true at Z's parameter file: one evaluation.
  session_ins_tieAt: the same at the tie that serves exactly what servedAt Z takes (tieAt Z recOf,
    Johnson/Top/TieInnerCompiledVerifierServed.lean): there the premise on the tie holds by definition.

Limits: NO T, NO TIE'S recOf AND NO Z IS GIVEN: session_ins and session_ins_served have been applied
to nothing. insReq_port needs none of them. Z is a letter: nothing here ties Z to N, s or the
claims; the test compares ten sizes and the policy, no other line and neither of the other two
files. EXACT MATCH ALONE: sizesAt refuses a parameter file whose acceptance policy is not exact
match. By a reading of the program's test (servedOf, OnBytes/Model/VerifyStages.lean; no theorem),
at a file with another policy the program can still pass: under the option -policy, or, without it,
at a request that covers the reply alone. At such a FILE these theorems are silent. THE
REFERENCE SIZES ALONE: at the small example's files the test says false. Nothing on what a yes says
of the instance; nothing on the session's typed string or its verifier: of the slot's three clauses
this is the first.

-/
import Johnson.Flat.ItemOf
import Johnson.Top.TieInnerCompiledVerifierServed
import Johnson.Top.InsReq
import Johnson.Top.SizesRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles

open Inst.Model
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Model OnBytes.Model.Verify
open OnBytes.K (UserStm InnerInputTieData innerInputTieShape)

/-- insReq returns q if and only if insOf, at the reference sizes, returns q's instance. -/
theorem Flat.insReq_iff {x : UserStm} {q : Flat.Req} :
    Flat.insReq x = some q ↔ insOf ppref x = some q.val :=
  Flat.buildReq_iff

/-- **Where the program's reader takes request and reply, insReq returns, and the words that say the
instance are the files' words.** -/
theorem Flat.insReq_words {x : UserStm} {so : Head.StOwn} {cov : Head.Covered}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) ppref.T = .ok so)
    (hc : Head.coveredOf so ppref.T ppref.V = .ok cov) :
    ∃ q : Flat.Req, Flat.insReq x = some q ∧ requestWordsOf q.val = words32 x.request ∧
      replyWordsOf q.val = words32 x.y ∧ q.val.r = so.r ∧ q.val.e = so.e ∧
      q.val.y.val = so.y := by
  obtain ⟨i, h0, h1, h2, h3, h4, h5, h6, h7⟩ := insOf_words h hc
  exact ⟨⟨i, h6, h7⟩, Flat.insReq_iff.2 h0, h1, h2, h3, h4, h5⟩

/-- What ties a request to a call's files. In words: the head of this file. -/
structure Flat.InsAt (F : K.Files) (q : Flat.Req) : Prop where
  plan : ∃ p : Planned, planned F.pol F.KL (some F.lay) = .ok p ∧ ppref.T = p.X.T ∧
    ppref.V = p.X.P.h.V
  read : ∃ (so : Head.StOwn) (cov : Head.Covered),
    Head.stFromCall (words32 F.request) (words32 F.y) ppref.T = .ok so ∧
    Head.coveredOf so ppref.T ppref.V = .ok cov ∧
    q.val.r = so.r ∧ q.val.e = so.e ∧ q.val.y.val = so.y
  words : requestWordsOf q.val = words32 F.request ∧ replyWordsOf q.val = words32 F.y
  bytes : requestBytesOf q.val = F.request ∧ replyBytesOf q.val = F.y
  item : ∃ item : ByteArray, itemOf F.pol F.KL q.val = some item ∧
    Proof.requestItem F.pol F.KL F.request = some item

/-- **Where the program says yes, insReq returns a request that is tied to the call's files.** -/
theorem Flat.insReq_port {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) (hP : sizesAt F.pol = .ok ppref) :
    ∃ q : Flat.Req, Flat.insReq (K.stmOf F o) = some q ∧ Flat.InsAt F q := by
  obtain ⟨p, i, item, g0, g1, g2, h0, b1, b2, i1, i2, w1, w2⟩ := insOf_port_bytes hp o hP
  obtain ⟨_, p', C, -, -, -, -, -, -, -, -, -, -, hpl, -, -, -, -,
    ⟨so, cov, _, _, hst, hcov, -⟩, -, -, -, -, ⟨hX, -⟩, -⟩ := hp
  have ep : p' = p := Except.ok.inj (hpl.symm.trans g0)
  rw [hX, ep, ← g1] at hst
  rw [hX, ep, ← g1, ← g2] at hcov
  have hst' : Head.stFromCall (words32 (K.stmOf F o).request) (words32 (K.stmOf F o).y) ppref.T =
      .ok so := hst
  obtain ⟨q, q0, q1, q2, q3, q4, q5⟩ := Flat.insReq_words hst' hcov
  have ei : q.val = i := Option.some.inj ((Flat.insReq_iff.1 q0).symm.trans h0)
  refine ⟨q, q0, ⟨p, g0, g1, g2⟩, ⟨so, cov, hst, hcov, q3, q4, q5⟩, ⟨q1, q2⟩, ?_,
    item, ?_, i2⟩
  · rw [ei]
    exact ⟨b1, b2⟩
  · rw [ei]
    exact i1

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **The first clause of the slot "session"**: the shape's insOf returns a request that is tied to
the call's files. -/
theorem session_ins (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) (Tt : InnerInputTieData (innerCompilerInputFromDryRunAtFullSize T))
    {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) (hP : sizesAt F.pol = .ok ppref) :
    ∃ q : Flat.Req, (innerInputTieShape Tt).insOf (K.stmOf F o) = some q ∧ Flat.InsAt F q := by
  obtain ⟨q, h0, h1⟩ := Flat.insReq_port hp o hP
  exact ⟨q, (insOf_eq N s E G P T hb Tt _).trans h0, h1⟩

/-- **The same under the slot's own premise**, where what is served at the tie is served at a
description's three public files, and the test on the sizes says true at its parameter file. -/
theorem session_ins_served
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) (Tt : InnerInputTieData (innerCompilerInputFromDryRunAtFullSize T)) {Z : K.Pub}
    (hT : ∀ x, Tt.Served x → K.servedAt Z x = true) (t : Flat.sizesRefB Z.pol = true)
    {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options)
    (hS : (innerInputTieShape Tt).Served (K.stmOf F o)) :
    ∃ q : Flat.Req, (innerInputTieShape Tt).insOf (K.stmOf F o) = some q ∧ Flat.InsAt F q :=
  session_ins N s E G P T hb Tt hp o (Flat.sizesAt_of_served (hT _ hS) t)

end

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **The same at the tie that serves exactly what servedAt Z takes**: no premise on the tie. -/
theorem session_ins_tieAt
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) (Z : K.Pub)
    (recOf : UserStm → OnBytes.Params.TableName → Option (innerCompilerInputFromDryRunAtFullSize T).protocol.Rec)
    (t : Flat.sizesRefB Z.pol = true)
    {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options)
    (hS : (innerInputTieShape (K.tieAt Z recOf)).Served (K.stmOf F o)) :
    ∃ q : Flat.Req, (innerInputTieShape (K.tieAt Z recOf)).insOf (K.stmOf F o) = some q ∧
      Flat.InsAt F q :=
  session_ins_served N s E G P T hb (K.tieAt Z recOf) (fun _ h => h) t hp o hS

end

end VerifiableInference.OnPublicFiles
