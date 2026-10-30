-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersRequest.lean

Nothing on hiding. No property of the protocol is claimed.
THE SECOND CLAUSE, "req", OF ScriptTies (Johnson/Goal/HonestTrace/ConstrAtThread.lean), AT A LETTER FOR THE TOKEN.
The clause says: the request file's bytes, read back (Meaning.backReq), with the Script's token laid in
(OnBytes.Flat.putReq at P5J.tokVOf), are the request x. Here: where the two files of the input's instance are read as x
(ProofFile.instOf v.x = some x) and the Script's token is the first word of the reply file, as a number
(ProofFile.Honest.K3.askedTok v.x, the reading that the lookups use), the clause holds.

Called from EntersRequestWords.lean: "askedTokenOfInstance": where instOf ξ = some x, askedTok ξ is the number of x's
reply.

Main theorems.
* "requestReadBackWithToken": at an instance ξ, a number "token" and ANY default request: from instOf ξ = some x and
  token = askedTok ξ, the clause's equation.
* "requestReadBackWithTokenIff": where instOf ξ = some x, the clause's equation holds at a number "token" EXACTLY IF
  the request ends before the window's end or tokVOf token is x's reply. So the premise on the token is more than the
  clause needs only where x.e < ppref.T; at x.e = ppref.T it is needed up to tokVOf.
* "scriptTiesRequestClause": the clause to the letter, at a Script Q and an input v.
* "scriptTiesRequestClauseAtAskedToken": every Script with its field tok turned to "fun v => askedTok v.x" pays the
  premise on the token by rfl.
* "scriptTiesRequestClauseAtJoin": the clause at joinQ (Johnson/Desc/ProofFile/Honest/Thread/Join.lean), at letters for
  all its arguments: the premise is on its argument "token" alone.
* "requestBytesAreReadBack": where instOf ξ = some x, (backReq ξ.pub.request).isSome = true.
* "everyRequestIsReadOffItsFiles": at every well-formed request q and every table's key some instance is read as q, and
  askedTok there is the number of q's reply: the premise "read" has members.

Limits. THE PREMISE ON THE TOKEN, Q.tok v = askedTok v.x, IS MET HERE ONLY AT A SCRIPT WHOSE FIELD tok WAS OVERWRITTEN FOR
THE PURPOSE (scriptTiesRequestClauseAtAskedToken): at no Script that anybody lays. So the clause is paid at no run's
Script by this file. THE CLAUSE DOES NOT TIE THE TOKEN EXCEPT WHERE THE REQUEST FILLS THE WINDOW: by the iff, where
x.e < ppref.T it holds at every token. The reference sizes ppref alone. Q is a letter: that the Script reads its
token so is shown by nothing here. (It is shown in the side library, at the base prover:
AtFullSide/HonestTrace/EntersTokenAndCellsAtTheWrittenScript.lean.) That instOf returns at a run's
input is a premise. The clauses cells and syms of ScriptTies are not touched.
-/
import Johnson.Goal.HonestTrace.ConstrAtThread
import Johnson.Desc.ProofFile.InstOf
import Johnson.Desc.ProofFile.Honest.K3.WitReq
import Johnson.Goal.Meaning.Row
import Johnson.Desc.ProofFile.Honest.Thread.Join
import Johnson.HonestTrace.Joint.EntersRequestWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Enters

open Inst.Model (ppref Instance)
open ProofFile.Honest (Local ProverCoinCounts Coins)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K3 (askedTok)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Req)

/-- A token's own number, read as a token, is the token. -/
theorem tokVOf_val (t : Fin ppref.V) : P5J.tokVOf t.val = t := by
  unfold P5J.tokVOf
  rw [dif_pos t.isLt]

/-- Where the two files are read as x, the request file is read back as x without its reply. -/
theorem backReq_of_read {ξ : ProofFile.Inst} {x : Instance ppref} (read : ProofFile.instOf ξ = some x)
    (w : VerifiableInference.OnPublicFiles.Flat.WellFormed x) :
    Meaning.backReq ξ.pub.request = some (OnBytes.Flat.reqWithoutReply ⟨x, w⟩) := by
  rw [← (ProofFile.instOf_bytes read).1]
  exact Meaning.backReq_bytes ⟨x, w⟩

/-- **The clause's equation at letters.** Where the two files of ξ are read as x and "token" is the first word of the
reply file: the request file, read back, with that token laid in, is x. The default request is any: it is not reached. -/
theorem requestReadBackWithToken {ξ : ProofFile.Inst} {x : Instance ppref} (read : ProofFile.instOf ξ = some x)
    {token : ℕ} (tokenIsAsked : token = askedTok ξ) (default : Req) :
    (OnBytes.Flat.putReq ((Meaning.backReq ξ.pub.request).getD default) (P5J.tokVOf token)).val = x := by
  obtain ⟨-, -, w1, w2⟩ := ProofFile.instOf_bytes read
  rw [backReq_of_read read ⟨w1, w2⟩, Option.getD_some, tokenIsAsked, askedTokenOfInstance read, tokVOf_val]
  exact congrArg Subtype.val (OnBytes.Flat.putReq_glue ⟨x, w1, w2⟩)

/-- **How much of the token the clause's equation needs.** Where the two files of ξ are read as x: the equation holds at
"token" exactly if x ends before the window's end or the token, read by tokVOf, is x's reply. -/
theorem requestReadBackWithTokenIff {ξ : ProofFile.Inst} {x : Instance ppref} (read : ProofFile.instOf ξ = some x)
    (token : ℕ) (default : Req) :
    (OnBytes.Flat.putReq ((Meaning.backReq ξ.pub.request).getD default) (P5J.tokVOf token)).val = x ↔
      (¬ x.e < ppref.T → P5J.tokVOf token = x.y) := by
  obtain ⟨-, -, w1, w2⟩ := ProofFile.instOf_bytes read
  rw [backReq_of_read read ⟨w1, w2⟩, Option.getD_some]
  rw [← Meaning.putReq_back_iff ⟨x, w1, w2⟩ (P5J.tokVOf token)]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- **THE CLAUSE "req" OF ScriptTies, TO THE LETTER**, at a Script Q and an input v: from "the input's two files are read
as x" and "the Script's token is the first word of the reply file". -/
theorem scriptTiesRequestClause {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (v : Local W₀ Rc ProofFile.Inst T) {x : Instance ppref} (read : ProofFile.instOf v.x = some x)
    (tokenIsAsked : Q.tok v = askedTok v.x) :
    (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf (Q.tok v))).val = x :=
  requestReadBackWithToken read tokenIsAsked P5J.At.d₀

/-- A guard by Lean that the statement above is the clause to the letter: it fills the field req of ScriptTies. -/
example {Bk : ProverCoinCounts} {W₀ Rc T : Type} (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst T) (i : Cm.Idx) {x : Instance ppref}
    (cells : VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells v) i) (read : ProofFile.instOf v.x = some x)
    (tokenIsAsked : Q.tok v = askedTok v.x)
    (symbols : OnBytes.HonestTrace.ScriptSymsAt Z Zp cF Q k v (OnBytes.HonestTrace.theTrace (P5J.At.X Zp) i x)) :
    OnBytes.HonestTrace.ScriptTies Z Zp cF Q k v i x :=
  ⟨cells, scriptTiesRequestClause Q v read tokenIsAsked, symbols⟩

/-- Every Script whose field tok is turned to "the first word of the input's reply file" meets the clause wherever the
input's two files are read: the premise on the token is paid by rfl. -/
theorem scriptTiesRequestClauseAtAskedToken {Bk : ProverCoinCounts} {W₀ Rc T : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst T) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (v : Local W₀ Rc ProofFile.Inst T) {x : Instance ppref} (read : ProofFile.instOf v.x = some x) :
    (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf (({ Q with tok := fun u => askedTok u.x } :
        Script Bk (Local W₀ Rc ProofFile.Inst T) (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT).tok v))).val = x :=
  scriptTiesRequestClause _ v read rfl

/-- **The clause at the join of the senders' lots** (joinQ, Johnson/Desc/ProofFile/Honest/Thread/Join.lean), whatever its
other arguments: the join's token is its argument "token", so the premise is on that argument alone. -/
theorem scriptTiesRequestClauseAtJoin {Bk : ProverCoinCounts} {W₀ Rc T Cl Xi X : Type}
    (blocks : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Cl)) (front : ℕ)
    (cells : Local W₀ Rc ProofFile.Inst T → P5J.CellsM OnBytes.Flat.numsFull)
    (token : Local W₀ Rc ProofFile.Inst T → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
    (reader : Local W₀ Rc ProofFile.Inst T → ProofFile.Honest.K1.PlaceIn Xi) (own₀ : X)
    (jobs : List (ℕ × ProofFile.Honest.K1.SendJob (ProofFile.Honest.K1.PlaceIn Xi) X))
    (others : ProofFile.Honest.FirstThread.Others Bk (Local W₀ Rc ProofFile.Inst T))
    (v : Local W₀ Rc ProofFile.Inst T) {x : Instance ppref} (read : ProofFile.instOf v.x = some x)
    (tokenIsAsked : token v = askedTok v.x) :
    (OnBytes.Flat.putReq ((Meaning.backReq v.x.pub.request).getD P5J.At.d₀)
      (P5J.tokVOf ((ProofFile.Honest.FirstThread.joinQ blocks front cells token arr reader own₀ jobs others).tok v))).val
      = x :=
  scriptTiesRequestClause _ v read tokenIsAsked

/-- Where the two files are read, the request file's bytes are read back. (Spent in EntersRequestAtFirstThread.lean.) -/
theorem requestBytesAreReadBack {ξ : ProofFile.Inst} {x : Instance ppref} (read : ProofFile.instOf ξ = some x) :
    (Meaning.backReq ξ.pub.request).isSome = true := by
  obtain ⟨-, -, w1, w2⟩ := ProofFile.instOf_bytes read
  rw [backReq_of_read read ⟨w1, w2⟩]
  rfl

/-- **The premise "read" has members**: at every well-formed request q and every table's key, the instance made of q's two
files is read as q, and the first word of its reply file is the number of q's reply. Of the premise on the Script's token
this shows nothing: that one is a condition on a Script. -/
theorem everyRequestIsReadOffItsFiles (q : Req) (key : OnBytes.TableKey) :
    ∃ ξ : ProofFile.Inst, ξ.pub.key = key ∧ ProofFile.instOf ξ = some q.val ∧ askedTok ξ = q.val.y.val := by
  have read : ProofFile.instOf ⟨⟨OnBytes.Flat.requestBytesOf q.val, key⟩, OnBytes.Flat.replyBytesOf q.val⟩ = some q.val :=
    ProofFile.instOf_of_eq q (by dsimp only) (by dsimp only)
  exact ⟨_, rfl, read, askedTokenOfInstance read⟩

end HonestTraceRun.Enters

#print axioms HonestTraceRun.Enters.requestReadBackWithToken
#print axioms HonestTraceRun.Enters.requestReadBackWithTokenIff
#print axioms HonestTraceRun.Enters.scriptTiesRequestClause
#print axioms HonestTraceRun.Enters.scriptTiesRequestClauseAtAskedToken
#print axioms HonestTraceRun.Enters.scriptTiesRequestClauseAtJoin
#print axioms HonestTraceRun.Enters.requestBytesAreReadBack
#print axioms HonestTraceRun.Enters.everyRequestIsReadOffItsFiles
