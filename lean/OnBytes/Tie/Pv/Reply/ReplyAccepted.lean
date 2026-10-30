-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Reply/ReplyAccepted.lean: for an accepted proof file: the reply that the caller names
is the one item of the round that the last link's first call takes and closes under the name REPLY.
Statements and proofs.

What it is for. The program's verifier receives the reply as a plain scalar at the last link's
beginning and compares it, behind all links, with the reply that its caller names. Three files say a
part each: `accepted_head` (OnBytes/Tie/Pv/Keeps/KeepsChain.lean): in the run that the verdict rests
on, the last link's routine was started at a state whose first plain scalar is the caller's reply;
`check_first_parts` (OnBytes/Tie/Pv/Keeps/KeepsFirst.lean): that state's plain scalars are the list
which `Blk.recvEs` yielded; `reply_view` (OnBytes/Tie/Pv/Reply/ReplyView.lean): that list is what
the first of the rounds still to come holds. This file joins them.

Main names:
  `LinksChain.view_end`: a chain of links' calls that begins on a view ends on a view.
  `accepted_reply_round`: accepted; every link's routine keeps; the last link is of kind 2. Then,
    beside the records of the run (`FileRan`, the chain over the links before the last, the last
    link's `LinkStep` and the `FirstParts` of its first call): a round rv with: the rounds to come
    at the context c4 behind `beginLink` are rv and then those at c6, behind REPLY; rv holds ONE
    item, the caller's reply.
Limits: one direction: from the verdict. That the last link of the program's own list is of kind 2
is a premise. THREE THINGS ARE NOT SAID. That rv is a WHOLE round: rv is the first of what is still
to come at c4, and that is a whole round only if no message is open there. That rv is a round of the
file's view, and which by number: that what is to come at c4 is a tail of the view's rounds is said
by no law here. That the plan's entry at that round has the name REPLY. Nothing is said on what the
reply means.
-/
import OnBytes.Tie.Pv.Reply.ReplyView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Reply
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5 OnBytes.Model.Road OnBytes.PscRun

/-- A chain of links' calls that begins on a view ends on a view. -/
theorem LinksChain.view_end {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} :
    ∀ {rest : List LinkH} {l : Nat} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
      {r : ChainCheck × Proof.LinksResult} {c' : Ctx},
      LinksChain links p wsLay cEnd rest l check out c r c' → c.ch.dry = false →
      c'.ch.dry = false
  | [], _, _, _, _, _, _, h, d => by
    obtain ⟨-, e⟩ : _ ∧ _ := h
    rw [e]
    exact d
  | _ :: _, _, _, _, _, _, _, h, _ => by
    obtain ⟨_, _, _, _, _, _, _, _, _, d1, _, T⟩ := h
    exact LinksChain.view_end T d1

/-- **Accepted: the caller's reply is the one item of the round that is closed as REPLY.** -/
theorem accepted_reply_round (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (Xs : List LinkH) (Xh : LinkH) (hZ : Z.toList = Xs ++ [Xh]) (h2 : Xh.kind = 2) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkH outH cH chk o C' F' c1 c2
      fr L G g plain kept ids mask j c4 c5 c6 c7 rv,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE Xs 0 check0 {} ca (checkH, outH) cH ∧
      LinkStep Z c.first wsLay cE Xs.length Xh checkH outH cH rN cb chk o C' F' c1 c2 ∧
      FirstParts checkH.frame cE cH fr c1 L G g plain kept ids mask j c4 c5 c6 c7 ∧
      c4.ch.pending = rv :: c6.ch.pending ∧ rv.vals = [Fmt.ItemValue.e reply.triple] := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkH, outH, cH, chk, o, C', F', c1, c2,
    R, A, S, hr⟩ := accepted_head Z hk h Xs Xh hZ h2
  have dH : cH.ch.dry = false := LinksChain.view_end A R.viewA
  obtain ⟨fr, L, G, g, plain, kept, ids, mask, j, c4, c5, c6, c7, P, -, hp⟩ :=
    check_first_parts (cEnd := cE) checkH dH S.m1 S.first
  have hk2 : (Xh.kind == 2) = true := by rw [h2]; rfl
  have hs : plain.length = 1 := by
    have e := (S.plainHead hk2).1
    rw [hp] at e
    simpa using e
  have h0 : plain[0]? = some reply := by
    rw [hp] at hr
    simpa using hr
  have hpl : plain = [reply] := by
    match plain, hs, h0 with
    | [x], _, h0 => exact congrArg (fun y => [y]) (Option.some.inj h0)
  have hne : (L.plain != 0) = true := by
    by_contra hn
    have e := (noReply_view P hn).1
    rw [e] at hs
    cases hs
  obtain ⟨rv, a1, a2, -, -⟩ := reply_view P hne
  refine ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkH, outH, cH, chk, o, C', F', c1, c2,
    fr, L, G, g, plain, kept, ids, mask, j, c4, c5, c6, c7, rv, R, A, S, P, a1, ?_⟩
  have a3 : rv.vals = plain.map fun x => Fmt.ItemValue.e x.triple := a2
  rw [a3, hpl]
  rfl

#print axioms accepted_reply_round

end OnBytes.Tie.Pv.Reply
