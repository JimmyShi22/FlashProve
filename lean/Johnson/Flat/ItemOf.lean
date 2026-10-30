-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ItemOf.lean: the statement's item "request" as a function of the instance, and the
request file, the reply file and that item at the exit code 0 of verify-on-bytes, said by the
instance.

The statement of a proof's first chain holds the request in two items (`Params.First.statement`,
OnBytes/Params/Chains.lean): "the request file's words", the request file whole, and "request":
`Proof.requestItem` (OnBytes/Proof/RequestItem.lean) makes the latter of the parameter file, the
scale file and the request FILE; the reply's word in it is 0. `itemOf policy KL x` is that function
at the request file that
says the instance x (`requestBytesOf`, Johnson/Flat/WordsBytes.lean). Every label, number of a call
and layout in the item is the port's own: this file types none.

Main names:
  `itemOf`: the definition.
  `itemOf_withoutReply`: the item at the instance with the reply 0 is the item at the instance (by
    rfl): the item is a function of what the first query holds under the ruled typing.
  `port_whole_words`: at what the exit code 0 says of the bytes (`K.PortYesAt`) the request file and
    the reply file are made of whole words.
  `PortItem F o P p i cov ls item`: the record `PortIns` (Johnson/Flat/InsOf.lean) and four facts
    more, with names. `portItem_of_port`: there, at the sizes P that `sizesAt` reads off the
    parameter file, there are p, i, cov, ls, item with that record: THE TWO FILES REBUILT FROM i ARE
    THE CALL's OWN REQUEST FILE AND REPLY FILE, and `itemOf` at i is `Proof.requestItem` at the
    call's files, which has returned. What a proof's first chain holds under the name "request" is
    this ITEM, not the request file's bytes: these stand in an item of their own, "the request
    file's words". `insOf_port_bytes`: ten of these facts as one conjunction, for
    those who take it apart by place.
Limits: in the item the request stands as a tree digest under the second hash function (`secondHashFunctionTree`,
OnBytes/Hash/SecondHashFunction.lean): nothing here says that two requests have two items. `sizesAt policy = .ok
P` is a premise of its own: the exit code 0 can occur where it refuses (Johnson/Flat/InsOf.lean,
Limits). No clause names the proof file.

-/
import Johnson.Flat.WordsBytes
import OnBytes.Model.VerifyLawsWhole

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- **The statement's item "request" at an instance.** -/
def itemOf (policy KL : ByteArray) {P : Params} (x : Instance' P) : Option ByteArray :=
  Proof.requestItem policy KL (requestBytesOf x)

/-- The item at the instance with the reply 0 is the item at the instance. -/
theorem itemOf_withoutReply (policy KL : ByteArray) {P : Params} (hV : 0 < P.V) (x : Instance' P) :
    itemOf policy KL (withoutReply hV x) = itemOf policy KL x := rfl

/-- Where the stage request's run returns, the two files are made of whole words. -/
theorem requestRun_whole_words {C : Common} {o : Options} {r : Read} {entry : ByteArray}
    {x : RequestRun} (h : requestRun C o r entry = .ok x) :
    r.request.size % 4 = 0 ∧ r.y.size % 4 = 0 := by
  unfold requestRun at h
  obtain ⟨_, h1, _⟩ := exc_bind h
  have hb := refuseIf_ok h1
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hb
  exact hb

/-- At what the exit code 0 says of the bytes the two files are made of whole words. -/
theorem port_whole_words {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) : F.request.size % 4 = 0 ∧ F.y.size % 4 = 0 := by
  obtain ⟨r, _, C, _, _, _, _, e5, e6, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨o, ac, w, _, _, hs⟩, _, _⟩ := hp
  unfold requestStage at hs
  cases hx : requestRun C o r F.ent with
  | error e =>
    rw [hx] at hs
    cases hs
  | ok x =>
    have := requestRun_whole_words hx
    rw [e5, e6] at this
    exact this

/-- **The two files and the item at the exit code 0, said by the instance.** No field names the
proof file. -/
structure PortItem (F : K.Files) (o : Options) (P : Params) (p : Planned) (i : Instance' P)
    (cov : Head.Covered) (ls : Array Stages.LinkH) (item : ByteArray) : Prop where
  /-- the record of Johnson/Flat/InsOf.lean -/
  ins : PortIns F o P p i cov ls
  /-- the two files rebuilt from i are the call's own -/
  request_bytes : requestBytesOf i = F.request
  reply_bytes : replyBytesOf i = F.y
  /-- the item at i is the item that the program has made of the call's files -/
  item_of : itemOf F.pol F.KL i = some item
  item_port : Proof.requestItem F.pol F.KL F.request = some item

/-- **From what the exit code 0 says of the bytes.** In words: the head of this file. -/
theorem portItem_of_port {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) {P : Params}
    (hP : sizesAt F.pol = .ok P) : ∃ p i cov ls item, PortItem F o P p i cov ls item := by
  obtain ⟨hr, hy⟩ := port_whole_words hp
  obtain ⟨p, i, cov, ls, I⟩ := portIns_of_port hp o hP
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨_, _, item, _, _, _, hitem, _, _⟩, _⟩ := hp
  have eR : requestBytesOf i = F.request := by
    unfold requestBytesOf
    rw [I.request_words]
    exact bytesOfWords_words32 _ hr
  have eY : replyBytesOf i = F.y := by
    unfold replyBytesOf
    rw [I.reply_words]
    exact bytesOfWords_words32 _ hy
  refine ⟨p, i, cov, ls, item, I, eR, eY, ?_, hitem⟩
  unfold itemOf
  rw [eR]
  exact hitem

/-- Ten of these facts as one conjunction. -/
theorem insOf_port_bytes {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) {P : Params}
    (hP : sizesAt F.pol = .ok P) :
    ∃ (p : Planned) (i : Instance' P) (item : ByteArray),
      planned F.pol F.KL (some F.lay) = .ok p ∧ P.T = p.X.T ∧ P.V = p.X.P.h.V ∧
      insOf P (K.stmOf F o) = some i ∧ requestBytesOf i = F.request ∧ replyBytesOf i = F.y ∧
      itemOf F.pol F.KL i = some item ∧ Proof.requestItem F.pol F.KL F.request = some item ∧
      i.r < i.e ∧ (i.e < P.T → i.y.val = 0) := by
  obtain ⟨p, i, _, _, item, J⟩ := portItem_of_port hp o hP
  exact ⟨p, i, item, J.ins.plan, J.ins.window, J.ins.vocabulary, J.ins.built, J.request_bytes,
    J.reply_bytes, J.item_of, J.item_port, J.ins.range, J.ins.reply_zero⟩

end OnBytes.Flat
