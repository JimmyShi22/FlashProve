-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/SendsFrom.lean: the sendings of the seven chains as a function of what the planner has
made (Params.Configured), and that Johnson.G.sendsOf (Johnson/G/Sends.lean) is that function behind
the program's planner.

sendsOf takes the three public files, calls Model.Verify.planned on them, and reads of what that
returns the made record alone. It has no form that starts from a value of the planner. Here is one.

Main names.
  sendsFrom     sendsOf's text behind its first two lines, at a made record c.
  sendsOf_eq    sendsOf pol lay KL = planned pol KL (some lay) >>= fun p => sendsFrom p.chains.made.
  sendsOf_of    so, where the planner returns p, sendsOf returns what sendsFrom p.chains.made does.

Limits. sendsFrom is a second text of sendsOf's lines; sendsOf_eq proves, by unfolding, that it is
the same; it will have to be turned with sendsOf. The limits of Johnson/G/Sends.lean hold. Nothing
on soundness.

-/
import Johnson.G.Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params

/-- The sendings of the seven chains, from what the planner has made. -/
def sendsFrom (c : Configured) : Except String (List ChainSends) := do
  let z := c.sized
  let a := z.set.samples
  let one (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
      Except String ChainSends := do
    let R := P.rounds.toArray
    let seeds := P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed"
    unless seeds.length == l.length do
      throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
    let out ← (seeds.zip l).mapM fun (r, s) => do
      unless treesOf codes s.sent.toArray == some r.1.entry.roots do
        throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
      match R[r.2 + 1]? with
      | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
      | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
    pure ⟨file, ch, codes, out⟩
  let K := z.key.once.shape
  let B := z.proof.batch.shape
  let x := z.key.ranges.x
  match c.key, c.proof with
  | [k0, k1, k2], [p0, p1, p2] =>
    [ one "key" 0 z.key.codes
        ([⟨"the index-mask message", [z.key.once.input]⟩,
          ⟨"the multiplicities", (Wf.messageOf x).toList⟩] ++
          ioppSends "the ranges' test" a x.choice.masksRide 1 x.stages ++ [← wSend K]) k0,
      one "key" 1 z.key.codes (← linSharedSends K a) k1,
      one "key" 2 z.key.codes (ioppSends "the own test" a K.choice.masksRide 1 K.testOwn) k2,
      one "entry" 0 z.entryCodes
        (⟨"the link's message", (linkMessage z.link.shape a).toList⟩ ::
          ioppSends "the link's test" a z.link.shape.choice.masksRide 1 z.link.shape.test) c.entry,
      one "proof" 0 z.proof.codes
        (frameSends z.proof a 0 (reqGroups z.proof.request).toList z.proof.request.link ++
          [← wSend B]) p0,
      one "proof" 1 z.proof.codes (← linSharedSends B a) p1,
      one "proof" 2 z.proof.codes (ioppSends "the own test" a B.choice.masksRide 1 B.testOwn) p2
    ].mapM id
  | _, _ => throw "the key or the proof has not three plans"

/-- **sendsOf is sendsFrom behind the program's planner.** -/
theorem sendsOf_eq (pol lay KL : ByteArray) : sendsOf pol lay KL =
    OnBytes.Model.Verify.planned pol KL (some lay) >>= fun p => sendsFrom p.chains.made := rfl

/-- Where the planner returns p, sendsOf returns what sendsFrom returns at what p has made. -/
theorem sendsOf_of {pol lay KL : ByteArray} {p : OnBytes.Model.Verify.Planned}
    (h : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p) :
    sendsOf pol lay KL = sendsFrom p.chains.made := by
  rw [sendsOf_eq, h]
  rfl

end Johnson.G

#print axioms Johnson.G.sendsOf_eq
#print axioms Johnson.G.sendsOf_of
