-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Idle.lean: THE GUARD ON THE REPLY: at a test that always says yes the guard is
nothing at all, and the first chain is the bare chain.

What the file is. The guard (Johnson/Desc/SeatGuard.lean) lays a test same behind every step of a
block, a segment or a chain: a step is refused if same says no of the states in front of it and
behind it. Here, for a test with hs : ∀ t s, same t s = true: a guarded segment is the segment, and
a guarded chain is the chain, AS STRUCTURES, field by field, not only by their flat lists. So the
driver's firstChain (Johnson/Desc/First/Driver/Chain.lean), which is firstChainWithoutReplyGuard behind the guard at
the structure's own test H.same, is firstChainWithoutReplyGuard where H.same always says yes: both are there or both
are not, and where they are there they are one chain. All is general in the state T and the claims'
type Cl.

Main names.
* bind_idle: a step that may refuse, with the idle test behind it, is the step.
* mapGuarded_idle: a list of blocks, each guarded, is the list.
* linkGuarded_idle: L.guarded same but = L.
* chainGuarded_idle: c.guarded same but = c.
* firstChain_idle: firstChain H links several = firstChainWithoutReplyGuard H links several.

What it leans on. Driver.lean: guarded_idle_self (every block is its own guarded form at such a
test). The library's definitions seatSame, Link.guarded, Chain.guarded
(Johnson/Desc/SeatGuard.lean) and firstChain (Johnson/Desc/First/Driver/Chain.lean). No proof is
carried from another file.

Limits. Every equation here is shown only for a test that always says yes. The test that the proof
file's seat lays compares the replies and can say no: of it nothing is said here. Nothing is shown
of any block of the protocol. Nothing on soundness.


-/
import Johnson.LPFGuard.Driver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference.Desc
open VerifiableInference.Desc.First

variable {T Cl : Type} {same : T → T → Bool}

/-- A step that may refuse, with the idle test behind it, is the step. -/
theorem bind_idle (hs : ∀ t s, same t s = true) (t : T) (x : Except String T) :
    x.bind (seatSame same t) = x := by
  cases x with
  | error e => rfl
  | ok s => exact if_pos (hs t s)

/-- A list of blocks, each guarded, is the list. -/
theorem mapGuarded_idle (hs : ∀ t s, same t s = true) (but : Place → Bool)
    (l : List (Block T Cl)) : l.map (Block.guarded same but) = l := by
  have e : Block.guarded (Cl := Cl) same but = id := funext fun b => guarded_idle_self hs but b
  rw [e, List.map_id]

/-- **A guarded segment is the segment**, as a structure. -/
theorem linkGuarded_idle (hs : ∀ t s, same t s = true) (but : Place → Bool) (L : Link T Cl) :
    L.guarded same but = L := by
  have h1 : (fun t => (L.lay t).bind (seatSame same t)) = L.lay :=
    funext fun t => bind_idle hs t _
  have h2 : (fun f => (L.batch f).guarded same but) = L.batch :=
    funext fun f => guarded_idle_self hs but _
  have h3 : (fun t => (L.clear t).bind (seatSame same t)) = L.clear :=
    funext fun t => bind_idle hs t _
  calc L.guarded same but
      = { L with lay := L.lay, hear := L.hear, batch := L.batch, close := L.close,
                 clear := L.clear } := by
        unfold Link.guarded
        rw [h1, h2, h3, mapGuarded_idle hs but L.hear, mapGuarded_idle hs but L.close]
    _ = L := rfl

/-- **A guarded chain is the chain**, as a structure. -/
theorem chainGuarded_idle (hs : ∀ t s, same t s = true) (but : Place → Bool) (c : Chain T Cl) :
    c.guarded same but = c := by
  have e : Link.guarded (Cl := Cl) same but = id := funext fun L => linkGuarded_idle hs but L
  calc c.guarded same but
      = { first := c.first, front := c.front, links := c.links, back := c.back,
          last := c.last } := by
        unfold Chain.guarded
        rw [e, List.map_id, guarded_idle_self hs but c.first, guarded_idle_self hs but c.last,
          mapGuarded_idle hs but c.front, mapGuarded_idle hs but c.back]
    _ = c := rfl

/-- **WHERE THE STRUCTURE's TEST ALWAYS SAYS YES THE FIRST CHAIN IS THE BARE CHAIN.** -/
theorem firstChain_idle (H : Blocks T Cl) (hs : ∀ t s, H.same t s = true) (links : List ModelPart)
    (several : Bool) : firstChain H links several = firstChainWithoutReplyGuard H links several := by
  unfold firstChain
  cases firstChainWithoutReplyGuard H links several with
  | none => rfl
  | some c => exact congrArg some (chainGuarded_idle hs hearsReply c)

#print axioms linkGuarded_idle
#print axioms chainGuarded_idle
#print axioms firstChain_idle

end LPFGuard
