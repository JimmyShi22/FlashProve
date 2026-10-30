-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Falls.lean: K9's FALL AS A STRUCTURE OF THE FRAME's (`Fall`, Honest/Side.lean), AT THE
MEMBER THAT REFUSES, AT EVERY SEGMENT. Definitions with code and `#guard` lines; no theorem. No goal is stated.

The frame joins the falls at one place (`fallOf`: the first that says something): so each kind types its own
`Fall` at that member's place. This file has K9's.
  `quietFall p n top notGood`   the `Fall`: place := `quietPlace p` (Honest/K9/Quiet.lean): the frame's member behind
                        the batching · test := K9's "free-slot" on the state in front of that member
                        (`freeSlotShare n`, Honest/K9/Fall.lean): it reads no challenge · share := TWO STATED NUMBERS
                        ADDED: n * top of the extension field's size (`batFallShare`), and `notGood`
  `quietFallsBy xs nums notGood`, `quietFallsAt xs X notGood`, `quietFalls Z notGood`   one `Fall` for each segment at
                        which K9's lot lays a batching with a round and the numbers are there: the place off the
                        lot's own reading (`k9Links`, `k9Where`), the numbers off `K9.testsWhere`, as `k9Tests` reads
                        them
  `fallAtQuiet p test share`   FOR ANOTHER KIND's `Fall` AT THE SAME MEMBER: the place laid for it; test and share are
                        that kind's
THE SHARE. The frame means by a fall's share the chance over THE WHOLE LIST OF CHALLENGES. K9's count is cut in two:
(1) at a state that is good at most n * top FIELD ELEMENTS fall as chi. What bounds that: `quiet_few_good`
(Honest/K9/QuietMore.lean) at the decision; at the seated block's step, and under a "good" that holds no yes and no
length (`goodW`): `gate_few_weak` (Honest/K9/GateArms.lean). Their number is the LEDGER's plan's number of claims less
1; `top` here is read off the PUBLIC PARAMETERS': two readings of the plan, tied nowhere yet. AND WHETHER n * top OF
THE FIELD's SIZE IS A NUMBER THAT CAN BE HELD HANGS ON THE LIBRARY's KIT OF CHALLENGES: a round's challenge is no
field element by type. At the kit of typed values (three residues) at most one challenge shows as one element, and the
form can stand as it is; at the kit of hash blocks, shown through a sampler, many do, and the number turns by a factor
that bounds how many (`gate_of_count`, `gate_of_count_blocks`, Johnson/P1K8R/GateOfCount.lean).
The one rule of the frame's that names a kit names the second: so no such number is quoted here as held.
(2) THE CHANCE THAT THE STATE IN FRONT OF THE BATCHING IS NOT GOOD: at which earlier challenges a slot's coefficient
is the zero polynomial in chi. (By the head of Johnson/Desc/First/Door/Sums.lean the ledger's coefficients are made,
at a layers' link, also of values that the prover has SENT. Whether some slot's LIVENESS hangs on such a value we have
not traced; a reader of the frame's house has walked it: a sent factor stands in weights on entries, in no coefficient
on a slot.)
(2) IS NOT K9's TO COUNT: each kind knows its own slots' coefficients: it is an event of the OTHER kinds' draws, at
which the verifier refuses nothing. So it is a LETTER here, `notGood`: whoever lays the `Fall` lays the kinds' numbers
for the segment, added. IT HAS NO PAYER YET. WITH notGood := 0 of 1 THE SHARE IS TOO SMALL AS THE FRAME MEANS IT. (The
frame's keepers are laying a structure of its own for such an event's number, paid once; then this letter can go.)
K4's own "free-slot" at the same member: its `Fall` is K4's house's. At K9's own number of slots its event lies inside
K9's (`k4Share_silent`, Honest/K9/Quiet.lean): so there its `Fall` may state 0 of 1; a second n * top would count the
event twice.
STATED NUMBERS; nothing in this file holds them against the test.
Limits. No line runs `quietFallsAt` or `quietFalls`: they want the verifier's public parameters. Where two K9 places
with steps stood at one segment (that there is none in the description is not shown), `k9Links` would list the segment
twice, and two equal `Fall`s would state the share twice. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Quiet
import Johnson.Desc.ProofFile.Honest.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Where)

/-- **K9's fall at the member behind the batching.** n: the slots that the segment's messages fill. top: the
highest power of chi under which a claim that names a slot is added. notGood: THE STATED CHANCE THAT THE STATE IN
FRONT OF THE BATCHING IS NOT GOOD: the kinds' numbers for their own slots, added: NOT K9's to count; it has no payer
yet. -/
def quietFall (p : Where) (n top : Nat) (notGood : Odds) : Fall S :=
  { place := quietPlace p
    test := fun s _ => freeSlotShare n s
    share := (batFallShare n top sizeOfE).plus notGood }

/-- One `Fall` for each segment. xs: the places that have rounds, with their stretches (`k9Stretches`). nums: a
segment's two numbers (n, top). notGood: a segment's stated chance. -/
def quietFallsBy (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (nums : Nat → Option (Nat × Nat))
    (notGood : Nat → Odds) : List (Fall S) :=
  (k9Links xs).filterMap fun l =>
    (k9Where xs l).bind fun p => (nums l).map fun w => quietFall p w.1 w.2 (notGood l)

/-- The numbers off the verifier's public parameters. -/
def quietFallsAt (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (X : OnBytes.Model.Verify.Public)
    (notGood : Nat → Odds) : List (Fall S) :=
  quietFallsBy xs
    (fun l => (VerifiableInference.Desc.K9.testsWhere X l 0).map fun w => (w.2.2.filled, w.2.1 - 1)) notGood

/-- At a public part. -/
def quietFalls (Z : Pub) (notGood : Nat → Odds) : List (Fall S) :=
  quietFallsAt (k9Stretches Z) Z.p.X notGood

/-- For another kind's `Fall` at the same member. -/
def fallAtQuiet (p : Where) (test : S → Option String) (share : Odds) : Fall S :=
  { place := quietPlace p, test := fun s _ => test s, share := share }

namespace Toy

/-- The toy's fall: two slots; the plan has two claims; the second number laid as 0 of 1. -/
def fallT : Fall S := quietFall pw 2 1 ⟨0, 1⟩

-- its share has a denominator, and is the first number where the second is 0 of 1; the second is added
#guard fallT.share.ok && fallT.share == ⟨2, sizeOfE⟩
#guard (quietFall pw 2 1 ⟨3, sizeOfE⟩).share == ⟨2 * sizeOfE + 3 * sizeOfE, sizeOfE * sizeOfE⟩
-- THE FRAME's OWN READER OF FALLS, along the toy's flat list from the state in front of the batching: at chi = 1
-- it meets the fall AT THE DESCRIPTION's OWN MEMBER BEHIND THE BATCHING, under K9's name; at chi = 5 it meets none
#guard chainFall [fallT] 0 (bs.drop 2) (sD held) { rounds := [⟨[], dE 1⟩], opened := [] }
  == some ((at_ 3).place, "K9.free-slot")
#guard chainFall [fallT] 0 (bs.drop 2) (sD held) { rounds := [⟨[], dE 5⟩], opened := [] } == none
-- over 24 values: the frame's reader meets the fall just where that member refuses
#guard (List.range 24).all fun c =>
  (chainFall [fallT] 0 (bs.drop 2) (sD held) { rounds := [⟨[], dE c.toUInt64⟩], opened := [] }).isSome
    == (((behind held c.toUInt64).toOption.map fun s₁ =>
      ((at_ 3).decide s₁ [] []).toOption.isNone).getD false)
-- seated one place off, nothing ever asks it (a control on the frame's reader)
#guard chainFall [{ fallT with place := (at_ 4).place }] 0 (bs.drop 2) (sD held)
  { rounds := [⟨[], dE 1⟩], opened := [] } == none
-- two kinds' `Fall`s at one member are joined: the first that says something speaks
#guard (behind held 5).toOption.map (fun s₁ =>
  fallOf [fallT, fallAtQuiet pw (fun _ => some "another's") ⟨1, 2⟩] (at_ 3).place s₁ [])
    == some (some "another's")
#guard (behind held 1).toOption.map (fun s₁ =>
  fallOf [fallT, fallAtQuiet pw (fun _ => some "another's") ⟨1, 2⟩] (at_ 3).place s₁ [])
    == some (some "K9.free-slot")
-- the list over the toy's places: one `Fall`, the toy's; none where the numbers are lacking
#guard (quietFallsBy spots (fun _ => some (2, 1)) fun _ => ⟨0, 1⟩).map (fun f => (f.place, f.share))
  == [(fallT.place, fallT.share)]
#guard (quietFallsBy spots (fun _ => none) fun _ => ⟨0, 1⟩).isEmpty

end Toy

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.quietFall
#print axioms ProofFile.Honest.K9.quietFallsBy
#print axioms ProofFile.Honest.K9.quietFallsAt
#print axioms ProofFile.Honest.K9.quietFalls
#print axioms ProofFile.Honest.K9.fallAtQuiet
#print axioms ProofFile.Honest.K9.Toy.fallT
