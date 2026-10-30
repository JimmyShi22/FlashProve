-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/FirstL.lean: a key file's first chain with the two lookups' rounds written off
a list. General: no value is treated.

The block of a lookup (K3.lookupKind, Johnson/Desc/First/Look/K3LookupGeneral.lean) makes its rounds by the
planner's own routine (K3.entriesG), and its own test on the plan asks that the routine returns.
Lean's kernel did not get through that routine at the full size: asked whether K3.entriesG set .once
(K3.faceOfLkp x), which is Params.finish set .once (Params.planLookup ..) with the rounds' entries
taken, returns at both lookups, in one line, the kernel's check failed after 120 seconds; Lean could
not print its message; the cause is not shown. The line was not asked again with maxHeartbeats
lifted, nor at one lookup alone, nor cut finer: which routine beneath it stops the kernel is not
known. Here: where the routine returns the list L, the block IS the block whose rounds, oracle
messages and own test are written off L; so the link is that link, and the chain that chain.
Equations, by unfolding and rewriting.

Main names.
  firstChainL links: the text of Key.firstChain (Johnson/Desc/Key/Chain1.lean) with the list of
  links as a letter. firstChain_links: Key.firstChain is that, at its own links: by unfolding.
  lookBlock L, lookLink L, lookLinks look: the block, the link, the list of links, off lists.
  lookBlock_eq, lookLink_eq, lookLinks_eq: where K3.entriesG returns these lists.
  firstChain_look: so Key.firstChain one D told set N = firstChainL (lookLinks look one set) ...
Limits. That the routine returns is a premise. firstChainL copies eleven lines of Key.firstChain:
firstChain_links holds the copy against the original. Nothing on soundness.

-/
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params

/-- Key.firstChain's text with the links as a letter. -/
def firstChainL (links : List (Link FirstState Claim)) (one : OneTime) (D : List Fmt.DeclaredRound)
    (told : List ProofFile.Root) (N : H2U.PlaceNums) : Chain FirstState Claim :=
  let sent := rootsBefore D (batchRound D)
  let first : Block FirstState Claim := sendIndexMasks one pieces (groupsTold told 0 (rootsAt D 0))
  let front : List (Block FirstState Claim) :=
      [sendOwnMessage one pieces (groupsTold told (rootsBefore D 2) (rootsAt D 2))]
  let rng : Block FirstState Claim := rangesTest (enterRanges one) leaveRanges N
  let back₀ : List (Block FirstState Claim) :=
    [layRows one, rng, batchTableRows (·.keys) one pieces sent] ++
      (sendW one pieces sent
        (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D)))).toList
  let inFront : List (Block FirstState Claim) := first :: front ++ links.flatMap Link.blocksInOrder ++ back₀
  { first := first, front := front, links := links, back := back₀
    last := firstChainEnd pieces (inFront.flatMap (·.rounds)) }

theorem firstChain_links (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) :
    firstChain one D told set N =
      firstChainL ((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1) one D told N :=
  rfl

/-- A block is the block with three of its fields laid anew, where these are its own. -/
theorem block_upd {S Cl : Type} (b : Block S Cl) {A : Bool} {R : List Fmt.DeclaredRound}
    {O : List (List VerifiableInference.Desc.Oracle)} (h1 : b.planOk = A) (h2 : b.rounds = R)
    (h3 : b.oracles = O) :
    b = { b with planOk := A, rounds := R, oracles := O } := by
  subst h1 h2 h3
  rfl

/-- Lookup i's block with its rounds, oracle messages and own test written off the list L. -/
def lookBlock (L : List Fmt.Entry) (set : Setting) (i : Nat) (x : Lookup) :
    Block FirstState Claim :=
  { K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x) with
    planOk := (lookupPlace set i x).face.ok &&
      decide ((lookupPlace set i x).first + (lookupPlace set i x).face.slots ≤
        (lookupPlace set i x).ns)
    rounds := L.map fun e => { entry := e }
    oracles := L.map fun _ => [] }

theorem lookBlock_eq {L : List Fmt.Entry} {set : Setting} (i : Nat) {x : Lookup}
    (h : K3.entriesG set .once (K3.faceOfLkp x) = some L) :
    K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x) = lookBlock L set i x := by
  have hp : (lookupPlace set i x).entries = some L := h
  refine block_upd _ ?_ ?_ ?_
  · show K3.PG.planOk _ _ _ _ = _
    unfold K3.PG.planOk
    rw [hp]
    simp
  · show ((lookupPlace set i x).entries.getD []).map _ = _
    rw [hp]
    rfl
  · show ((lookupPlace set i x).entries.getD []).map _ = _
    rw [hp]
    rfl

/-- Lookup i's link with that block. -/
def lookLink (L : List Fmt.Entry) (one : OneTime) (set : Setting) (i : Nat) (x : Lookup) :
    Link FirstState Claim :=
  { lookupLink one set i x with hear := [caller one i x, lookBlock L set i x] }

theorem lookLink_eq {L : List Fmt.Entry} (one : OneTime) {set : Setting} (i : Nat) {x : Lookup}
    (h : K3.entriesG set .once (K3.faceOfLkp x) = some L) :
    lookupLink one set i x = lookLink L one set i x := by
  unfold lookLink
  rw [← lookBlock_eq i h]
  rfl

/-- The links, each lookup's rounds off look. -/
def lookLinks (look : Lookup → List Fmt.Entry) (one : OneTime) (set : Setting) :
    List (Link FirstState Claim) :=
  (lookupsOf one).zipIdx.map fun x => lookLink (look x.1) one set x.2 x.1

theorem map_zipIdx_congr {α β : Type} (f g : α × Nat → β) :
    ∀ (l : List α) (k : Nat), (∀ x ∈ l, ∀ i, f (x, i) = g (x, i)) →
      (l.zipIdx k).map f = (l.zipIdx k).map g
  | [], _, _ => rfl
  | a :: l, k, h => by
    simp only [List.zipIdx_cons, List.map_cons]
    rw [h a (by simp) k, map_zipIdx_congr f g l (k + 1) fun x hx i => h x (by simp [hx]) i]

theorem lookLinks_eq {look : Lookup → List Fmt.Entry} {one : OneTime} {set : Setting}
    (h : ∀ x ∈ lookupsOf one, K3.entriesG set .once (K3.faceOfLkp x) = some (look x)) :
    ((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1) = lookLinks look one set :=
  map_zipIdx_congr _ _ _ 0 fun x hx i => lookLink_eq one i (h x hx)

/-- **Where the planner's routine returns look x at each lookup x, the first chain is the chain
with the lookups' rounds written off look.** -/
theorem firstChain_look {look : Lookup → List Fmt.Entry} {one : OneTime} {set : Setting}
    (h : ∀ x ∈ lookupsOf one, K3.entriesG set .once (K3.faceOfLkp x) = some (look x))
    (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (N : H2U.PlaceNums) :
    firstChain one D told set N = firstChainL (lookLinks look one set) one D told N := by
  rw [firstChain_links, lookLinks_eq h]

end Johnson.KB4

#print axioms Johnson.KB4.firstChain_links
#print axioms Johnson.KB4.block_upd
#print axioms Johnson.KB4.lookBlock_eq
#print axioms Johnson.KB4.lookLink_eq
#print axioms Johnson.KB4.map_zipIdx_congr
#print axioms Johnson.KB4.lookLinks_eq
#print axioms Johnson.KB4.firstChain_look
