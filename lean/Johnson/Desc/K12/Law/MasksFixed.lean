-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/MasksFixed.lean: one proposition on the plan of a proximity test: which message
each tree is that the first switch opens, and which written rounds send a tree; and what it pays.

A law on a fold with a mask asks that the mask's word is fixed before the fold's first draw. In the
library's typed chain that holds by the type: a later stage's words are functions of the switch's
first message, the first stage's are letters outside the game (or, for the first fold's own mask, a
function of the chain's first message). What whoever spends the law in a game still owes is which
message each opened tree is. MasksFixed says it, on the plan alone, by equations. Definitions,
statements and proofs.
Main names:
  `InFront p src`: the declared source stands in front of the test: an own tree below the plan's
    count of roots in front of "BAT", or a tree of another chain; and "before" names it. (At an own
    tree the half "before names it" is spent by no corollary here: it is kept for the law of
    beforeAt.)
  `MasksFixed p`: four fields. ownN: the test sends one tree beside its switches' where the first
    fold sends its own mask, else none. own: that tree is told as the chain's own number free. made:
    there are at least two stages; the written rounds are there; WShape (TreesMade.lean): of a
    fold's and a switch's written rounds just the switch's first sends a tree, and the first fold's
    first where it sends its own mask; what the first switch opens is the plan's list nums.first and
    then the own mask's tree. front: each tree of nums.first stands in front of the test, or is the
    own mask's tree itself.
  `front_of_fixed`: the field front from `fixedOk` (Johnson/Desc/K12/FixedBefore.lean), by
    `fixed_switch` at j = 0 (FixedLaw.lean).
  `masksFixed_made`: MasksFixed from: the numbers give rounds; as many lists of oracle messages;
    sizesOk's walk; fixedOk.
  `not_masksFixed_of_late`, `not_masksFixed_of_empty`: two plans that have not MasksFixed: one that
    reads a tree which the test sends behind the first fold's first round as one of the first
    stage's trees; one with "before" emptied.
The corollaries, in plain letters: the definitions of Johnson/Desc/K12/Coin/Sheet.lean
and Johnson/Desc/K12/Coin/OwnArm.lean are unfolded here by hand.
  `inFront_below`, `opening_of`: tools: what stands in front has a number below the stretch's first,
    under the pins; a place of D.ts has its number from a declared opening of the first switch.
  `MasksFixed.own0`, `own1`: AtPlace.own0, AtPlaceOwn.own1.
  `MasksFixed.trees`: AtPlace.trees, at every letters X. `MasksFixed.treesOwn`: AtPlaceOwn.trees,
    with TreesOwnP for TreesOwn.
  `MasksFixed.firstOpens2`: the second clause of FirstOpens (∀ z ∈ D.ts, no z < base) from its
    first, under two pins on num.
  `MasksFixed.freshBase`: the third clause of FirstOpensOwn (no D.fresh.t = base) from its first,
    under numOwn and "the last of D.ts is D.fresh.t" (the binder hlast here: it is not the library's
    premise of that name, "a word fixed before the block", nor lastOk).
  `MasksFixed.membersBelow`: every other place of D.ts has no z < base (the second clause of
    FirstOpensOwn wants this at the members' places), under the three pins and inj.
Limits: "which tree a later stage opens" is not a field: it is dealOk's clause src (DealMade.lean: a
theorem). The pins n2 (n < free → num (.own n) < base) and n3 ((c + 1, n) ∈ before → num (.taken c
n) < base) are premises: at numAt n2 follows from the one equation numAt … (.own free) = base; n3 is
the law of beforeAt (Johnson/Desc/Block.lean), which is proved nowhere. The first clause of
FirstOpens (the book against the plan) is a premise. Where the first fold sends its own mask, a
member that shares the own mask's tree is barred at the record (`aloneAt_of_step_own`,
OwnMaskStep.lean: from the step's yes under ownMask = true: no member stands at the mask's place of
the book), not on the plan: fixedOk lets a member of nums.first with the source "own", number free,
by; so membersBelow takes inj (no z = no D.fresh.t → z = D.fresh.t on D.ts), which is paid nowhere
as it stands; it is a clause on the plan in disguise. No soundness is claimed, and nothing is said
on hiding.
-/
import Johnson.Desc.K12.Law.TreesMade
import Johnson.Desc.K12.Law.FixedLaw

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.First
open H2K.FixedBefore (fixedOk Fixed fixed_switch foldStart sentIn)
open H2K.Pub (WR writtenOf chainFrom Letters sgOf)

/-- A declared source stands in front of the test, and «before» names it. -/
def InFront (p : P12) : Fmt.TreeSource → Prop
  | .own n => n < p.nums.free ∧ (p.place.chain, n) ∈ p.before
  | .taken c n => (c + 1, n) ∈ p.before

/-- **Which message each tree is that the test's first switch opens, and which written rounds send a
tree.** -/
structure MasksFixed (p : P12) : Prop where
  ownN : ownN p = if p.nums.ownMask then 1 else 0
  own : p.nums.ownMask = true → ∃ x W, ownTold p.nums = [p.nums.own x W p.nums.free]
  made : ∃ a b rest w0 w, p.nums.stages = a :: b :: rest ∧ writtenOf p.nums = some (w0 :: w) ∧
    WShape ((ownTold p.nums).map (·.1)).head? (b :: rest) a w ∧
    opensOf p a.k = p.nums.first ++ ownTold p.nums
  front : ∀ o ∈ p.nums.first, InFront p o.2 ∨ (p.nums.ownMask = true ∧ o.2 = .own p.nums.free)

/-- The field front, from fixedOk. -/
theorem front_of_fixed (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (hfx : fixedOk p = true) :
    ∀ o ∈ p.nums.first, InFront p o.2 ∨ (p.nums.ownMask = true ∧ o.2 = .own p.nums.free) := by
  obtain ⟨s, next, rest, R', hs, _, hrds⟩ := rounds_head p.nums rds hr
  have hF := fixed_switch p hfx rds hr 0 s (by rw [hs]; simp) (by rw [hs]; rfl)
  have h0 : foldStart 1 p.nums.stages 0 = 1 := by simp [foldStart]
  rw [h0] at hF
  have hcut : (rds.drop (1 + 1 + s.k)).take 2 = [⟨(rSeed next).entry, [], []⟩,
      ⟨(rCs p.nums.work s 0 0).entry, [],
        p.nums.first ++ (if p.nums.ownMask then (told p.nums).take 1 else [])⟩] := by
    have e : 1 + 1 + s.k = (1 + s.k) + 1 := by omega
    rw [hrds, e, List.drop_succ_cons, List.drop_left' (by simp [Nat.add_comm])]
    rfl
  have hsent : sentIn p.nums rds (1 + 1) = p.nums.free + if p.nums.ownMask then 1 else 0 := by
    unfold sentIn
    rw [hrds]
    show p.nums.free + (0 + ((epsE p.nums.ownMask false).roots + 0)) = _
    rw [epsE_roots]
    simp
  intro o ho
  have hf := hF ⟨(rCs p.nums.work s 0 0).entry, [],
    p.nums.first ++ (if p.nums.ownMask then (told p.nums).take 1 else [])⟩ (by rw [hcut]; simp) o
    (List.mem_append_left _ ho)
  obtain ⟨sh, src⟩ := o
  cases src with
  | own n =>
    have hf' : (n < p.nums.free ∧ (p.place.chain, n) ∈ p.before) ∨
        (p.nums.free ≤ n ∧ n < sentIn p.nums rds (1 + 1)) := hf
    rw [hsent] at hf'
    rcases hf' with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · cases hm : p.nums.ownMask
      · rw [hm] at h2
        simp at h2
        omega
      · rw [hm] at h2
        simp at h2
        exact Or.inr ⟨rfl, by show Fmt.TreeSource.own n = _; congr 1; omega⟩
  | taken c n => exact Or.inl hf

/-- **MasksFixed**, from the numbers and two tests on the plan. -/
theorem masksFixed_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (hlen : p.oracles.length = rds.length)
    (answers : Nat) (hS : stagesOk answers none p.nums.stages = true) (hfx : fixedOk p = true) :
    MasksFixed p := by
  obtain ⟨a, rest, w0, w, hs, hw, _, _, _, h5, h6⟩ := written_made p rds hr hlen
    fun s hs => (stages_of_ok answers _ none hS s hs).2
  obtain ⟨s, next, rest', _, hs', _, _⟩ := rounds_top p.nums rds hr
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  exact ⟨ownN_eq p a next rest' hs, h6,
    ⟨a, next, rest', w0, w, hs, hw, shape_made p rds hr answers hS a _ hs w0 w hw, h5⟩,
    front_of_fixed p rds hr hfx⟩

namespace MasksFixed
variable {p : P12}

/-- AtPlace.own0. -/
theorem own0 (h : MasksFixed p) (ho : p.nums.ownMask = false) : H2K.First.ownN p = 0 := by
  rw [h.ownN, ho]
  rfl

/-- AtPlaceOwn.own1. -/
theorem own1 (h : MasksFixed p) (ho : p.nums.ownMask = true) : H2K.First.ownN p = 1 := by
  rw [h.ownN, ho]
  rfl

/-- AtPlace.trees, at every letters. -/
theorem trees (h : MasksFixed p) (ho : p.nums.ownMask = false) (X : Letters) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : OnBytes.Slice.Chain (sgOf a))
    (hs : p.nums.stages = a :: rest) (hw : writtenOf p.nums = some (w0 :: l))
    (hc : chainFrom X rest a l = some c) : c.Trees := by
  obtain ⟨a', b, rest', w0', w', hs', hw', hW, _⟩ := h.made
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  obtain ⟨_, rfl⟩ := List.cons.inj (Option.some.inj (hw.symm.trans hw'))
  have e : ((ownTold p.nums).map (·.1)).head? = none := by simp [ownTold, ho]
  rw [e] at hW
  exact trees_of_shape X _ a l c hW hc

/-- AtPlaceOwn.trees, with TreesOwnP for TreesOwn. -/
theorem treesOwn (h : MasksFixed p) (ho : p.nums.ownMask = true) (X : Letters)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR)
    (c : OnBytes.Slice.Chain (sgOf a)) (hs : p.nums.stages = a :: rest)
    (hw : writtenOf p.nums = some (w0 :: l)) (hc : chainFrom X rest a l = some c) :
    TreesOwnP c := by
  obtain ⟨a', b, rest', w0', w', hs', hw', hW, _⟩ := h.made
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  obtain ⟨_, rfl⟩ := List.cons.inj (Option.some.inj (hw.symm.trans hw'))
  obtain ⟨x, W, hx⟩ := h.own ho
  rw [hx] at hW
  exact treesOwn_of_shape X _ b rest' a l c hW hc

/-- What stands in front of the test has a number below the stretch's first. -/
theorem inFront_below (num : Fmt.TreeSource → Nat) (base : Nat)
    (n2 : ∀ n, n < p.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ p.before → num (.taken c n) < base) (src : Fmt.TreeSource)
    (h : InFront p src) : num src < base := by
  cases src with
  | own n => exact n2 n h.1
  | taken c n => exact n3 c n h

/-- A place of D.ts has its number from a declared opening of the first switch. -/
theorem opening_of (h : MasksFixed p) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (num : Fmt.TreeSource → Nat) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no) (z : Nat)
    (hz : z ∈ D.ts) : ∃ o ∈ p.nums.first ++ ownTold p.nums, num o.2 = no z := by
  obtain ⟨a', b, rest', _, _, hs', _, _, ho⟩ := h.made
  obtain ⟨rfl, _⟩ := List.cons.inj (hs.symm.trans hs')
  have hm : no z ∈ D.opens.map (fun o => num o.2) := by
    rw [h1]
    exact List.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨o, ho', e⟩ := List.mem_map.1 hm
  rw [hD, ho] at ho'
  exact ⟨o, ho', e⟩

/-- The second clause of FirstOpens, from its first. -/
theorem firstOpens2 (h : MasksFixed p) (ho : p.nums.ownMask = false) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) (num : Fmt.TreeSource → Nat)
    (base : Nat) (n2 : ∀ n, n < p.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ p.before → num (.taken c n) < base) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no) :
    ∀ z ∈ D.ts, no z < base := by
  intro z hz
  obtain ⟨o, hm, e⟩ := h.opening_of a rest hs num D no hD h1 z hz
  have hn : ownTold p.nums = [] := by simp [ownTold, ho]
  rw [hn, List.append_nil] at hm
  rw [← e]
  rcases h.front o hm with hf | ⟨h2, _⟩
  · exact inFront_below num base n2 n3 _ hf
  · rw [ho] at h2
    cases h2

/-- The third clause of FirstOpensOwn, from its first. -/
theorem freshBase (h : MasksFixed p) (ho : p.nums.ownMask = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) (num : Fmt.TreeSource → Nat)
    (base : Nat) (n1 : ∀ n, num (.own (p.nums.free + n)) = base + n) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no)
    (hlast : D.ts.getLast? = some D.fresh.t) : no D.fresh.t = base := by
  obtain ⟨a', b, rest', _, _, hs', _, _, hop⟩ := h.made
  obtain ⟨rfl, _⟩ := List.cons.inj (hs.symm.trans hs')
  obtain ⟨x, W, hx⟩ := h.own ho
  have e := congrArg List.getLast? h1
  rw [List.getLast?_map, List.getLast?_map, hlast, hD, hop, hx, List.getLast?_concat] at e
  have e' : num (.own p.nums.free) = no D.fresh.t := Option.some.inj e
  rw [← e']
  exact n1 0

/-- Every other place of D.ts has a number below the stretch's first. -/
theorem membersBelow (h : MasksFixed p) (ho : p.nums.ownMask = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) (num : Fmt.TreeSource → Nat)
    (base : Nat) (n1 : ∀ n, num (.own (p.nums.free + n)) = base + n)
    (n2 : ∀ n, n < p.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ p.before → num (.taken c n) < base) (D : Plain) (no : Nat → Nat)
    (hD : D.opens = opensOf p a.k) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no)
    (hlast : D.ts.getLast? = some D.fresh.t)
    (inj : ∀ z ∈ D.ts, no z = no D.fresh.t → z = D.fresh.t) :
    ∀ z ∈ D.ts, z ≠ D.fresh.t → no z < base := by
  intro z hz hne
  have hb := h.freshBase ho a rest hs num base n1 D no hD h1 hlast
  have hfree : num (.own p.nums.free) = base := n1 0
  obtain ⟨o, hm, e⟩ := h.opening_of a rest hs num D no hD h1 z hz
  obtain ⟨x, W, hx⟩ := h.own ho
  rw [hx] at hm
  rcases List.mem_append.1 hm with hm | hm
  · rcases h.front o hm with hf | ⟨_, h2⟩
    · rw [← e]
      exact inFront_below num base n2 n3 _ hf
    · rw [h2, hfree, ← hb] at e
      exact absurd (inj z hz e.symm) hne
  · obtain rfl := List.mem_singleton.1 hm
    have e2 : num (.own p.nums.free) = no z := e
    rw [hfree, ← hb] at e2
    exact absurd (inj z hz e2.symm) hne

end MasksFixed

/-- (s1) A SILLY MEMBER: a plan that reads a tree which the test sends behind the first fold's first
round as one of the first stage's trees has not MasksFixed. -/
theorem not_masksFixed_of_late (p : P12) (sh : Fmt.Shape) (n : Nat)
    (h : (sh, Fmt.TreeSource.own (p.nums.free + (n + 1))) ∈ p.nums.first) : ¬ MasksFixed p := by
  intro hM
  rcases hM.front _ h with hf | ⟨_, h2⟩
  · have : p.nums.free + (n + 1) < p.nums.free := hf.1
    omega
  · have : p.nums.free + (n + 1) = p.nums.free := Fmt.TreeSource.own.inj h2
    omega

/-- (s2) A SILLY MEMBER: with «before» emptied, a plan that names a tree for its first stage and
sends no mask of its own has not MasksFixed. -/
theorem not_masksFixed_of_empty (p : P12) (hb : p.before = []) (ho : p.nums.ownMask = false)
    (o : Fmt.Shape × Fmt.TreeSource) (h : o ∈ p.nums.first) : ¬ MasksFixed p := by
  intro hM
  rcases hM.front o h with hf | ⟨h2, _⟩
  · obtain ⟨sh, src⟩ := o
    cases src with
    | own n =>
      have : (p.place.chain, n) ∈ p.before := hf.2
      rw [hb] at this
      cases this
    | taken c n =>
      have : (c + 1, n) ∈ p.before := hf
      rw [hb] at this
      cases this
  · rw [ho] at h2
    cases h2

end H2K.Made

#print axioms H2K.Made.masksFixed_made
#print axioms H2K.Made.MasksFixed.own0
#print axioms H2K.Made.MasksFixed.own1
#print axioms H2K.Made.MasksFixed.trees
#print axioms H2K.Made.MasksFixed.treesOwn
#print axioms H2K.Made.MasksFixed.firstOpens2
#print axioms H2K.Made.MasksFixed.freshBase
#print axioms H2K.Made.MasksFixed.membersBelow
#print axioms H2K.Made.not_masksFixed_of_late
#print axioms H2K.Made.not_masksFixed_of_empty
