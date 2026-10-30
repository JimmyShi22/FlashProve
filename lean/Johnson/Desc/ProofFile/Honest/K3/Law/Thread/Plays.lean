-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/Plays.lean: the honest side of the kind "lookup"
(K3). Conditional: the frame's sentence "it plays" (`Plays`, Honest/Thread/Pays.lean) at a member
of the first chain at whose place a lookup's seated row stands. General in the first chain's
letters. One structure; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number.

What is shown.
  `SeatedAt`: the hypotheses, all on public data and on the letters: which half stands at the
    member's place; the member's rounds and oracle messages; the lookup's numbers.
  `fresh_nil`: a member that states no oracle message brings no new tree.
  `stands_of_thr`: what the theorems on the lookup ask in front, from the thread and the challenges'
    test.
  `plays_look`: `Plays L.thread b`.
Of the thread in front the proof uses one clause alone: as many challenges were heard as there are
rounds in front. No summand is read; the sentence holds at all coins.

Hypotheses that remain.
  `hS`: `SeatedAt`. Its fields: half (the half that the chain's list of halves holds at the member's
    place is the lookup's), place, rounds, oracles, ok, entries, and base (the public number of
    rounds in front is the flat list's own).
  `hb`, `hA`, `hd`: (in `stands_of_thr`) blk is member number b; the thread holds in front; the
    challenges are such as the member's rounds can draw. `h`, `ho`: (in `fresh_nil`) blk is member
    number b; it states no oracle message.

Imported. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/SiteThr.lean and Honest/K3/Law/Thread/ToyLetters.lean
[not in this library] call `plays_look`; Honest/K3/Law/Thread/LeftThr.lean calls `stands_of_thr`;
Honest/K3/Law/Thread/AtThread.lean calls `fresh_nil`. By the import lines
Honest/K3/Law/Thread/Accepted.lean imports this file, and the others have it through that one.

`SeatedAt` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. An implication. No instance of these hypotheses is exhibited in this file. `Plays` is a form
of a hypothesis of the frame's: what follows from it is other files'.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Joined
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OneBlock
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3 (entriesFit)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type} (T : Thread Bk S Cl V W X Pb)

/-- **A member that states no oracle message brings no new tree.** -/
theorem fresh_nil {b : Nat} {blk : Block S Cl} (h : T.bs[b]? = some blk)
    (ho : blk.oracles.flatMap id = []) : T.fresh b = [] := by
  have e : treesTo T.bs (b + 1) = treesTo T.bs b := by
    rw [treesTo_succ h, ho]
    rfl
  unfold Thread.fresh Thread.hand
  rw [e]
  apply List.filter_eq_nil_iff.2
  intro σ hσ
  simp only [Bool.not_eq_true, Bool.not_eq_false']
  exact List.contains_iff_mem.2 hσ |>.symm ▸ rfl

end

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **A lookup's seated row stands at whatever member has the number b.** No field says that a
member stands at number b. Here a is the lookup's public data, J its summands, wit the seat's reader
of the input, and es the planner's entries. -/
structure SeatedAt (b : Nat) (a : At) (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj)
    (es : List Fmt.Entry) : Prop where
  /-- the half that the chain's list of halves holds at the member's place is the lookup's -/
  half : ∀ blk, L.bs[b]? = some blk → L.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a)
  place : ∀ blk, L.bs[b]? = some blk → blk.place = a.place
  rounds : ∀ blk, L.bs[b]? = some blk → blk.rounds = es.map declOf
  oracles : ∀ blk, L.bs[b]? = some blk → blk.oracles = es.map fun _ => []
  ok : a.face.ok = true
  entries : entriesFit a.face es = true
  /-- the public number of rounds in front is the flat list's own -/
  base : a.base = roundsTo L.bs b

variable {L}

/-- What the theorems on the lookup ask in front, from the thread and the challenges' test. -/
theorem stands_of_thr {b : Nat} {a : At} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj}
    {es : List Fmt.Entry} (hS : SeatedAt L b a J wit es) {blk : Block FS Cl}
    (hb : L.bs[b]? = some blk) {k : Coins Bk} {s : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}
    {ds : List Fmt.Drawn} (hA : Thr L.thread b k s m E) (hd : drawsFit blk.rounds ds = true) :
    Stands a es m ds :=
  ⟨hS.ok, (heard_of_thr L hA).trans hS.base.symm, hS.entries, by rw [← hS.rounds blk hb]; exact hd⟩

/-- **It plays**: the frame's sentence at member number b of the first chain: from the thread in
front, at every run's coins, at every list that the member's rounds can sample: the play and the
setting of the columns return (no column is read), and no new tree is owed. Conditional on
`SeatedAt`. No instance of these hypotheses is exhibited in this file. -/
theorem plays_look {b : Nat} {a : At} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj}
    {es : List Fmt.Entry} (hS : SeatedAt L b a J wit es) : Plays L.thread b := by
  intro blk hb k s m E ds l hA hd _ hl
  have hb' : L.bs[b]? = some blk := hb
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk L.hs _ (hS.half blk hb') l hl
  have hSt := stands_of_thr hS hb' hA hd
  obtain ⟨y, hy, _, _, _⟩ := movedInner _ _ _ _ a J wit blk.name
    (L.thread.φ.sees m.st.input) es m ds c 0 0 (fun _ _ => none) (fun _ => none) hSt
  have hy' : play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps blk (L.thread.φ.sees m.st.input) c) ds
    []
      m = .ok y := by
    rw [steps_eq a J wit _ es blk (hS.place blk hb') (hS.rounds blk hb') (hS.oracles blk hb') c]
    exact hy
  refine ⟨y, [], ⟨⟨_, hl, hy'⟩, ?_⟩, ?_⟩
  · rw [hS.rounds blk hb', readsOf_plain]
    rfl
  · rw [fresh_nil L.thread hb (by rw [hS.oracles blk hb']; simp)]
    intro σ hσ
    exact absurd hσ (List.not_mem_nil)

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.fresh_nil
#print axioms ProofFile.Honest.K3.Law.AtThr.stands_of_thr
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_look
