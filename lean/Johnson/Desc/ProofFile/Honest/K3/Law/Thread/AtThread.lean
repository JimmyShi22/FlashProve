-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtThread.lean: the honest side of the kind "lookup"
(K3). Conditional: two of the sentences that the frame lists as owed at a member, at a lookup's
member, with the thread a variable: `Plays T b` and `Accepted T fall b`
(Honest/Thread/Pays.lean), at every letter fall. Every fact on the thread's letters that the
proofs use is a field of one structure of hypotheses, `K3Seated`. One structure; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: T is a thread's structure of letters (`Thread`,
Honest/Thread/Thr.lean), and b is the member's number. The join is the statement `JoinedAt`
(Honest/K3/Law/Joined.lean).

What is shown.
  `K3Seated`: the hypotheses, by name.
  `plays_k3`: `K3Seated T b …` gives `Plays T b`. The proof does not use the field joins.
  `stepped_k3`: what the member's step has left is the state of which the field joins speaks.
  `accepted_k3`: `K3Seated T b …` gives `Accepted T fall b`, at every fall.
  `seated_of_look`: at the first chain's thread the structure follows from `SeatedAt`
    (Honest/K3/Law/Thread/Plays.lean) and `JoinsAt` (Honest/K3/Law/Thread/Accepted.lean).

Hypotheses that remain: the fields of `K3Seated`.
  half: the list of halves holds the lookup's seated row at the member's place.
  place, rounds, oracles: the member stands at the lookup's place, and its rounds and oracle
    messages are those of the planner's entries.
  ok, entries: two tests with code on public data.
  base: the lookup's public number of rounds in front is the thread's.
  joins: from the thread in front, at all coins that the row can be lent: the seat's reader finds a
    ledger in the state, and the row's play, the hearing from that ledger and the member's own step
    go through together (`JoinedAt`).
Which letters of the thread are read: bs (the member), hs (the half at the member's place), front
(how many challenges stand in front of the chain), φ (what the parts see of the input), chain and
ft. Not read by these proofs: form, formP, means, table, fixed, keeps, rides, wit, stored, valid;
they come in where the field joins is shown.
By name: `hS`: `K3Seated`. In `stepped_k3` besides: `hb`, `hA`, `hd`, `hSt`: blk is member number b;
the thread holds in front; the challenges are such as the member's rounds can draw; the member's
step has been taken. In `seated_of_look`: `hS`, `hJ`: `SeatedAt` and `JoinsAt`
(Honest/K3/Law/Thread/Plays.lean, Honest/K3/Law/Thread/Accepted.lean).

Imported. Files under Honest/Thread/.

How the proof goes. The texts are those of Plays.lean and Accepted.lean, with the thread's letters
for the first chain's.

Users. Honest/K3/Law/Thread/AtThreadSite.lean and Honest/K3/Law/Thread/AtThreadBridges.lean
[not in this library] call `plays_k3` and `accepted_k3`; AtThreadBridges.lean [not in this library]
calls `seated_of_look`; Honest/K3/Law/Thread/PlaysAnyState.lean imports this file.

`K3Seated` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]).
A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term
there: no file shows the field at such a lot, so the theorems of this file that bear it cannot be
called there as they stand.
Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. `accepted_k3` is a lemma; it does not show what is owed: the field joins holds the member's
own accepting step, and this theorem only takes it out. AtThreadSite.lean shows that field at a
description's own member. `Plays` and `Accepted` are two of the sentences that
Honest/Thread/Pays.lean lists as owed at a member of a chain; they are forms of hypotheses of the
frame's. The acceptance is said at any summands: it says nothing on values.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.Accepted

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV entriesFit)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {Cl V W X Pb Wj : Type} (T : Thread Bk FS Cl V W X Pb)

/-- **The hypotheses at a lookup's member, the thread a variable.** Here b is the member's number; a
is the lookup's public data; J its summands; wit the seat's reader of the input; es the planner's
entries; first the ledger's count in front; fork the seat's reader of the ledger; Q what is said of
the state that the member's step leaves. -/
structure K3Seated (b : Nat) (a : At) (J : LookJobs Wj) (wit : W → Wj) (es : List Fmt.Entry)
    (first : Nat) (fork : FS → Option Fork) (Q : FS → FS → HeardV → Fork → Prop) : Prop where
  half : ∀ blk, T.bs[b]? = some blk → T.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a)
  place : ∀ blk, T.bs[b]? = some blk → blk.place = a.place
  rounds : ∀ blk, T.bs[b]? = some blk → blk.rounds = es.map declOf
  oracles : ∀ blk, T.bs[b]? = some blk → blk.oracles = es.map fun _ => []
  ok : a.face.ok = true
  entries : entriesFit a.face es = true
  base : a.base = T.front + roundsTo T.bs b
  joins : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (s : FS) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts),
    Thr T b k s m E → drawsFit blk.rounds ds = true →
    ∃ F, fork s = some F ∧ JoinedAt blk a J wit (T.φ.sees m.st.input) m ds c first s F T.chain
      T.ft (fun _ _ => none) (fun _ => none) (Q s)

variable {T}
variable {b : Nat} {a : At} {J : LookJobs Wj} {wit : W → Wj} {es : List Fmt.Entry} {first : Nat}
  {fork : FS → Option Fork} {Q : FS → FS → HeardV → Fork → Prop}

/-- **It plays.** Conditional on `K3Seated`. The proof does not use the field joins. -/
theorem plays_k3 (hS : K3Seated T b a J wit es first fork Q) : Plays T b := by
  intro blk hb k s m E ds l hA hd _ hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.half blk hb) l hl
  have hSt : Stands a es m ds :=
    ⟨hS.ok, (Thread.heard_length T hA.2.1).trans hS.base.symm, hS.entries,
      by rw [← hS.rounds blk hb]; exact hd⟩
  obtain ⟨y, hy, _, _, _⟩ := movedInner _ _ _ _ a J wit blk.name
    (T.φ.sees m.st.input) es m ds c 0 0 (fun _ _ => none) (fun _ => none) hSt
  have hy' : play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps blk (T.φ.sees m.st.input) c) ds []
      m = .ok y := by
    rw [steps_eq a J wit _ es blk (hS.place blk hb) (hS.rounds blk hb) (hS.oracles blk hb) c]
    exact hy
  refine ⟨y, [], ⟨⟨_, hl, hy'⟩, ?_⟩, ?_⟩
  · rw [hS.rounds blk hb, readsOf_plain]
    rfl
  · rw [fresh_nil T hb (by rw [hS.oracles blk hb]; simp)]
    intro σ hσ
    exact absurd hσ (List.not_mem_nil)

/-- **Whatever the member's step has left is the state of which the field joins speaks.** Its field
`opened` is as it stood in front. Conditional on `K3Seated`. -/
theorem stepped_k3 (hS : K3Seated T b a J wit es first fork Q) {blk : Block FS Cl}
    (hb : T.bs[b]? = some blk) {k : Coins Bk} {s s' : FS} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hA : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hSt : T.Stepped blk k s m E ds y cols s') :
    cols = [] ∧
      y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds,
        m.seen ++ roundsOf y.1, m.opened⟩ ∧
      ∃ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts)
        (F : Fork) (g : HeardV) (G : Fork),
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
          (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts 0 = .ok c ∧
        fork s = some F ∧ hearV a.face F (roundsOf y.1) = some (g, G) ∧ Q s s' g G ∧
          BehindYes a J first wit m ds c g G := by
  obtain ⟨⟨⟨l, hl, hy⟩, hc⟩, hstep⟩ := hSt
  obtain ⟨_, _, c, hlend, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.half blk hb) l hl
  obtain ⟨F, hFk, y', t, g, G, hy', hy2, _, _, hstep', hh, hQ, hB⟩ :=
    hS.joins blk hb k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    rw [hS.rounds blk hb, readsOf_plain] at hc
    exact (Except.ok.inj hc).symm
  subst hc0
  have e : (t, 0) = (s', ([] : List OpenedColumn).length) := Except.ok.inj (hstep'.symm.trans hstep)
  obtain rfl : t = s' := congrArg Prod.fst e
  exact ⟨rfl, hy2, c, F, g, G, hlend, hFk, hh, hQ, hB⟩

/-- **It is accepted, at every letter fall.** Conditional on `K3Seated`. -/
theorem accepted_k3 (hS : K3Seated T b a J wit es first fork Q)
    (fall : Nat → FS → List Fmt.Drawn → Option String) : Accepted T fall b := by
  intro blk hb k s m E ds y cols hA hd _ _ hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl' := hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.half blk hb) l hl
  obtain ⟨F, _, y', t, g, G, hy', _, _, _, hstep, _⟩ := hS.joins blk hb k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    have hc' := hc
    rw [hS.rounds blk hb, readsOf_plain] at hc'
    exact (Except.ok.inj hc').symm
  subst hc0
  exact ⟨t, ⟨⟨_, hl', hy⟩, hc⟩, hstep⟩

end

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}
  {L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}

/-- **At the first chain's thread the structure follows from `SeatedAt` and `JoinsAt`.** -/
theorem seated_of_look {b : Nat} {a : At} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj}
    {es : List Fmt.Entry} {first : Nat} {fork : FS → Option Fork}
    {Q : FS → FS → HeardV → Fork → Prop} (hS : SeatedAt L b a J wit es)
    (hJ : JoinsAt L b a J wit first fork Q) : K3Seated L.thread b a J wit es first fork Q where
  half := hS.half
  place := hS.place
  rounds := hS.rounds
  oracles := hS.oracles
  ok := hS.ok
  entries := hS.entries
  base := by
    rw [hS.base]
    exact (Nat.zero_add _).symm
  joins := hJ

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.plays_k3
#print axioms ProofFile.Honest.K3.Law.AtThr.stepped_k3
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_k3
#print axioms ProofFile.Honest.K3.Law.AtThr.seated_of_look
