-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PlaysAnyState.lean: the honest side of the kind "lookup"
(K3): two of the forms of hypothesis that Honest/Thread/Pays.lean asks at each member, `Plays T b`
and `Accepted T fall b`, at a lookup's member, with the thread a variable and the type S of the
verifier's state a variable: the two theorems of Honest/K3/Law/Thread/AtThread.lean, whose thread is
typed at the state of the proof file's first chain, in a form that a chain with another type of
state can call. Two structures of hypotheses, a definition, theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Plays` and `Accepted` are definitions of
Honest/Thread/Pays.lean; by their docstrings each is a hypothesis's form, of which nothing is
claimed.

Why. `plays_k3` (AtThread.lean) uses seven fields of its structure of hypotheses, none of which
names the state. `accepted_k3` (there) takes the member's accepting step out of the field joins,
which says of the state only that the member's step returns from it and what the letter Q says. So
the type of the state can be a variable in both.

What is shown.
  `steps_eqS`: the seated row's steps at a member whose rounds and oracle messages are those of the
    planner's entries (`steps_eq` of Honest/K3/Law/Joined.lean, at any type of state).
  `K3PlaysAt`: (structure) the hypotheses of `Plays`, by name: the seven.
  `plays_k3S`: `K3PlaysAt T b ...` gives `Plays T b`.
  `JoinedAtS`: (definition) what the join concludes (`JoinedAt` of Honest/K3/Law/Joined.lean, at any
    type of state).
  `joinedAtS_first`: at the first chain's state it is `JoinedAt`, by rfl.
  `K3SeatedS`: (structure) the seven and the field joins.
  `accepted_k3S`: `K3SeatedS T b ...` gives `Accepted T fall b`, at every fall. This is a lemma; it
    does not show the acceptance: the field joins holds the member's own accepting step, and
    the theorem only takes it out.
  `playsAt_of_seated`, `seatedS_of_seated`: at the first chain's state `K3Seated` (AtThread.lean)
    gives both structures. So `plays_k3` and `accepted_k3` are cases of the two theorems here.

Hypotheses that remain.
  `hS`: `K3PlaysAt` (in `plays_k3S`); `K3SeatedS` (in `accepted_k3S`).
  `hpl`, `hr`, `ho`: (in `steps_eqS`) the sub-protocol stands at the place; its rounds are the
    entries'; it states no oracle message.
  In `playsAt_of_seated` and `seatedS_of_seated` `hS` is `K3Seated`.

Imported, through Honest/K3/Law/Thread/AtThread.lean. Files under Honest/Thread/.

Users. `plays_atSiteS` (Honest/K3/Law/Thread/PlaysAtSite.lean [not in this library]) and
`plays_headRest` (Honest/K3/Law/Thread/PlaysAtHeadRest.lean [not in this library]) call `plays_k3S`;
these two files state `K3PlaysAt` at a site.

`K3PlaysAt` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. `K3SeatedS` holds `K3PlaysAt` as its field plays, and spells the elder
row's parts in its field joins. Who pays the field, each at the fast summands and under hypotheses
on the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]).
A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term
there: no file shows the field at such a lot, so the theorems of this file that bear it cannot be
called there as they stand.
Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. Where the field joins is shown at a chain with another type of state is not stated here. At
the proof file's first chain it is shown in Honest/K3/Law/Thread/AtThreadSite.lean, from that
description's own member, its lot's seat and the library's test on that state: none of these can be
called at another type of state. `Plays` and `Accepted` are forms of hypothesis of
Honest/Thread/Pays.lean. The acceptance is stated at any summands: it says nothing on values.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV entriesFit)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb Wj : Type}

/-- The seated row's steps at a member whose place is the lookup's and whose rounds and oracle
messages are those of the planner's entries. No field of the state is read. -/
theorem steps_eqS (a : At) (J : LookJobs Wj) (wit : W → Wj) (v : Option V)
    (es : List Fmt.Entry) (b : Block S Cl) (hpl : b.place = a.place)
    (hr : b.rounds = es.map declOf) (ho : b.oracles = es.map fun _ => [])
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts) :
    (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps b v c = seatSteps a J wit b.name v es c := by
  show rowSteps b.name b.place v _ 0 (b.rounds.zip b.oracles) c =
    rowSteps b.name a.place v _ 0 (es.map fun e => (declOf e, ([] : List Oracle))) c
  rw [hpl, hr, ho, List.zip_map']

/-- **What the join concludes, at any type of state.** The text is that of `JoinedAt`
(Honest/K3/Law/Joined.lean). -/
def JoinedAtS (b : Block S Cl) (a : At) (J : LookJobs Wj) (wit : W → Wj) (v : Option V)
    (m : Mid W X) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
    (s : S) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Q : S → HeardV → Fork → Prop) : Prop :=
  ∃ y s' g G, play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps b v c) ds [] m = .ok y ∧
    y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩ ∧
    (∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = []) ∧
    fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] ∧
    b.step ft s (roundsOf y.1) [] = .ok (s', 0) ∧
    hearV a.face F (roundsOf y.1) = some (g, G) ∧ Q s' g G ∧ BehindYes a J first wit m ds c g G

/-- At the first chain's state it is `JoinedAt`. -/
theorem joinedAtS_first (b : Block FS Cl) (a : At) (J : LookJobs Wj) (wit : W → Wj)
    (v : Option V) (m : Mid W X) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts) (first : Nat)
    (s : FS) (F : Fork) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Q : FS → HeardV → Fork → Prop) :
    JoinedAtS b a J wit v m ds c first s F chain ft stored tree Q =
      JoinedAt b a J wit v m ds c first s F chain ft stored tree Q := rfl

variable (T : Thread Bk S Cl V W X Pb)

/-- **The hypotheses of `Plays` at a lookup's member, with the thread and the type of the state
variables.** Here b is the member's number, a the lookup's public data, J its summands, wit the
seat's reader of the input, and es the planner's entries. -/
structure K3PlaysAt (b : Nat) (a : At) (J : LookJobs Wj) (wit : W → Wj) (es : List Fmt.Entry) :
    Prop where
  half : ∀ blk, T.bs[b]? = some blk → T.hs.find? (fun h => h.place == blk.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a)
  place : ∀ blk, T.bs[b]? = some blk → blk.place = a.place
  rounds : ∀ blk, T.bs[b]? = some blk → blk.rounds = es.map declOf
  oracles : ∀ blk, T.bs[b]? = some blk → blk.oracles = es.map fun _ => []
  ok : a.face.ok = true
  entries : entriesFit a.face es = true
  base : a.base = T.front + roundsTo T.bs b

/-- **The seven and the field joins.** Here first is the ledger's count in front, fork the seat's
reader of the ledger, and Q what is said of the state that the member's step leaves. -/
structure K3SeatedS (b : Nat) (a : At) (J : LookJobs Wj) (wit : W → Wj) (es : List Fmt.Entry)
    (first : Nat) (fork : S → Option Fork) (Q : S → S → HeardV → Fork → Prop) : Prop where
  plays : K3PlaysAt T b a J wit es
  joins : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (s : S) (m : Mid W X) (E : Env)
    (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) ⟨ptsOf, pointsAt⟩ J wit a).parts),
    Thr T b k s m E → drawsFit blk.rounds ds = true →
    ∃ F, fork s = some F ∧ JoinedAtS blk a J wit (T.φ.sees m.st.input) m ds c first s F T.chain
      T.ft (fun _ _ => none) (fun _ => none) (Q s)

variable {T}
variable {b : Nat} {a : At} {J : LookJobs Wj} {wit : W → Wj} {es : List Fmt.Entry} {first : Nat}
  {fork : S → Option Fork} {Q : S → S → HeardV → Fork → Prop}

/-- **It plays** (`Plays T b`), at any type of state. Conditional on `K3PlaysAt`. -/
theorem plays_k3S (hS : K3PlaysAt T b a J wit es) : Plays T b := by
  intro blk hb k s m E ds l hA hd _ hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.half blk hb) l hl
  have hSt : Stands a es m ds :=
    ⟨hS.ok, (Thread.heard_length T hA.2.1).trans hS.base.symm, hS.entries,
      by rw [← hS.rounds blk hb]; exact hd⟩
  obtain ⟨y, hy, _, _, _⟩ := movedInner _ _ _ _ a J wit blk.name
    (T.φ.sees m.st.input) es m ds c 0 0 (fun _ _ => none) (fun _ => none) hSt
  have hy' : play ((proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).steps blk (T.φ.sees m.st.input) c) ds []
      m = .ok y := by
    rw [steps_eqS a J wit _ es blk (hS.place blk hb) (hS.rounds blk hb) (hS.oracles blk hb) c]
    exact hy
  refine ⟨y, [], ⟨⟨_, hl, hy'⟩, ?_⟩, ?_⟩
  · rw [hS.rounds blk hb, readsOf_plain]
    rfl
  · rw [fresh_nil T hb (by rw [hS.oracles blk hb]; simp)]
    intro σ hσ
    exact absurd hσ (List.not_mem_nil)

/-- **It is accepted** (`Accepted T fall b`), at every letter fall and at any type of state.
Conditional on `K3SeatedS`. A lemma; it does not show the acceptance: the field joins holds the
member's own accepting step. -/
theorem accepted_k3S (hS : K3SeatedS T b a J wit es first fork Q)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Accepted T fall b := by
  intro blk hb k s m E ds y cols hA hd _ _ hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl' := hl
  obtain ⟨_, _, c, _, rfl⟩ := chainSteps_one Bk _ _ _ blk T.hs _ (hS.plays.half blk hb) l hl
  obtain ⟨F, _, y', t, g, G, hy', _, _, _, hstep, _⟩ := hS.joins blk hb k s m E ds c hA hd
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hc0 : cols = [] := by
    have hc' := hc
    rw [hS.plays.rounds blk hb, readsOf_plain] at hc'
    exact (Except.ok.inj hc').symm
  subst hc0
  exact ⟨t, ⟨⟨_, hl', hy⟩, hc⟩, hstep⟩

end

section
variable {Bk : ProverCoinCounts} {Cl V W X Pb Wj : Type} {T : Thread Bk FS Cl V W X Pb}
  {b : Nat} {a : At} {J : LookJobs Wj} {wit : W → Wj} {es : List Fmt.Entry} {first : Nat}
  {fork : FS → Option Fork} {Q : FS → FS → HeardV → Fork → Prop}

/-- **At the first chain's state `K3Seated` gives the seven.** -/
theorem playsAt_of_seated (hS : K3Seated T b a J wit es first fork Q) :
    K3PlaysAt T b a J wit es :=
  ⟨hS.half, hS.place, hS.rounds, hS.oracles, hS.ok, hS.entries, hS.base⟩

/-- **And the seven with the field joins.** -/
theorem seatedS_of_seated (hS : K3Seated T b a J wit es first fork Q) :
    K3SeatedS T b a J wit es first fork Q :=
  ⟨playsAt_of_seated hS, hS.joins⟩

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.steps_eqS
#print axioms ProofFile.Honest.K3.Law.AtThr.joinedAtS_first
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_k3S
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_k3S
#print axioms ProofFile.Honest.K3.Law.AtThr.playsAt_of_seated
#print axioms ProofFile.Honest.K3.Law.AtThr.seatedS_of_seated
