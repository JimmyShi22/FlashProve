-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Top.lean: the honest side of the kind "lookup" (K3). The row's
inner lemmas in the frame's own terms, cut as the frame cuts what is owed at a member: that the
row's play goes through; that the verifier's hearing accepts on what was played; what holds behind
that acceptance. All three speak of the seated row (`proverSideOfLookupInChainAtOneOwner`), of the frame's `play` on its steps
at the planner's entries, and of where a chain's run stands in front of the lookup (`Mid`).
Definitions, three statements and their proofs.

Terms. Honest/K3/GLOSSARY.md ("course", "hearing", "ledger", "play", "row").

What is shown.
  `courseAt`, `LedgerIn`, `Stands`: the course that such a play is; the ledger in front; the
    hypotheses that all three statements share.
  `MovedInner`, `movedInner`: at all coins, with no summand read and no hypothesis on the verifier's
    side: `play` returns; what it leaves; no table is sent; no column is read.
  `HeardInner`, `heardInner`: conditional on `HB` and on one part of keys: on what any such play
    yields, `hearV` returns. No summand's value matters.
  `LeftInner`, `leftInner`: conditional on `HB` and on one part of keys: wherever `hearV` has
    returned on it: what was heard is the run's, with its points; the invariant holds behind the
    last stage; and, if the summands are `Lawful`, `Left` holds.
These are lemmas' statements about one kind's honest part, none of the library's goals.

Hypotheses that remain.
  `Stands` and `LedgerIn` (`hS`, `hL`; `h` in `fit_of_stands`, `inv0_of`).
  `HB` (`B`; Honest/K3/Law/SumWhole.lean), in `heardInner` and `leftInner`.
  One part of keys (`hp`), in the same two.
  `hy`: (in `seated_walk`) the play on the seated row's steps returns.
  `Lawful`, for the last clause of `LeftInner`.

Users. This file is imported by Honest/K3/Law/HBPaid.lean and Honest/K3/Law/TopMembers.lean
[not in this library].

Limits. The verifier's side is the kind's own texts `hearV` and `planesV`, not the `step` of a
seated sub-protocol: that sub-protocol's further tests, the rounds without their digests, and the
text that it runs for the claims on the planes are treated in other files. That a book lends the row
its coins is treated in another file (Honest/K3/Law/RowLends.lean).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LookOne
import Johnson.Desc.ProofFile.Honest.K3.Law.RowSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Oracle Place)
open VerifiableInference.Desc.K3 (HeardV hearV entriesFit)

variable {W W₁ X₁ : Type}

/-! ## The letters -/

/-- **The course that a play of the seated row is**: of the lookup's public data, the summands, the
ledger's next slot, the half's reader of the input, where the run stands in front of the lookup, the
lookup's challenges, and coins by stage. -/
def courseAt (a : At) (J : LookJobs W) (first : Nat) (wit : W₁ → W) (m : Mid W₁ X₁)
    (ds : List Fmt.Drawn) (c : (s : Stage) → StageCoins a s) : Course W :=
  { a := a, J := J, first := first, c := c, t := m.st.narrow wit (fun _ => ()), seen := m.shown
    ds := ds }

/-- **The ledger in front of the lookup**: the arrays have their size; the count of slots is the
public number; there is room for the lookup; from the count on all is free as far as the lookup
reaches. -/
structure LedgerIn (f : LFace) (first : Nat) (F : Fork) : Prop where
  sized : Sized F
  next : F.next = first
  room : first + f.slots ≤ F.ns
  free : ∀ j, F.next ≤ j → j < first + f.slots → ¬ Filled F j

/-- It is the invariant in front of the first stage, at every coins. -/
theorem inv0_of {R : Course W} {F : Fork} (h : LedgerIn R.f R.first F) : Inv R 0 F :=
  ⟨h.sized, by rw [h.next]; simp [slotsIn], h.room, h.free, fun s hs => by simp at hs,
    fun _ _ _ _ _ s hs => by simp at hs⟩

/-- **What all three statements ask**: the tests on the lookup's numbers; as many challenges were
heard as the place's public data says; the planner's entries are the verifier's text's but for the
work bits; the challenges pass the frame's own test at these entries. -/
structure Stands (a : At) (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn) : Prop where
  ok : a.face.ok = true
  base : m.st.heard.length = a.base
  entries : entriesFit a.face es = true
  draws : drawsFit (es.map declOf) ds = true

theorem fit_of_stands {a : At} {es : List Fmt.Entry} {m : Mid W₁ X₁} {ds : List Fmt.Drawn}
    (h : Stands a es m ds) (J : LookJobs W) (first : Nat) (wit : W₁ → W)
    (c : (s : Stage) → StageCoins a s) : Fit (courseAt a J first wit m ds c) :=
  ⟨h.ok, h.base, (drawsWork a.face es ds h.entries).symm.trans h.draws⟩

/-- Rounds that are declared by their entries alone read no column. -/
theorem readsOf_plain (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
      readsOf chain ft stored tree (es.map declOf) ds = []
  | [], _ => by simp [readsOf]
  | _ :: _, [] => by simp [readsOf]
  | _ :: es, _ :: ds => by
    simp only [List.map_cons, readsOf, readsOf_plain chain ft stored tree es ds]
    simp [declOf]

/-- The steps of the seated row at the planner's entries. -/
abbrev seatSteps {V₁ : Type} (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String)
    (v : Option V₁) (es : List Fmt.Entry)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts) :
    List (Step W₁ X₁) :=
  rowSteps name a.place v (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit a).parts 0
    (es.map fun e => (declOf e, ([] : List Oracle))) c

/-! ## 1 The play goes through -/

/-- The statement that the seated row's play goes through, at all coins: it returns; it leaves the
state with the challenges heard, the challenges and the rounds laid behind what stood there, and the
columns opened as they stood; every round bears the lookup's place and no table; and the lookup's
rounds read no column. No summand is read and nothing of the verifier's side is asked. A lemma's
statement, none of the library's goals. -/
def MovedInner : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String) (v : Option V₁)
    (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)),
    Stands a es m ds →
    ∃ y, play (seatSteps a J wit name v es c) ds [] m = .ok y ∧
      y.2 = ⟨{ m.st with heard := m.st.heard ++ ds }, m.loc ++ ds, m.seen ++ roundsOf y.1,
        m.opened⟩ ∧
      (∀ q ∈ y.1, q.place = a.place ∧ q.told = true ∧ q.tables = []) ∧
      fillCols (readsOf chain ft stored tree (es.map declOf) ds) [] = .ok []

/-- **The seated row's play goes through** (the statement `MovedInner`). -/
theorem movedInner : MovedInner := by
  intro V₁ W₁ X₁ W a J wit name v es m ds c chain ft stored tree hS
  obtain ⟨c', _, hplay⟩ := rowPlaysSeated V₁ W₁ X₁ W
    (courseAt a J 0 wit m ds (courseCoins a fun _ _ _ => 0)) wit m.st name v es m.loc c rfl
  obtain ⟨y, x, hy, _, hyx, hy2, hq⟩ := hplay (fit_of_stands hS J 0 wit _) hS.entries []
  subst hyx
  refine ⟨y, hy, hy2, hq, ?_⟩
  rw [readsOf_plain]
  rfl

/-! ## 2 The hearing accepts; 3 What holds behind it -/

/-- What the two statements on the verifier's side take from one walk. -/
theorem seated_walk (B : HB) {V₁ : Type} (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String)
    (v : Option V₁) (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (first : Nat) (F : Fork) (n : Nat) (y : List Played × Mid W₁ X₁) (hS : Stands a es m ds)
    (hp : a.face.parts = [n]) (hL : LedgerIn a.face first F)
    (hy : play (seatSteps a J wit name v es c) ds [] m = .ok y) :
    ∃ c' : (s : Stage) → StageCoins a s,
      CoinsAre (V := Unit) (courseAt a J first wit m ds c')
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c) ∧
      ∃ g G, hearV a.face F (roundsOf y.1) = some (g, G) ∧
        HeardIs (courseAt a J first wit m ds c') g ∧
        PointsAgree a.face g a.base (m.st.heard ++ ds) ∧
        Inv (courseAt a J first wit m ds c') (stages a.face).length G ∧
        ∀ (planes : List (E × E) → GE) (keys : Nat → Array E → GE),
          Lawful (courseAt a J first wit m ds c') planes keys →
          Left (courseAt a J first wit m ds c') planes keys g G := by
  obtain ⟨c', hc, hplay⟩ := rowPlaysSeated V₁ W₁ X₁ W
    (courseAt a J first wit m ds (courseCoins a fun _ _ _ => 0)) wit m.st name v es m.loc c rfl
  obtain ⟨y', x, hy', hx, hyx, _, _⟩ := hplay (fit_of_stands hS J first wit _) hS.entries []
  have e : y' = y := Except.ok.inj (hy'.symm.trans hy)
  subst e
  subst hyx
  have hF := fit_of_stands hS J first wit c'
  have hx' : (courseAt a J first wit m ds c').rounds = some (roundsOf y'.1) := hx
  obtain ⟨g, G, hh, hH, hI, _, h1, h2⟩ := lookHeard_one (stageStep B) (leavesStep B) W
    (courseAt a J first wit m ds c') F (roundsOf y'.1) n hp hF (inv0_of hL) hx'
  have C := cut_of_rounds _ _ hF hx'
  have P : PointsAgree a.face g a.base (m.st.heard ++ ds) := by
    have := pointsAgree_of_hearV a.face n hp F G (roundsOf y'.1) g m.st.heard [] hh
    rw [C.drawn, List.append_nil, hS.base] at this
    exact this
  exact ⟨c', hc, g, G, hh, hH, P, hI, fun planes keys hLaw =>
    lookLeft_of _ planes keys F G _ g n hp hF C hh hH hI h1 h2 hLaw⟩

/-- The statement that on what the seated row's play yields the verifier's hearing returns, at one
part of keys, from a ledger with room in front. No summand's value matters. A lemma's statement,
none of the library's goals. -/
def HeardInner : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String) (v : Option V₁)
    (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (first : Nat) (F : Fork) (n : Nat) (y : List Played × Mid W₁ X₁),
    Stands a es m ds → a.face.parts = [n] → LedgerIn a.face first F →
    play (seatSteps a J wit name v es c) ds [] m = .ok y →
    ∃ g G, hearV a.face F (roundsOf y.1) = some (g, G)

/-- **Conditional on `HB`; one part of keys: the hearing returns on what was played** (the statement
`HeardInner`). -/
theorem heardInner (B : HB) : HeardInner := by
  intro V₁ W₁ X₁ W a J wit name v es m ds c first F n y hS hp hL hy
  obtain ⟨_, _, g, G, hh, _⟩ := seated_walk B a J wit name v es m ds c first F n y hS hp hL hy
  exact ⟨g, G, hh⟩

/-- The statement of what holds behind the hearing's return, at one part of keys: wherever `hearV`
has returned on what the seated row's play yields, there is a course with the row's coins such that:
what was heard is the run's; its points are those of the challenges by number; the invariant holds
behind the last stage; and, if the summands are `Lawful` at that course, `Left`: all rows are worth
0, the key tree's last form is worth alpha less the keys' value, the three claims on the planes
hold. A lemma's statement, none of the library's goals. -/
def LeftInner : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (a : At) (J : LookJobs W) (wit : W₁ → W) (name : String) (v : Option V₁)
    (es : List Fmt.Entry) (m : Mid W₁ X₁) (ds : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (first : Nat) (F G : Fork) (n : Nat) (y : List Played × Mid W₁ X₁) (g : HeardV),
    Stands a es m ds → a.face.parts = [n] → LedgerIn a.face first F →
    play (seatSteps a J wit name v es c) ds [] m = .ok y →
    hearV a.face F (roundsOf y.1) = some (g, G) →
    ∃ c' : (s : Stage) → StageCoins a s,
      CoinsAre (V := Unit) (courseAt a J first wit m ds c')
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c) ∧
      HeardIs (courseAt a J first wit m ds c') g ∧
      PointsAgree a.face g a.base (m.st.heard ++ ds) ∧
      Inv (courseAt a J first wit m ds c') (stages a.face).length G ∧
      ∀ (planes : List (E × E) → GE) (keys : Nat → Array E → GE),
        Lawful (courseAt a J first wit m ds c') planes keys →
        Left (courseAt a J first wit m ds c') planes keys g G

/-- **Conditional on `HB`; one part of keys; its last clause on `Lawful`: what holds behind the
hearing's return** (the statement `LeftInner`). -/
theorem leftInner (B : HB) : LeftInner := by
  intro V₁ W₁ X₁ W a J wit name v es m ds c first F G n y g hS hp hL hy hh
  obtain ⟨c', hc, g', G', hh', hH, P, hI, hLeft⟩ :=
    seated_walk B a J wit name v es m ds c first F n y hS hp hL hy
  rw [hh] at hh'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh')
  exact ⟨c', hc, hH, P, hI, hLeft⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.inv0_of
#print axioms ProofFile.Honest.K3.Law.fit_of_stands
#print axioms ProofFile.Honest.K3.Law.readsOf_plain
#print axioms ProofFile.Honest.K3.Law.movedInner
#print axioms ProofFile.Honest.K3.Law.seated_walk
#print axioms ProofFile.Honest.K3.Law.heardInner
#print axioms ProofFile.Honest.K3.Law.leftInner
