-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsForm.lean: THE LETTERS for "every run returns" (`Owed.runs`, Johnson/Desc/ProofFile/Honest/Owed.lean)
without the invariants of a thread: an invariant OF FORM along a description's three chains, and what is
asked of one sub-protocol along it. General in the description, the book and the prover. Definitions alone.

Why. `runC` (Honest/Walk.lean) plays on with fixed substitutes after the first rejection, so that it returns
does not hang on any acceptance. The frame's law `runC_returns` (Honest/Law/RunsFile.lean) asks `PlaysOn`
(Honest/Law/ThreadC.lean) at every sub-protocol along invariants of the caller's choice. Here they say only in
what form the run stands: nothing on the witness, nothing on the verifier's state, nothing on a coin.

  `roundsIn`, `oraclesIn`   the declared rounds, and the declared oracle messages, of the sub-protocols in front
                          of number j of a chain's list
  `MidForm`     the form of the prover's state in front of a sub-protocol: its input; the challenges that it has
                heard are those of the chain's start and then a list that the rounds in front can draw; its
                stops are handed the like; it has been shown one round for each challenge heard; columns are
                handed
  `EnvForm`     the form of the tables at hand: the stored tables' columns; what is taken over; and the chain's
                own tables produced so far are the oracle messages declared so far, each at its declared width
                (`TablesFit`, Honest/Law/RunsC.lean)
  `formAt`      the invariant: the two together; it reads neither the coins nor the verifier's state
  `BlockPlays`  WHAT ONE SUB-PROTOCOL OWES: from a state of that form, at challenges that its rounds can draw, where
                nothing of it stops and the book has lent (`chainSteps` at the one sub-protocol has returned):
                `play` returns. No column, no step, no next invariant: these are paid once, for all
  `startNone`, `startThird`, `takenNone`, `takenThird`   the forms at the chains' starts
  `BlocksPlay`  `BlockPlays` at every sub-protocol of the three lists

Nothing is shown here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import Johnson.Desc.ProofFile.Honest.Law.StratRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

section Chain
variable {S Cl V W Y Pb : Type}

/-- The declared rounds of the sub-protocols in front of number j. -/
def roundsIn (bs : List (Block S Cl)) (j : Nat) : List Fmt.DeclaredRound := (bs.take j).flatMap (·.rounds)

/-- The oracle messages that the sub-protocols in front of number j declare, in the order of sending. -/
def oraclesIn (bs : List (Block S Cl)) (j : Nat) : List Oracle :=
  (rowsOfChain (bs.take j)).flatMap (·.2)

/-- **The form of the prover's state in front of a sub-protocol.** `Start h₀ l₀`: what the state had heard,
and what its stops were handed, at the chain's start. `rs`: the declared rounds in front. `w`: the input. -/
structure MidForm (Start : List Fmt.Drawn → List Fmt.Drawn → Prop) (rs : List Fmt.DeclaredRound) (w : W)
    (m : Mid W Y) : Prop where
  input : m.st.input = w
  heard : ∃ h₀ l₀ ds, Start h₀ l₀ ∧ drawsFit rs ds = true ∧ m.st.heard = h₀ ++ ds ∧ m.loc = l₀ ++ ds
  seen : m.seen.map (·.drawn) = m.st.heard
  opened : m.opened.isSome = true

/-- **The form of the tables at hand.** `Taken`: what may stand for the look-up of a tree that is taken over.
`os`: the oracle messages declared in front. -/
def EnvForm (stored : Nat → Nat → Option (List UInt64))
    (Taken : (Nat → Nat → Option (Place × Table)) → Prop) (os : List Oracle) (E : Env) : Prop :=
  ∃ taken laid, Taken taken ∧ E = envOf stored taken laid ∧ TablesFit os laid

/-- **The invariant of form** in front of sub-protocol number j of a chain's list. -/
def formAt {Bk : ProverCoinCounts} (stored : Nat → Nat → Option (List UInt64))
    (Taken : (Nat → Nat → Option (Place × Table)) → Prop)
    (Start : List Fmt.Drawn → List Fmt.Drawn → Prop) (w : W) (bs : List (Block S Cl)) (j : Nat) :
    Coins Bk → S → Mid W Y → Env → Prop :=
  fun _ _ m E => MidForm Start (roundsIn bs j) w m ∧ EnvForm stored Taken (oraclesIn bs j) E

/-- **WHAT ONE SUB-PROTOCOL OWES.** `Pre`: the form of the state in front of it. -/
def BlockPlays (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain : Nat) (hs : List (Placed V W Y)) (b : Block S Cl)
    (Pre : Mid W Y → Prop) : Prop :=
  ∀ (k : Coins Bk) (m : Mid W Y) (ds : List Fmt.Drawn) (l : List (Step W Y)), Pre m →
    drawsFit b.rounds ds = true → chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    ∃ y, play l ds [] m = .ok y

end Chain

/-- At the first and the shared chain's start nothing has been heard. -/
def startNone (h₀ l₀ : List Fmt.Drawn) : Prop := h₀ = [] ∧ l₀ = []

/-- Nothing is taken over in the first and the shared chain. -/
def takenNone (taken : Nat → Nat → Option (Place × Table)) : Prop := taken = fun _ _ => none

section File
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- At the second chain's start the state has heard a list that the first chain's rounds can draw and then
one that the shared chain's can; its stops are handed the first alone. -/
def startThird (F : FileDescription Xi) (h₀ l₀ : List Fmt.Drawn) : Prop :=
  ∃ d₁ d₂, drawsFit F.roundsDeclaredByBlocks.1 d₁ = true ∧ drawsFit F.roundsDeclaredByBlocks.2.1 d₂ = true ∧ h₀ = d₁ ++ d₂ ∧ l₀ = d₁

/-- What the second chain takes over: the look-up in two lists of rounds whose tables are the oracle messages
that the first and the shared chain declare. -/
def takenThird (F : FileDescription Xi) (taken : Nat → Nat → Option (Place × Table)) : Prop :=
  ∃ l₁ l₂, TablesFit ((rowsOfChain F.first.blocksInOrder).flatMap (·.2)) l₁ ∧
    TablesFit ((rowsOfChain F.shared.blocksInOrder).flatMap (·.2)) l₂ ∧ taken = taken₃ l₁ l₂

/-- **`BlockPlays` at every sub-protocol of the three lists.** `own`, `common`: the two inputs of the run. -/
structure BlocksPlay (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (own : Local W₀ Rc Xi Tr) (common : Common W₀ Rc Ky) : Prop where
  first : ∀ j b, F.first.blocksInOrder[j]? = some b →
    BlockPlays .own Bk 0 H.first b (MidForm startNone (roundsIn F.first.blocksInOrder j) own)
  shared : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    BlockPlays .shared Bk 1 H.shared b (MidForm startNone (roundsIn F.shared.blocksInOrder j) common)
  second : ∀ j b, F.second.blocksInOrder[j]? = some b →
    BlockPlays .own Bk 2 H.second b (MidForm (startThird F) (roundsIn F.second.blocksInOrder j) own)

/-- **THE STATEMENT that the letters are for** (its term: E2E/OfflineRunsLaw.lean): where `ready` has returned,
the description passes its tests on the plan and `sealPlain`, every sub-protocol that declares a root has a
prover's side, the plan serves, and every sub-protocol plays from the form: at all challenges that the rounds
can draw, outside the stops, `runC` returns. -/
def RunsOfBlocks (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop :=
  ∀ (w₀ : W₀) (rc : Rc) (x : Xi) (k : Coins Bk) (ρ : Draws) (R : Ready W₀ Rc Xi Ky Tr X₀ X),
    ready F Bk H w₀ rc x k = .ok R → F.planOk = true → sealPlain F = true → rootedAll F H = true →
    PlanServes H w₀ rc R → BlocksPlay F Bk H R.own R.common → ρ.due F = true →
    silentAt F H w₀ rc x ρ = none → ∃ r, runC F Bk H w₀ rc x k ρ = .ok r

end File

end AtPublicFiles.OfflineRows
