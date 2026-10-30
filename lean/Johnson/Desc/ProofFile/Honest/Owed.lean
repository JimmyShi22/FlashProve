-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Owed.lean: the definition `Owed`, and three small definitions that it
uses. `Owed` collects, as one Lean structure of propositions, the hypotheses that a statement about
all honest sides of one description would have to take. It is stated over `runC` (Honest/Walk.lean),
the honest run that asks the description's own step on what has been sent. Definitions only:
no theorem is stated here, and no rule that joins sides.

  `earlierOf`   the earlier chains' declared rounds, by the chain's number
  `orRefused`   an error in the place of "no state"
  `Lettered.withField`   a list with what the field `opened` holds beside its A and its B
  `Owed`   the structure

How it depends on `runC`. The run that has to succeed is `runC`'s. `On` has to be proved of every
part that the run has called (`RunC.called`, a test on the run), and of no other: after a
sub-protocol that rejects, no later part of its chain and no part of the second chain is called. A
rejection in the first chain does not reach the shared chain, whose parts are still called
(Honest/Walk.lean, "Two strands"). `bud` has to be proved of every part, called or not: it reads the
part's own challenges and the positions read of its tables, and no coin. Both are asked at all coins
and at every list of challenges outside the one silent set (`silentAt`, Honest/Rule.lean); that no
fall occurs is not a hypothesis here. The description's tests on its plan are a hypothesis: among
them, that no tree is opened before the round that sends it.
The state of a run before a called part is what `midAtW` or `midSharedAtW` (Honest/MidW.lean)
returns: the walk's own state there. `midAt` and `midSharedAt` (Honest/Frame.lean) start at a state
whose field `opened` is `none` and never lengthen it (`play` keeps whatever field its start state
has), so at the states that they reach the hypothesis of `Good.exact` on that field is false
wherever `front` holds a column for every read of `pre`. `orRefused` fits the types: after a
rejection the walk has no state, and that becomes an error.

How `good` speaks of the opened columns.
  1  The earlier chains' declared rounds are laid by `earlierOf F`, not by a free parameter: a wrong
     list there would compile and make `exact` idle.
  2  `Good.plays` says B at the state with the columns read laid in (`Mid.took`), for all lists.
  3  Beside each list's A and B stands what the field holds: `WithField` (Honest/FieldGood.lean)
     lays `FieldAt` (Honest/Field.lean) and `FieldFit` (Honest/FieldLaw.lean) beside a condition,
     and `Lettered.withField` does so at a list. So no list has to word that for itself, and a list
     whose parts read the field finds it among the hypotheses of `plays` and `acc` alone. The
     field's half of B is paid by one law for all lists (`Good.field`, Honest/FieldGood.lean).

Limits.
  * This file proves `Owed` of nothing. At the key file's description it is a theorem of the offline
    honest prover at muted rows, where `plays` and `acc` hold vacuously, at public files in scope
    that pass their test (`offline_rows_at_the_files`, E2E/OfflineClausesAtTheFiles.lean). Others
    take premises of their own (Johnson/T3/OwedOfKinds.lean). It gives: Honest/Law/Rule/Row.lean.
  * That the field's condition holds at a chain's start in a run is not proved.
  * `base` and `skip` are free in the second chain (`good` asks all values): nothing here says
    that the run's own values are the two earlier chains' columns and the number of their
    challenges.
  * `FieldAt` fills all the rounds' reads at once from the tables that are available now; the walk
    fills them sub-protocol by sub-protocol from those available then. That the two agree is not
    proved.
  * That `midAtW` and `midSharedAtW` return the state through which `runC`'s own walk goes is read
    off the definitions; it is not proved (Honest/MidW.lean, Limits).
  * The hypothesis of `Good.exact` on the field, at the walk's own state and at `Run.beforeAt`, is
    not asked here and no statement concludes it (which columns it holds: Honest/WalkOpened.lean,
    Limits): a statement on `exact` has to take it or prove it; else `exact` at a reader of the
    field speaks of states that no run is shown to reach. With `Before` written out, at the state
    that `midAtW` or `midSharedAtW` returns: Honest/Law/Rule/OpenedRun.lean (its Limits). The rule
    does not ask it: `rule_views` (Honest/Law/Rule/Row.lean) takes `Owed` and `G.owns` alone.
  * With the field beside A, `plays` and `acc` are asked at no state whose field is `none`: so at no
    state of `run`, `midAt` or `midSharedAt`.
  * `Rel`, the relation on inputs, is a free parameter. With Rel := False the three fields that
    speak of inputs (`input`, `runs`, `owed`) hold vacuously, and any `Rel` that is narrower than
    the relation about which something is to be stated narrows all three.
  * There is a way to meet `owed` vacuously that the same hypotheses over `run` would not have. `On`
    has to be proved of called parts alone. So where an early sub-protocol always rejects, `On` has
    to be proved of no later part of its chain and of no part of the second chain, at every coin.
    Such a sub-protocol can be one that declares an item at a place without a list of parts (nothing
    is sent there, and its step rejects), or one that rejects whatever is sent; a start of the
    second chain that always rejects has the same effect. Nothing here excludes that. `acc` and the
    falls' shares do, where they are proved.
  * A part that always stops puts every list of challenges into the silent set; `runs` and `owed`
    then hold vacuously. The stated shares are meant to exclude that, where they are proved
    (Honest/Side.lean and Honest/Rule.lean say the same of `Good`).
  * That every fall is at a sub-protocol's place (`Sides.fallsSeated`, Honest/Fall.lean) is not
    asked here. A fall at a place of no sub-protocol has no effect, and nothing reports it.
  * What is stated is what a statement on `exact` and `fresh` would take, not one on `acc`.
  * One request: a batch of several is not modelled.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.MidW
import Johnson.Desc.ProofFile.Honest.FieldGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **The earlier chains' declared rounds**, as `preOf` (Rule.lean) takes them, by the chain's
number, from 0: none for the first and the shared chain, and none at any other number; for the
second chain those of the first and then those of the shared chain, each with its number and 0 as
the number of its first own tree. -/
def earlierOf (F : FileDescription Xi) : Nat → List (Nat × Nat × List Fmt.DeclaredRound)
  | 2 => [(0, 0, F.roundsDeclaredByBlocks.1), (1, 0, F.roundsDeclaredByBlocks.2.1)]
  | _ => []

section
variable {S Cl V W Y Pb : Type}

/-- An error in the place of "no state": once the verifier has rejected the walk plays nothing. -/
def orRefused (e : Except Refusal (Option (Mid W Y))) : Except Refusal (Mid W Y) :=
  e.bind fun o =>
    match o with
    | some m => .ok m
    | none => .error ⟨.unfit, "the verifier has rejected before the address"⟩

/-- **A list with what the field holds beside its A and its B**: before the place, the reads of the
rounds before it; after the place, these and the place's own; and the law's three side conditions
(`FieldFit`). `base`, `skip`: as in `FieldAt`. -/
def Lettered.withField {Bk : ProverCoinCounts} (L : Lettered Bk S Cl V W Y Pb) (chain firstTree : Nat)
    (bs : List (Block S Cl)) (base : List OpenedColumn) (skip : Nat) : Lettered Bk S Cl V W Y Pb :=
  { L with
    A := WithField chain firstTree (roundsBefore bs L.place) base skip L.A
    B := WithField chain firstTree (roundsUpTo bs L.place) base skip L.B }

end

/-- **The hypotheses that a statement on `exact` and `fresh` about all sides of one description
would take.** It is a definition. Whatever is proved about it is named where it is proved; nothing
is claimed here; and it is none of the library's goals.

`F`, `Bk`, `H`: one description, one book, one prover; the prover's sides are taken from the lists
(`Sides.prover`). `Rel`: the inputs about which something is to be stated. The relation proper reads
the index, the instance and the witness, not the stored tables' pads and encoding randomness. `Rel`
has the argument rc because the explicit input holds a sample that is computed from them. The form
that is meant: Rel w₀ rc ξ says that ξ is the explicit input which is built from (w₀, rc, a seed)
and an instance x, and that the relation proper holds of the index w₀, the instance x and the
witness, which here is computed from the index and the explicit input (`Prover.trace`).
`Committer.rel` (Honest/Committer.lean) has this form. Any other clause on rc excludes a set of
values of the stored tables' pads and encoding randomness, which somebody has to measure; a clause
that excludes indices or instances is a choice of the relation and costs nothing. Nothing here
restricts `Rel` to that form. -/
structure Owed (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (Rel : W₀ → Rc → Xi → Prop) : Prop where
  /-- the description passes its own tests on the plan -/
  plan : F.planOk = true
  /-- the book passes its tests at the description -/
  book : Bk.word F = none
  /-- no two sub-protocols of the description are at one place, so "the sub-protocol at the place"
  is unique -/
  places : F.placesOk = true
  /-- every list of parts is at a place of its chain: an executable test. Its sub-protocol is then
  one of the description's own by construction -/
  seats : G.seated = true
  /-- each side meets `Good`, with the earlier chains' rounds by `earlierOf`, and with what the
  field holds beside its A and B. In the first and the shared chain no column has been opened at the
  start (`some []`); in the second chain what the two earlier chains have opened is: all values are
  asked. At this book, at the description's own order of places, at its chain's `Face` and numbers,
  and at its own parameters; `acc` outside its chain's falls -/
  good : (∀ L ∈ G.first, (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
        F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
    (∀ L ∈ G.shared, (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
        F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
    ∀ L ∈ G.second, ∀ base skip,
      (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
        F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃
  /-- at every input: none of the errors of Honest/Frame.lean's functions that depend on the input
  and are no stop. What all requests share is in range, and the request has a trace. (The third such
  error, a stored column that is not available, is excluded by `runs`, outside the silent set.) -/
  input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true
  /-- at every input, all coins and every list of challenges that the rounds can draw, outside the
  one silent set, whether a fall occurs or not: `runC` returns a run. (Whether the description then
  accepts is not asked here.) -/
  runs : ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins Bk) ρ, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    ∃ r, runC F Bk (G.prover H) w₀ rc x k ρ = .ok r
  /-- and there, of that run's own values, as conclusions: `bud` holds at every part, and `On` at
  every part that the run has called, at the walk's own state before the part -/
  owed : ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins Bk) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
    (∀ L ∈ G.first, L.owedAt F.first.blocksInOrder k 0
      (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
    (∀ L ∈ G.shared, L.owedAt F.shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called) ∧
    ∀ L ∈ G.second, L.owedAt F.second.blocksInOrder k 2
      (fun a => orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called

end ProofFile.Honest

#print axioms ProofFile.Honest.earlierOf
#print axioms ProofFile.Honest.orRefused
#print axioms ProofFile.Honest.Lettered.withField
#print axioms ProofFile.Honest.Owed
