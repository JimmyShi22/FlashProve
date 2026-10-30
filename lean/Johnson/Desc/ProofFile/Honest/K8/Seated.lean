-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/Seated.lean: THE SMALLNESS TEST AT ITS OWN MEMBER OF A CHAIN's FLAT
LIST, at which the matrix is drawn: THE NAMED PREMISES ON A THREAD's LETTERS, GATHERED IN RECORDS,
AND THE KIND's DEBTS THERE, STATED IN THE THREAD's FORM
(Johnson/Desc/ProofFile/Honest/Thread/Thr.lean, Pays.lean). The thread T, the member's number b and
its block blk are variables. Definitions of type Prop alone: NO PROOF STANDS HERE: the proofs are
Honest/K8/SeatedPlays.lean's and SeatedLaws.lean's. None is one of the library's goals.

THE RECORDS. Each field is a fact on a letter of T, on blk, or on the half's public data: an
equation, or an implication. Nothing shows here that any thread has them.
  `K8Seated T b blk cells P`   THE SEAT. `here`: blk is the member number b · `seats`: blk is seated
      over the draw's block at the place's numbers: the same declared rounds, and a yes of blk is a
      yes of that block behind which no mark stands, both ways (`Seats`,
      Johnson/Desc/First/K8/LawSeated.lean) · `oracles`: it states one round's empty list of oracle
      messages · `half`: the half that stands at its place is the kind's (`smallHalf`,
      Honest/K8/Part.lean) · `named`: THE SEAT's TEST ON PUBLIC DATA (`smallFits`) · `sees`: the
      chain's face shows the second stop the whole input
  `K8Ready T b p` WHAT THE DECISION ASKS OF THE STATE IN FRONT, AS AN IMPLICATION FROM THE TWO
      LETTERS form AND formP AT b: `ReadyAt p s` is the left half of the library's `MeansAtS`, with
      "no mark". BY THE LIBRARY's `step_seats_iff`, AS READ, A YES ASKS OF THE STATE JUST THIS: SO
      IT IS THE WHOLE CONTENT OF `small_accepted`. Whether a chain's formP says it at this border is
      not held here; if it does not, the same debt can be asked from the thread with what is said of
      reached states, or by the cut "structure | values" (Carries, Returns, Values over a shape)
  `K8Letters T b p`   THE FORM, THE RIDERS AND keeps BEHIND THE MEMBER. `keeps`: the kind's own
      clause (`K8Keeps`, Johnson/Desc/K8/Honest/Keeps.lean), with "no mark behind", gives the letter
      at b · `form`, `formP`, `rides`: each passes from b to b + 1 across a yes
  `K8Items T b cells P A iS iD`   THE TWO ITEMS THAT ARE THE KIND's TO FILL. A: a reader that is a
      letter of the record: the table of cells of a witness (T.Wt is a letter that is a type) ·
      `small`, `digits`: the library's two sentences behind the draw (`SmallAt`, `DigitsAt`,
      Johnson/Desc/First/K8/LawItems.lean) give what the items iS, iD mean · `tie`, `zz`: THE
      WITNESS IS MADE OF THE INPUT's CELLS: its symbol arrays and vector of reads (`TieBy`), and,
      from the draw's challenge on, its array of digits (`ZzBy`, Honest/K8/SmallLaw.lean) ·
      `fine`: the library's two conditions more on the state behind, and its test on the digits'
      columns · `some`: the place has a matrix
THE DEBTS, each a definition of a proposition (`Spec.…`):
  `small_plays`      K8Seated → Plays T b
  `small_accepted`   K8Seated → K8Ready → Accepted T fall b, AT EVERY fall: the member's step tests
                     no value
  `small_behind`     K8Seated → K8Letters → Behind T b
  `small_exchange`   K8Seated → K8Items → the sentence of Exchange T b at the two items
WHERE EACH FIELD OF THE SEAT IS SPENT, BY THE PROOFS' TEXT (Honest/K8/SeatedPlays.lean,
SeatedLaws.lean): half, oracles, the rounds of `seats` and the first clause of `named`: in all four
· here: in the first three · the yes of `seats`: in the last three · `sees`: a premise of the lemma
`seated_moved`; what it yields (the second stop's silence, at the input's own cells) is spent in the
exchange alone · the second clause of `named`: nowhere.
Limits. `K8Ready`, `K8Letters.formP` and `K8Items.tie`, `zz`, `fine` are no unfoldings: they have
content, and who pays each is not said here. `small_behind` IS LITTLE MORE THAN A RE-BUNDLING: its
own content is that a yes of the seated block gives `K8Keeps`, `MeansAtS` and no mark, and that what
was handed to the chain is unturned. Of the row's other owed items (the two pins) nothing. RidesPast
is not stated. The kind's runs at the two later members are not of this member. A made-up thread at
which `K8Seated`, `K8Ready` and `K8Letters` hold together, with a stand at which its sentence holds:
Honest/K8/SeatedToy.lean; of `K8Items` there is no member.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.K8.DrawBridge
import Johnson.Desc.K8.Honest.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS Seats approximateRangeProofDrawKind atS tabs SmallAt DigitsAt Extra)
open VerifiableInference.Desc.First.K8.Honest

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- **The seat.** -/
structure K8Seated (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) : Prop where
  here : T.bs[b]? = some blk
  seats : Seats blk (approximateRangeProofDrawKind (Cl := Claim) atS P.1)
  oracles : blk.oracles = [[]]
  half : (T.hs.find? fun g => g.place == blk.place) = some (smallHalf cells P)
  named : smallFits P = true
  sees : ∀ w, T.φ.sees w = some w

/-- What the decision asks of the state in front: `MeansAtS` without the round and the state
behind; and no mark. -/
def ReadyAt (p : Par) (s : S) : Prop :=
  s.failed = none ∧ ∃ tl : HTailF2, s.tl? = some tl ∧ tl.funClosed = true ∧
    (s.rowsOwed = none ∨ s.rowsOwed = some 0) ∧ (tl.cfF.size = 0 ∧ tl.foldDrawn = 0) ∧
    tl.NM = p.ks.length ∧ tl.mats.toList.map (·.k) = p.ks ∧ tl.mats.toList.map (·.m) = p.ms ∧
    tl.tau = p.tau ∧ (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p

/-- An implication from the two letters of (P) at b: where the form holds the state is ready. -/
def K8Ready (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (p : Par) : Prop :=
  ∀ a s, T.form b (a, s) = true → T.formP b (a, s) → ReadyAt p s

/-- **(P), (R) and keeps behind the member.** -/
structure K8Letters (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (p : Par) : Prop where
  keeps : ∀ s s', K8Keeps s s' → s'.failed = none → T.keeps b s s'
  form : ∀ a s s', T.form b (a, s) = true → K8Keeps s s' → s'.failed = none →
    T.form (b + 1) (a, s') = true
  formP : ∀ a s r s', T.formP b (a, s) → MeansAtS p s r s' → T.formP (b + 1) (a, s')
  rides : ∀ w s s', T.rides b w s → K8Keeps s s' → s'.failed = none → T.rides (b + 1) w s'

/-- **The two items that are the kind's to fill.** -/
structure K8Items (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) (A : T.Wt → TableE)
    (iS iD : T.ι) : Prop where
  small : ∀ w a y v, SmallAt A a.2 v → T.means w iS a y v
  digits : ∀ w a y v, DigitsAt A a.2 v → T.means w iD a y v
  tie : ∀ k s m E s' tl' e, Thr T b k s m E → K8Keeps s s' → s'.tl? = some tl' →
    TieBy tl' (A (T.wit k m.st.input (m.st.heard ++ e))) (cellsAtOf (cells m.st.input.trace) P.2)
  zz : ∀ k s m E s' tl' (d : Fmt.Drawn) e, Thr T b k s m E → K8Keeps s s' → s'.tl? = some tl' →
    tl'.cfF = d.trits.toArray →
    ZzBy tl' (A (T.wit k m.st.input (m.st.heard ++ d :: e)))
      (cellsAtOf (cells m.st.input.trace) P.2)
  fine : ∀ k s m E s' tl', Thr T b k s m E → K8Keeps s s' → s'.tl? = some tl' →
    Extra s' ∧ DgP.colsTest tl' = true
  some : P.1.ks ≠ []

namespace Spec

/-- States: IT PLAYS. -/
def small_plays : Prop :=
  ∀ (W₀ Rc Xi Tr X Pb : Type) (Bk : ProverCoinCounts)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)),
    K8Seated T b blk cells P → Plays T b

/-- States: IT IS ACCEPTED, at every fall. -/
def small_accepted : Prop :=
  ∀ (W₀ Rc Xi Tr X Pb : Type) (Bk : ProverCoinCounts)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (fall : Nat → S → List Fmt.Drawn → Option String),
    K8Seated T b blk cells P → K8Ready T b P.1 → Accepted T fall b

/-- States: BEHIND ITS YES. -/
def small_behind : Prop :=
  ∀ (W₀ Rc Xi Tr X Pb : Type) (Bk : ProverCoinCounts)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)),
    K8Seated T b blk cells P → K8Letters T b P.1 → Behind T b

/-- States: THE EXCHANGE, at the two items. -/
def small_exchange : Prop :=
  ∀ (W₀ Rc Xi Tr X Pb : Type) (Bk : ProverCoinCounts)
    (T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat)
    (blk : Block S Claim) (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (A : T.Wt → TableE) (iS iD : T.ι),
    K8Seated T b blk cells P → K8Items T b cells P A iS iD →
    ∀ k s m E ds y cols s', Thr T b k s m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k s m E ds y cols s' → T.Items [iS, iD] k s' y.2 (E.add y.1)

end Spec

end ProofFile.Honest.K8
