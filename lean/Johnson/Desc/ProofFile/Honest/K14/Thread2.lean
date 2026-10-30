-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Thread2.lean: kind K14: THE SHARED CHAIN's LETTERS, AS FAR AS THEY
ARE THIS KIND's TO LAY: a term of SharedThread.Letters (Honest/Thread/Shared.lean). Definitions, and
small lemmas on them.

Words of the frame (Honest/Thread/Thr.lean): a thread is a sentence on a run of the honest prover at
each border of a chain; a member is a sub-protocol of the chain's list, by its number from 0; the
border b stands in front of the member b; a letter is a field of the thread that its maker lays. The
2 in this file's names: the shared chain is the second of a proof file's three.

Main names:
  num                 the three sampled messages' numbers in the chain's own statement: 0, 2, 3: the
                      plan's where two messages go out with o_u (PlanFacts has that) and no message
                      stands in front
  WitLens, WitLens.words, WitLens.snd   **THE WITNESS's TYPE Wt IS A VARIABLE**: how this kind reads
                      a family of words off a witness (get) and lays one into it (set), with two
                      laws. Two terms: the witness is a family of words; the witness is a pair whose
                      second component is one. THE LIBRARY HAS THE LIKE: Lens S P with Lens.Lawful
                      and Lens.id (Johnson/Desc/Lens.lean): WitLens Wt is a Lens Wt (Words …)
                      bundled with the first two of its three laws
  mgWords ℓ Q N Mg₀   what this kind's and the sendings' shared items say, OF THE WORDS THAT ℓ READS
                      OFF THE WITNESS. Every other field stays Mg₀'s: the committed table's pin, and
                      all fields of the slot's own items
  form2, form2_eq     the form at a border: between 2 and 9 the kind's book-keeping (shapeK at the
                      plan's numbers) and: the state's codes are the plan's; elsewhere a letter
  laid2, keeps2   what one of the eight leaves: at four of them QuietStep; at "LIN zeta" the
                  statement; at the two sendings what the items that go past them read; AND what
                  "LIN point", the two sendings and "LIN zeta" have laid, in the library's own
                  relations, the sendings' at this kind's own public parameters (laid2): at "LIN
                  point" and "LIN zeta" every field of the state behind BUT THE NOTED POINT, of
                  which it says only that it is some round's drawn elements: any list; at a sending
                  all but three things of a new message (laid2's docstring names them)
  keepsAll, keepsAll_eq   the thread's letter keeps AT EVERY MEMBER OF THE CHAIN: at the members 1
                      to 8 keeps2; elsewhere a letter of Others. The letter rides is Others's AT
                      EVERY BORDER: this kind lays no clause on it
  rvOf, noChallenge, firstRv   the first challenge heard, as a round
  Others              THE LETTERS THAT ARE NOT THIS KIND's: the planner's chains, the two proximity
                      tests, the closing, the table's numbers, Mg₀, the form outside 2 to 9, the
                      test that nothing is left, the halves, the trees' tables and from which
                      challenge on each is fixed, the committed table, how many trees the first and
                      the shared chain send (n₁, n₂), which inputs are valid, keeps outside
                      the eight, rides, what an honest prover holds, how the witness is read and
                      written (lens), and the witness but for the words at the numbers of Ours
                      (rest)
  Ours Q sentU o      the number o lies in one of two stretches: o < sentU.size, or
                      2 ≤ o < 2 + the number of messages that go out with o_omega (withOmega Q.S).
                      sentU IS ANY ARRAY: THESE ARE THIS KIND's FOUR MESSAGES' NUMBERS, 0 TO 3, ONLY
                      UNDER PlanFacts (Johnson/Desc/K14/Honest/YesChain.lean: sentU has two members,
                      and the shape splits, so that two go out with o_omega). At a longer sentU the
                      two stretches overlap. The lemmas hold at every sentU
  holdsAt, witAll     the witness's WORDS at every number: at the numbers of Ours the honest words;
                      elsewhere the words of the letter rest, which may hang on the challenges heard
  words2_rest, words2_ours, wit_of_agree, witAll_idem   **a family of words that agrees with the
                      honest words at the numbers of Ours is witAll over itself**; witAll, laid over
                      its own result, returns it
  witL, get_witL, witL_snd_fst, witL_of_agree, witL_idem   the witness, of any type: witAll's words
                      laid into the letter rest; the words read off it are witAll's; at the pair its
                      first component is rest's; the two laws above at it
  letters2 Q sentU O Cl   **the term.** bs: the shared chain carried to the type Cl of claims, as a
                      proof file's IOP holds it; order: the statement is in order; item: the item at
                      which the kind's rounds read the committed table; the witness: witL: at the
                      numbers of Ours its words are the honest words (words2:
                      Johnson/Desc/K14/Honest/ChainHolds.lean), off what the prover holds and the
                      first challenge heard

Two choices that a reader should weigh. A message's pin is laid as "the state holds its sample
constraints, and they hold of the words": AT THESE LETTERS THE ITEMS pin m AND row (.sample m) ARE
ONE SENTENCE. The constraints are said at the state's own statement, not in the library's forms
(Johnson/Desc/K14/Honest/ItemsOwn.lean says why).

WHAT THE TERM STILL LAYS FOR MEMBERS THAT ARE NOT THIS KIND's, in one place: order: "the statement
is in order" AT EVERY BORDER OF THE CHAIN; the meanings of pin, row, nearU, recRow and omU at all
borders; first, item and split for the whole chain; the witness's words at the numbers of Ours. HOW
MANY BORDERS THERE ARE IS NOT FIXED HERE: the chain is the front, the library's eight, the letter
tests and the closing (chainOf, Johnson/Desc/K14/Blocks.lean), and tests is a list of any length.
Where it has two members and the library makes its eight there are twelve members and thirteen
borders: there «Behind» at the members 0, 9, 10 and 11 owes the order, and the five meanings are
read at the borders 9 to 12 too. split IS LAID true AT EVERY Q, also at a Q whose shape does not
split: so the term is for shapes that split.

What is not claimed. Every field of Others is a letter: no sentence here ties the field holds to the
fields table or stored. NO ITEM OF THE THREAD TIES THE WORDS words2 TO THE TABLES THAT STAND SENT.
That the thread holds at any run. Nothing on any property.
Who calls them: witL_snd_fst is called by no other file.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shared
import Johnson.Desc.K14.Honest.RidesQuiet
import Johnson.Desc.K14.Honest.FlatSteps
import Johnson.Desc.Key.Laid.DrawsDef
import Johnson.Desc.Key.Laid.Laid2Def

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Means (Words InOrder)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Shared (Msg2 NumbersS MeaningS)
open Desc.K14 (P14 St chainOf first)
open Desc.K14.Honest (Inputs SmpOwn SendStep words2)
open Desc.K14.Law (NearAt RecAll OmU RowsU RowsO FoldAt uRK colsOf shapeK codX QuietStep parU parO)

/-- The numbers of the shared chain's three sampled messages in its own statement, by the plan. (The
message number 1 is the first mask, which is not sampled.) -/
def num : Msg2 → Nat
  | .oU => 0
  | .oOmega => 2
  | .oSp => 3

/-- **HOW THIS KIND READS AND WRITES A WITNESS OF ANY TYPE**: a family of words is read off it (get)
and laid into it (set): what is laid is read; laying what is read changes nothing. -/
structure WitLens (Wt : Type) where
  get : Wt → Words Cb.Gl.E
  set : Wt → Words Cb.Gl.E → Wt
  get_set : ∀ a v, get (set a v) = v
  set_get : ∀ a, set a (get a) = a

/-- The witness is a family of words. -/
def WitLens.words : WitLens (Words Cb.Gl.E) :=
  ⟨fun v => v, fun _ v => v, fun _ _ => rfl, fun _ => rfl⟩

/-- The witness is a pair whose second component is a family of words. -/
def WitLens.snd (α : Type) : WitLens (α × Words Cb.Gl.E) :=
  ⟨fun a => a.2, fun a v => (a.1, v), fun _ _ => rfl, fun _ => rfl⟩

/-- **What this kind's and the sendings' shared items say**: of the family of words that ℓ reads off
the witness. The kind's claims in the forms of the kind's laws (Johnson/Desc/K14/Law/LedgerOne.lean:
mgI), at distance 0; the constraints and the sample constraints AT THE STATE's OWN STATEMENT; a
message's pin: the state holds its sample constraints, and they hold of the words: asked of each
sampled message whose tenant (N.tenant) is the pair (j, t): so it is true at a pair that is no
sampled message's tenant, and asks both where two messages have one tenant. Mg₀: ALL OTHER
FIELDS STAY ITS OWN: the committed table's pin, and every field of the slot's own items (the first
chain's pin, the claim on the cells, (Dot), (Eval), "no mark"): nothing is laid for them here. -/
def mgWords {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : P14) (N : NumbersS) (Mg₀ : MeaningS St P₁ Wt) :
    MeaningS St P₁ Wt :=
  { Mg₀ with
    pin := fun j t s _ w => ∀ m, N.tenant m = (j, t) → SmpOwn (num m) s (ℓ.get w)
    nearU := fun s y w => NearAt rdE Q.par (uRK Q.par s) (ℓ.get w) (colsOf y.cell) 0
    recRow := fun s w => RecAll rdE Q.par (uRK Q.par s) (ℓ.get w)
    omU := OmU Q.par (uRK Q.par) ℓ.get
      (fun w y => ℓ.get w 2 .main ((linLayOmega Q.codes Q.par.S).index y))
    row := fun c s w =>
      match c with
      | .sample m => SmpOwn (num m) s (ℓ.get w)
      | .recG => RowsU rdE 0 Q.par.S.fold.index.answers s (ℓ.get w)
      | .loc => RowsU rdE Q.par.S.fold.index.answers Q.par.S.fold.columns s (ℓ.get w)
      | .fold => FoldAt rdE Q.par.S s (ℓ.get w)
      | .foldU => RowsU rdE (Q.par.S.fold.index.answers + Q.par.S.fold.columns) 1 s (ℓ.get w)
      | .foldOmega => RowsO rdE 0 1 s (ℓ.get w) }

/-- The form at a border: between 2 and 9 the kind's book-keeping at the plan's numbers, and: the
state's codes are the plan's. Elsewhere: a letter. -/
def form2 (Q : P14) (other : Nat → St → Bool) (b : Nat) (s : St) : Bool :=
  if 2 ≤ b ∧ b ≤ 9 then shapeK Q.par 0 2 Q.par.S.fold.columns b s && codX Q b s else other b s

/-- Between 2 and 9 it is these two tests. -/
theorem form2_eq (Q : P14) (other : Nat → St → Bool) (b : Nat) (s : St) (h : 2 ≤ b ∧ b ≤ 9) :
    form2 Q other b s = (shapeK Q.par 0 2 Q.par.S.fold.columns b s && codX Q b s) := if_pos h

/-- **What "LIN point", the two sendings and "LIN zeta" have laid**: the library's own relations
(Johnson/Desc/Key/Laid/DrawsDef.lean, Laid2Def.lean), the sendings' at this kind's own public
parameters. At "LIN point" and "LIN zeta": every field of the state behind but the noted point
(psiSh | zFd), of the state in front. OF THE NOTED POINT ONLY THAT IT IS SOME ROUND's DRAWN
ELEMENTS: ANY LIST IS THAT: r is bound by "there is" and tied to no round that the member has heard:
the letter keeps sees two states and no round. (The library's laid_point and linZeta_inv name the
round; laid2_step, Honest/K14/Debts2.lean, lets it go.) At a sending: what the kind notes; that the
codes in front are the sending's parameters'; the statement's codes, groups and elder messages; that
what is opened is kept; how many messages are new; the book and the count of roots behind; that "in
order" is kept. OF A NEW MESSAGE: its shape; that it is in no group and not spent; whether it is
sampled; the number of its sample constraints; its ledger where it has answers. UNSAID OF IT: the
entries of its sample constraints; its pad; its ledger where it has no answer. PointLaid is meant
where the shape splits, Laid22 where the masks go ahead. -/
def laid2 (Q : P14) (sentU : Array OracleNotice) (b : Nat) (s s' : St) : Prop :=
  (b = 1 → ∃ r, VerifiableInference.Desc.Key.PointLaid Q.par s s' r) ∧
    (b = 2 → VerifiableInference.Desc.Key.LaidW.Laid22 Q.par.S (parU Q sentU) s s') ∧
    (b = 5 → VerifiableInference.Desc.Key.LaidW.Laid25 (parO Q) s s') ∧
    (b = 7 → ∃ r, VerifiableInference.Desc.Key.ZetaLaid s s' r)

/-- What the sub-protocol behind a border leaves. FIRST, IN THE FORM IN WHICH «RidesPast» SPENDS IT:
at "(rec_gamma)", "LOC", the joinings and "SPLIT": what the kind notes, the messages and the book;
at "LIN zeta": the statement, and which group is o_u's; at the sending of o_u: the point as it is
noted, and: read with o_u noted as the message to come (uRK), the state in front notes of the point,
of o_u and of the key what the state behind notes; at the second sending: what is noted of the
point, of o_u and of its group, and of the statement the codes, the groups and the messages that
were there. LAST: laid2: what "LIN point", the two sendings and "LIN zeta" have laid. -/
def keeps2 (Q : P14) (sentU : Array OracleNotice) (b : Nat) (s s' : St) : Prop :=
  ((b = 3 ∨ b = 4 ∨ b = 6 ∨ b = 8) → QuietStep s s') ∧
    (b = 7 → s'.st = s.st ∧ s'.loc.gU = s.loc.gU) ∧
    (b = 2 → s'.loc.psiSh = s.loc.psiSh ∧ (uRK Q.par s').loc.psiSh = (uRK Q.par s).loc.psiSh ∧
      (uRK Q.par s').loc.oU = (uRK Q.par s).loc.oU ∧
      (uRK Q.par s').loc.key = (uRK Q.par s).loc.key) ∧
    (b = 5 → s'.loc.psiSh = s.loc.psiSh ∧ (uRK Q.par s').loc.oU = (uRK Q.par s).loc.oU ∧
      s'.loc.gU = s.loc.gU ∧ SendStep s.st s'.st) ∧
    laid2 Q sentU b s s'

/-- What a sub-protocol leaves, at every member of the chain: at the members 1 to 8 keeps2;
elsewhere a letter. -/
def keepsAll (Q : P14) (sentU : Array OracleNotice) (other : Nat → St → St → Prop) (b : Nat)
    (s s' : St) : Prop :=
  if 1 ≤ b ∧ b ≤ 8 then keeps2 Q sentU b s s' else other b s s'

/-- At the members 1 to 8 it is keeps2. -/
theorem keepsAll_eq (Q : P14) (sentU : Array OracleNotice) (other : Nat → St → St → Prop) (b : Nat)
    (s s' : St) (h : 1 ≤ b ∧ b ≤ 8) : keepsAll Q sentU other b s s' = keeps2 Q sentU b s s' :=
  if_pos h

/-- The round in which the challenges d were sampled and nothing is shown. -/
def rvOf (d : Fmt.Drawn) : Fmt.RoundView := ⟨[], d⟩

/-- No challenge. -/
def noChallenge : Fmt.Drawn := ⟨[], [], [], none⟩

/-- The first of the challenges heard, as such a round; no challenge where none was heard. -/
def firstRv (h : List Fmt.Drawn) : Fmt.RoundView := rvOf (h.headD noChallenge)

/-- **The letters that are not this kind's to lay.** -/
structure Others (Bk : ProverCoinCounts) (W₀ Rc X₀ P₁ Wt : Type) where
  /-- how this kind reads and writes the witness -/
  lens : WitLens Wt
  /-- the planner's chains -/
  c : Model.Verify.Chains
  /-- the proximity tests' sub-protocols: meant are two; the type allows a list of any length -/
  tests : List (Block St Unit)
  /-- the chain's closing, as a function of the sub-protocols in front of it -/
  last : List (Block St Unit) → Block St Unit
  /-- the table's numbers -/
  N : NumbersS
  /-- the items' meaning, for every field that this kind does not lay -/
  Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt
  /-- the form outside the borders 2 to 9 -/
  shape : Nat → St → Bool
  /-- the test that nothing is left -/
  nothingLeft : St → Bool
  /-- the prover's halves -/
  hs : List (Placed Empty (Common W₀ Rc TableKey) X₀)
  /-- the trees' tables -/
  table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table
  /-- from which challenge on each tree's table is fixed -/
  fixed : Fmt.TreeSource → Nat
  /-- the committed table -/
  stored : Common W₀ Rc TableKey → Nat → Nat → Option (List UInt64)
  /-- how many trees the first chain sends -/
  n₁ : Nat
  /-- how many trees the shared chain sends -/
  n₂ : Nat
  /-- which inputs are valid -/
  valid : Common W₀ Rc TableKey → Prop
  /-- what a member outside 1 to 8 leaves -/
  keeps : Nat → St → St → Prop
  /-- the thread's further clause, at every border -/
  rides : Nat → Common W₀ Rc TableKey → St → Prop
  /-- what an honest prover holds, of a run's coins and the input; its field w₀ is not read -/
  holds : Coins Bk → Common W₀ Rc TableKey → Inputs
  /-- the witness but for the words at the numbers of Ours: of a run's coins, the input and the
  challenges heard -/
  rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type}

/-- What the prover holds, with ALL the words that are read off the letter rest laid in as w₀, those
at the numbers of Ours too; that the honest words do not read them there is words2_ours. -/
def holdsAt (O : Others Bk W₀ Rc X₀ P₁ Wt) (k : Coins Bk) (w : Common W₀ Rc TableKey)
    (h : List Fmt.Drawn) : Inputs :=
  { O.holds k w with w₀ := O.lens.get (O.rest k w h) }

/-- **The witness's words at every number**: at the numbers of Ours (this kind's four messages'
under PlanFacts) the honest words; elsewhere a letter. -/
noncomputable def witAll (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) : Words Cb.Gl.E :=
  words2 Q sentU (first Q.codes w.key) (firstRv h) { holds k w with w₀ := rest k w h }

/-- The number o lies in one of two stretches: below sentU.size, or from 2 on and below 2 + the
number of messages that go out with o_omega. sentU is any array. Under PlanFacts (sentU has two
members, and the shape splits) these are the numbers 0 to 3 of this kind's four messages; at a
longer sentU the two stretches overlap. -/
def Ours (Q : P14) (sentU : Array OracleNotice) (o : Nat) : Prop :=
  o < sentU.size ∨ (2 ≤ o ∧ o < 2 + (Desc.K14.withOmega Q.S).size)

/-- At a number that is not of Ours the honest words are the words in front. -/
theorem words2_rest (Q : P14) (sentU : Array OracleNotice) (key : TableKey) (r : Fmt.RoundView)
    (H : Inputs) (o : Nat) (ho : ¬ Ours Q sentU o) (part : OnBytes.Part) (i : Nat) :
    words2 Q sentU (first Q.codes key) r H o part i = H.w₀ o part i := by
  have h1 : ¬ (0 ≤ o ∧ o < 0 + sentU.size) := fun c => ho (Or.inl (by omega))
  have h2 : ¬ (0 + 2 ≤ o ∧ o < 0 + 2 + (Desc.K14.withOmega Q.S).size) :=
    fun c => ho (Or.inr (by omega))
  show (if 0 + 2 ≤ o ∧ o < 0 + 2 + (Desc.K14.Law.parO Q).sent.size then _ else
    if 0 ≤ o ∧ o < 0 + (Desc.K14.Law.parU Q sentU).sent.size then _ else H.w₀ o part i) = _
  rw [Desc.K14.Law.parK1_sent, Desc.K14.Law.parK1_sent, if_neg h2, if_neg h1]

/-- At a number of Ours they do not hang on the words in front. -/
theorem words2_ours (Q : P14) (sentU : Array OracleNotice) (key : TableKey) (r : Fmt.RoundView)
    (H : Inputs) (v : Words Cb.Gl.E) (o : Nat) (ho : Ours Q sentU o) (part : OnBytes.Part)
    (i : Nat) :
    words2 Q sentU (first Q.codes key) r { H with w₀ := v } o part i =
      words2 Q sentU (first Q.codes key) r H o part i := by
  show (if 0 + 2 ≤ o ∧ o < 0 + 2 + (Desc.K14.Law.parO Q).sent.size then _ else
    if 0 ≤ o ∧ o < 0 + (Desc.K14.Law.parU Q sentU).sent.size then _ else v o part i) =
    (if 0 + 2 ≤ o ∧ o < 0 + 2 + (Desc.K14.Law.parO Q).sent.size then _ else
    if 0 ≤ o ∧ o < 0 + (Desc.K14.Law.parU Q sentU).sent.size then _ else H.w₀ o part i)
  rw [Desc.K14.Law.parK1_sent, Desc.K14.Law.parK1_sent]
  by_cases h2 : 0 + 2 ≤ o ∧ o < 0 + 2 + (Desc.K14.withOmega Q.S).size
  · rw [if_pos h2, if_pos h2]
    rfl
  · have h1 : 0 ≤ o ∧ o < 0 + sentU.size := by
      rcases ho with c | c
      · omega
      · exact absurd (by omega) h2
    rw [if_neg h2, if_neg h2, if_pos h1, if_pos h1]
    rfl

/-- **A family of words that agrees with the honest words at the numbers of Ours is witAll over
itself.** -/
theorem wit_of_agree (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (W : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    (h : ∀ k w l o part i, Ours Q sentU o → W k w l o part i =
      words2 Q sentU (first Q.codes w.key) (firstRv l) (holds k w) o part i) :
    W = witAll Q sentU holds W := by
  funext k w l o part i
  unfold witAll
  by_cases ho : Ours Q sentU o
  · rw [words2_ours Q sentU _ _ _ _ o ho, h k w l o part i ho]
  · rw [words2_rest Q sentU _ _ _ o ho]

/-- witAll, laid over its own result, returns it. -/
theorem witAll_idem (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E) :
    witAll Q sentU holds rest = witAll Q sentU holds (witAll Q sentU holds rest) :=
  wit_of_agree Q sentU holds _ fun _ _ _ o part i ho => words2_ours Q sentU _ _ _ _ o ho part i

/-- **The witness, of any type**: into the letter rest the words of witAll are laid, made over the
words that are read off rest. -/
noncomputable def witL (ℓ : WitLens Wt) (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) : Wt :=
  ℓ.set (rest k w h) (witAll Q sentU holds (fun k w h => ℓ.get (rest k w h)) k w h)

/-- The words that are read off it are witAll's. -/
theorem get_witL (ℓ : WitLens Wt) (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    ℓ.get (witL ℓ Q sentU holds rest k w h) =
      witAll Q sentU holds (fun k w h => ℓ.get (rest k w h)) k w h := ℓ.get_set _ _

/-- At the pair the first component is the letter rest's: this kind writes nothing there. -/
theorem witL_snd_fst (α : Type) (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → α × Words Cb.Gl.E) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    (witL (WitLens.snd α) Q sentU holds rest k w h).1 = (rest k w h).1 := rfl

/-- **A witness whose words agree with the honest words at the numbers of Ours is witL over it.** -/
theorem witL_of_agree (ℓ : WitLens Wt) (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (W : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
    (h : ∀ k w l o part i, Ours Q sentU o → ℓ.get (W k w l) o part i =
      words2 Q sentU (first Q.codes w.key) (firstRv l) (holds k w) o part i) :
    W = witL ℓ Q sentU holds W := by
  funext k w l
  unfold witL
  rw [← wit_of_agree Q sentU holds (fun k w l => ℓ.get (W k w l)) h, ℓ.set_get]

/-- witL, laid over its own result, returns it. -/
theorem witL_idem (ℓ : WitLens Wt) (Q : P14) (sentU : Array OracleNotice)
    (holds : Coins Bk → Common W₀ Rc TableKey → Inputs)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt) :
    witL ℓ Q sentU holds rest = witL ℓ Q sentU holds (witL ℓ Q sentU holds rest) :=
  witL_of_agree ℓ Q sentU holds _ fun k w l o part i ho => by
    rw [get_witL]
    exact words2_ours Q sentU _ _ _ _ o ho part i

/-- **THE SHARED CHAIN's LETTERS, AS FAR AS THEY ARE THIS KIND's.** Cl: the file's type of claims.
The witness: the letter rest, with the honest words laid in, off what the prover holds and the first
challenge heard. THE FIELD split IS LAID true AT EVERY Q, also at a Q whose shape does not split:
the thread's table of items and its list of places are read at split = true, so the term is for
shapes that split. -/
noncomputable def letters2 (Q : P14) (sentU : Array OracleNotice) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt where
  split := true
  N := O.N
  Mg := fun w => mgWords O.lens Q O.N (O.Mg₀ w)
  shape := form2 Q O.shape
  nothingLeft := O.nothingLeft
  order := fun s => InOrder s.st
  bs := ((chainOf O.c Q O.tests O.last).retype (Cl' := Cl)).blocksInOrder
  hs := O.hs
  wit := witL O.lens Q sentU O.holds O.rest
  table := O.table
  fixed := O.fixed
  stored := O.stored
  first := first Q.codes
  item := Q.item
  n₁ := O.n₁
  n₂ := O.n₂
  valid := O.valid
  rides := O.rides
  keeps := keepsAll Q sentU O.keeps

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.form2_eq
#print axioms ProofFile.Honest.K14.keepsAll_eq
#print axioms ProofFile.Honest.K14.words2_rest
#print axioms ProofFile.Honest.K14.words2_ours
#print axioms ProofFile.Honest.K14.wit_of_agree
#print axioms ProofFile.Honest.K14.witAll_idem
#print axioms ProofFile.Honest.K14.get_witL
#print axioms ProofFile.Honest.K14.witL_snd_fst
#print axioms ProofFile.Honest.K14.witL_of_agree
#print axioms ProofFile.Honest.K14.witL_idem
