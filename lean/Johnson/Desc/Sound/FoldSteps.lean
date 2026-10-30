-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldSteps.lean: WHAT STANDS, AND WHAT ONLY GROWS, ALONG A LINK: one law a block
and one law a run, and what the fold's own text (Johnson/Desc/Block.lean) makes of them.
THE WITNESSES ARE PINNED: t,
u₀, w; t₁ and z too, as folds' values (two fields in `Traced`), and w₁ in the two
statements "…At" on the closing; THE BATCHING's LAW IS ALSO ASKED OF THE BLOCK THAT STANDS IN THE
FLAT LIST, AT THE LINK's OWN CLAIMS ALONE (`CallsAt`, between these two). A SHEET OF STATEMENTS:
definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN THIS FILE (the proofs:
Johnson/Desc/Sound/FoldStepsProofs.lean).

Why. A kind's law often speaks of SEVERAL moments of one link: its block's decision, at one record;
its runs of claims, which the batching calls later, at other records; and the record at which the
link's one equation speaks. It then asks that something laid at the first moment still stands at the
later ones (what was heard), or has only grown (a ledger). Who pays that? No kind alone: every block
and every run between the moments has to leave it, and the fold's text has to call them in a row.
Here: the one small law that each block and each run owes, general in the record; and the rest as
theorems about Block.lean's text.

The law. R: a relation between two records, reflexive and transitive (`Pre R`): "what matters
stands, or has only grown, from the first to the second".
  `Block.Steps R b`: where b's decision goes on, R holds from the record in front to the record
    behind.
  `Block.RunsStep R b`: the like for every run of claims of b. `Block.AfterStep R b`: for every run
    behind the batching.
  `Calls R Q batch`: THE BATCHING's LAW: where the batching's decision goes on, it has called the
    link's claims, as the one function that it is handed, at a record t with R from the record in
    front to t; the call went on; R holds from the record that the call left to the record behind;
    AND Q, a letter, holds of the record in front, the rounds shown, t, the claims, what the call
    left and the record behind: so the batching's files can say in Q what it did WITH THESE VERY
    CLAIMS.
  `CallsAt R Q B f`: the same of one block B and one function f. THE TRACES ASK `CallsAt R Q
    L.batched (claimsInBy L.each L.hear L.order)`: less than `Calls R Q L.batch` (`CallsAtOfCalls`).
(`Block.Leaves h`, Johnson/Desc/Sound/FoldHeard.lean, is `Block.Steps` at "h behind is h in front":
`StepsOfLeaves`.)

The link's own three blocks, by name: `Link.laid`, `Link.behind`, `Link.cleared`: Block.lean's text
of `Link.blocksInOrder`, cut; `FlatIs`: the flat list is these around the link's places: by rfl.

The statements.
  `FoldSteps`: along a fold of blocks that step, R holds from the first record to the last.
  `FoldAt`: a fold over pre ++ rest that goes on: THE FOLD OVER pre GOES ON, to a record m, the
    rounds behind those that pre declares, and some columns; R holds from the first record to m; and
    the fold over rest goes on from there to the same end. So a front is cut off, AND A TAIL: what
    is said of a fold over `Link.blocksInOrder` is had of a chain's fold over front ++ links ++ back.
    `FoldJoin`: the converse.
  `ClaimsTrace`: WHERE `claimsIn` GOES ON: R holds from its first record to its last, and EVERY RUN
    THAT THE ORDER NAMES WAS CALLED: at a record v with R from the first record to v; it went on; R
    holds from the record that it left to the last; and its claims are among the link's.
  `AfterSteps`: the like for `afterIn` (R from first to last).
  OVER Block.lean the batching is handed `claimsInBy L.each …`: `claimsIn` with the
    link's test behind each run; such a test can only refuse (`claimsIn_of_claimsInBy`,
    Johnson/Desc/BlockLaws.lean): so `ClaimsTrace` reaches it. "Behind the batching" runs
    `Link.runBehind`: the link's tests, which cannot turn the record, then `afterIn`.
  `LinkTrace`: THE LINK. L.hear = h₁ ++ b :: h₂. Where the fold over `Link.blocksInOrder` goes on from (s,
    rs, cols): t IS WHAT THE FOLD OVER laid :: h₁ GIVES FROM (s, rs, cols): a function's value: two
    traces agree on it; b's decision went on from t to t₁, at its own stretch of the rounds
    (`shownAt h₁ b rs`); u₀ IS WHAT THE FOLD OVER laid :: L.hear GIVES; R t₁ u₀;
    the batching's decision went on from u₀ to z, at its own stretch;
    it called the link's claims at u: they went on, to the claims cls and the record e: R u₀ u, R u
    e, R e z, and Q u₀ (its rounds) u cls e z;
    every run of b that the order names was called at a record v with R t₁ v, went on, left v' with
    R v' e, its claims among cls.
  `LinkTraceClose`: the like, ON TO A PLACE d OF THE CLOSING (L.close = c₁ ++ d :: c₂): w is what
    the fold over laid :: L.hear ++ [the batching, behind] ++ c₁ gives; R z w; d's decision went on
    from w.
  `Carries`, `RanAt`, `RanAtOfLink`, `RanAtToSettling`: the case "what was heard stands; the ledger
    only grows, with its sizes": at letters for the ledger's type, its order `later` and its test
    `sized`.

Every "there is", walked. t, u₀, w: values of named folds from (s, rs, cols). t₁, z (and w₁, in the
statements "…At"): values of named folds too; and of named decisions at these, at named rounds, at
the groups of columns gs that `Block.step` cuts (under "there is"). u, cls, e: the batching's own
call: what `Calls` gives; Q speaks of the same. v, v', the run and the number that it is handed:
`claimsIn`'s.

Limits. No block, run or batching of the protocol is named: `Steps`, `RunsStep` and `Calls` are
premises: ONE LAW A BLOCK, ONE A RUN, ONE FOR THE BATCHING. They run over ALL records, also those
that no run reaches. A block that refuses all has them for nothing. IT KEEPS "with its sizes"; IT
DOES NOT START IT: that the record t₁ holds a ledger with its sizes is a premise of the last two
statements' inner clause: whoever shows it of the place that opens the ledger speaks of the same t.
Nothing says that the batching calls the claims ONCE. No trace run by run for the runs behind the
batching. `Steps` through `andThen`, `lift`, `liftPart`, `inside`: not here. Nothing on soundness,
on acceptance, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-! ## 1 The laws -/

/-- Reflexive and transitive. -/
structure Pre (R : S → S → Prop) : Prop where
  refl : ∀ s, R s s
  trans : ∀ a b c, R a b → R b c → R a c

/-- Where the block's decision goes on, R holds from the record in front to the record behind. -/
def Block.Steps (R : S → S → Prop) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → R s s'

/-- The like for every run of claims of the block. -/
def Block.RunsStep (R : S → S → Prop) (b : Block S Cl) : Prop :=
  ∀ c ∈ b.claims, ∀ n s cl s', c.2 n s = .ok (cl, s') → R s s'

/-- The like for every run behind the batching. -/
def Block.AfterStep (R : S → S → Prop) (b : Block S Cl) : Prop :=
  ∀ c ∈ b.after, ∀ s s', c.2 s = .ok s' → R s s'

/-- **The batching's law**: where its decision goes on it has called the function that it was
handed. -/
def Calls (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (batch : (S → Except String (List Cl × S)) → Block S Cl) : Prop :=
  ∀ f s rs gs s', (batch f).decide s rs gs = .ok s' →
    ∃ t cls e, R s t ∧ f t = .ok (cls, e) ∧ R e s' ∧ Q s rs t cls e s'

/-- **The same of one block B and one function f**: where B's decision goes on, f was called. WHAT
THE TRACES ASK: of the link's batching as it stands in the flat list, at the link's own claims. So
it can be paid also where a link's field `batch` does not read its argument, and the block that
stands there was made with the link's claims by whoever laid it. -/
def CallsAt (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (B : Block S Cl) (f : S → Except String (List Cl × S)) : Prop :=
  ∀ s rs gs s', B.decide s rs gs = .ok s' →
    ∃ t cls e, R s t ∧ f t = .ok (cls, e) ∧ R e s' ∧ Q s rs t cls e s'

def CallsAtOfCalls : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (batch : (S → Except String (List Cl × S)) → Block S Cl), Calls R Q batch →
    ∀ f, CallsAt R Q (batch f) f

/-! ## 2 The link's own blocks, by name -/

/-- The link's first block: Block.lean's text. -/
def Link.laid (L : Link S Cl) : Block S Cl :=
  { roundlessBlock (L.name ++ ": laid") L.chain (some L.number) 0 L.lay with
      planOk := orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
        L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter }

/-- The batching at the link's claims. -/
def Link.batched (L : Link S Cl) : Block S Cl := L.batch (claimsInBy L.each L.hear L.order)

/-- The block that runs the runs behind the batching. -/
def Link.behind (L : Link S Cl) : Block S Cl :=
  roundlessBlock (L.name ++ ": behind the batching") L.chain (some L.number) (L.hear.length + 2)
    L.runBehind

/-- The link's last block. -/
def Link.cleared (L : Link S Cl) : Block S Cl :=
  roundlessBlock (L.name ++ ": cleared") L.chain (some L.number) (L.hear.length + L.close.length + 3)
    L.clear

def FlatIs : Prop :=
  ∀ (S Cl : Type) (L : Link S Cl),
    L.blocksInOrder = L.laid :: L.hear ++ [L.batched, L.behind] ++ L.close ++ [L.cleared]

/-! ## 3 The fold's text -/

def StepsOfLeaves : Prop :=
  ∀ (S Cl α : Type) (h : S → α) (b : Block S Cl), b.Leaves h → b.Steps fun s s' => h s' = h s

def FoldSteps : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop), Pre R → ∀ (ft : Nat) (bs : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    (∀ b ∈ bs, b.Steps R) → foldBlocks ft bs s rs cols = .ok out → R s out.1

/-- The rounds behind those that the blocks pre declare. -/
def behindOf (pre : List (Block S Cl)) (rs : List Fmt.RoundView) : List Fmt.RoundView :=
  rs.drop (pre.flatMap (·.rounds)).length

def FoldAt : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop), Pre R → ∀ (ft : Nat) (pre rest : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    (∀ b ∈ pre, b.Steps R) → foldBlocks ft (pre ++ rest) s rs cols = .ok out →
    ∃ m cols', R s m ∧ foldBlocks ft pre s rs cols = .ok (m, behindOf pre rs, cols') ∧
      foldBlocks ft rest m (behindOf pre rs) cols' = .ok out

def FoldJoin : Prop :=
  ∀ (S Cl : Type) (ft : Nat) (pre rest : List (Block S Cl)) (s m : S) (rs rs' : List Fmt.RoundView)
    (cols cols' : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft pre s rs cols = .ok (m, rs', cols') → foldBlocks ft rest m rs' cols' = .ok out →
    foldBlocks ft (pre ++ rest) s rs cols = .ok out

/-- One run that the order names was called between the records s and e, and its claims are among
cls. -/
def RunCalled (R : S → S → Prop) (bs : List (Block S Cl)) (o : Nat × String) (s e : S)
    (cls : List Cl) : Prop :=
  ∃ b run n v cl v', bs[o.1]? = some b ∧ b.claims.lookup o.2 = some run ∧
    run n v = .ok (cl, v') ∧ R s v ∧ R v' e ∧ ∀ c ∈ cl, c ∈ cls

/-- **Where the link's claims go on, every run that the order names was called.** -/
def ClaimsTrace : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop), Pre R → ∀ (bs : List (Block S Cl))
    (order : List (Nat × String)) (s e : S) (cls : List Cl),
    (∀ b ∈ bs, b.RunsStep R) → claimsIn bs order s = .ok (cls, e) →
    R s e ∧ ∀ o ∈ order, RunCalled R bs o s e cls

def AfterSteps : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop), Pre R → ∀ (bs : List (Block S Cl))
    (order : List (Nat × String)) (s e : S),
    (∀ b ∈ bs, b.AfterStep R) → afterIn bs order s = .ok e → R s e

/-- What `LinkTrace` says of a link's fold from (s, rs, cols), at the records t t₁ u₀ z u e and the
claims cls. -/
structure Traced (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (L : Link S Cl) (h₁ : List (Block S Cl)) (b : Block S Cl) (ft : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (t t₁ u₀ z u e : S) (cls : List Cl) : Prop where
  /-- t is what the fold over the link's first block and the places in front of b gives -/
  front : ∃ c, foldBlocks ft (L.laid :: h₁) s rs cols = .ok (t, behindOf (L.laid :: h₁) rs, c)
  /-- b's decision, at its own stretch of the rounds -/
  decided : ∃ gs, b.decide t (shownAt h₁ b rs) gs = .ok t₁
  /-- t₁ too is a fold's value: over the first block, the places in front of b, and b -/
  behindB : ∃ c, foldBlocks ft (L.laid :: h₁ ++ [b]) s rs cols =
    .ok (t₁, behindOf (L.laid :: h₁ ++ [b]) rs, c)
  /-- u₀ is what the fold over the first block and all places in front of the batching gives -/
  heard : ∃ c, foldBlocks ft (L.laid :: L.hear) s rs cols =
    .ok (u₀, behindOf (L.laid :: L.hear) rs, c)
  toBatch : R t₁ u₀
  /-- the batching's decision, at its own stretch -/
  batched : ∃ gs, L.batched.decide u₀ (shownAt L.hear L.batched rs) gs = .ok z
  /-- z too is a fold's value -/
  behindBatch : ∃ c, foldBlocks ft (L.laid :: L.hear ++ [L.batched]) s rs cols =
    .ok (z, behindOf (L.laid :: L.hear ++ [L.batched]) rs, c)
  toCall : R u₀ u
  called : claimsInBy L.each L.hear L.order u = .ok (cls, e)
  along : R u e
  fromCall : R e z
  said : Q u₀ (shownAt L.hear L.batched rs) u cls e z
  /-- every run of b that the order names -/
  runs : ∀ name, (h₁.length, name) ∈ L.order →
    ∃ run n v cl v', b.claims.lookup name = some run ∧ run n v = .ok (cl, v') ∧ R t₁ v ∧
      R v' e ∧ ∀ c ∈ cl, c ∈ cls

/-- **The link.** -/
def LinkTrace : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop), Pre R →
    ∀ (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps R) → (∀ c ∈ L.hear, c.RunsStep R) → Calls R Q L.batch →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls, Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls

/-- The same, ASKING LESS OF THE BATCHING: `CallsAt`, of the block that stands in the flat list, at
the link's own claims. -/
def LinkTraceAt : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop), Pre R →
    ∀ (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps R) → (∀ c ∈ L.hear, c.RunsStep R) → CallsAt R Q L.batched
      (claimsInBy L.each L.hear L.order) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls, Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls

/-- The blocks of a link's flat list in front of the place of the closing behind c₁. -/
def Link.upTo (L : Link S Cl) (c₁ : List (Block S Cl)) : List (Block S Cl) :=
  L.laid :: L.hear ++ [L.batched, L.behind] ++ c₁

/-- **The link, on to a place of the closing.** -/
def LinkTraceClose : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop), Pre R →
    ∀ (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps R) → (∀ c ∈ L.hear, c.RunsStep R) → Calls R Q L.batch →
    (∀ c ∈ L.hear, c.AfterStep R) → (∀ c ∈ c₁, c.Steps R) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁, Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧ R z w ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        ∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁

/-- The same, ASKING LESS OF THE BATCHING: `CallsAt`, of the block that stands in the flat list, at
the link's own claims. -/
def LinkTraceCloseAt : Prop :=
  ∀ (S Cl : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop), Pre R →
    ∀ (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps R) → (∀ c ∈ L.hear, c.RunsStep R) → CallsAt R Q L.batched
      (claimsInBy L.each L.hear L.order) →
    (∀ c ∈ L.hear, c.AfterStep R) → (∀ c ∈ c₁, c.Steps R) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁, Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧ R z w ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁) ∧
        ∃ c, foldBlocks ft (L.upTo c₁ ++ [d]) s rs cols =
          .ok (w₁, behindOf (L.upTo c₁ ++ [d]) rs, c)

/-! ## 4 What was heard stands; the ledger only grows, with its sizes -/

section Ledger
variable {Φ Γ : Type}

/-- From s to s': what was heard at s is heard at s'; a ledger with its sizes at s is followed at s'
by a later one with its sizes. -/
def Carries (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop) (sized : Φ → Prop)
    (s s' : S) : Prop :=
  (∀ g, heard s = some g → heard s' = some g) ∧
    ∀ F, fork s = some F → sized F → ∃ F', fork s' = some F' ∧ later F F' ∧ sized F'

/-- **One run of claims said yes at a later record**: what was heard still stands there; its ledger
is a later one than F', with its sizes; the run leaves the ledger G. -/
structure RanAt (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (g : Γ) (F' : Φ) (run : Nat → S → Except String (List Cl × S)) (s : S)
    (cl : List Cl) (G : Φ) : Prop where
  heard : heard s = some g
  later : ∃ F, fork s = some F ∧ later F' F ∧ sized F
  ran : ∃ n s', run n s = .ok (cl, s') ∧ fork s' = some G

def CarriesPre : Prop :=
  ∀ (S Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop), (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    Pre (Carries fork heard later sized)

/-- What the two statements below conclude at a record x (behind the link's claims; or in front of
the settling): if b's decision left g as heard and a ledger F' with its sizes: g still stands at x;
x holds a ledger H with its sizes, later than F'; and every run of b that the order names `RanAt` …,
leaving a ledger G with `later G H`, its claims among cls. -/
def RanUpTo (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop) (sized : Φ → Prop)
    (L : Link S Cl) (h₁ : List (Block S Cl)) (b : Block S Cl) (t₁ x : S) (cls : List Cl) : Prop :=
  ∀ g F', heard t₁ = some g → fork t₁ = some F' → sized F' →
    heard x = some g ∧ ∃ H, fork x = some H ∧ later F' H ∧ sized H ∧
      ∀ name, (h₁.length, name) ∈ L.order →
        ∃ run v cl G, b.claims.lookup name = some run ∧
          RanAt fork heard later sized g F' run v cl G ∧ later G H ∧ ∀ c ∈ cl, c ∈ cls

/-- **Who pays "the run ran at a later record", and "later" to the ledger behind the link's
claims.** -/
def RanAtOfLink : Prop :=
  ∀ (S Cl Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop),
    (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    ∀ (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps (Carries fork heard later sized)) →
    (∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) →
    Calls (Carries fork heard later sized) Q L.batch →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls,
        Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        RanUpTo fork heard later sized L h₁ b t₁ e cls

/-- The same, ASKING LESS OF THE BATCHING: `CallsAt`, of the block that stands in the flat list, at
the link's own claims. -/
def RanAtOfLinkAt : Prop :=
  ∀ (S Cl Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop),
    (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    ∀ (L : Link S Cl) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
    (∀ c ∈ h₂, c.Steps (Carries fork heard later sized)) →
    (∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) →
    CallsAt (Carries fork heard later sized) Q L.batched (claimsInBy L.each L.hear L.order) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls,
        Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        RanUpTo fork heard later sized L h₁ b t₁ e cls

/-- **The like, on to the settling**: d: the place of the closing at which the link's claims are
settled: at the record w in front of d's decision. -/
def RanAtToSettling : Prop :=
  ∀ (S Cl Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop),
    (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    ∀ (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps (Carries fork heard later sized)) →
    (∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) →
    Calls (Carries fork heard later sized) Q L.batch →
    (∀ c ∈ L.hear, c.AfterStep (Carries fork heard later sized)) →
    (∀ c ∈ c₁, c.Steps (Carries fork heard later sized)) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁,
        Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁) ∧
        RanUpTo fork heard later sized L h₁ b t₁ w cls

/-- The same, ASKING LESS OF THE BATCHING: `CallsAt`, of the block that stands in the flat list, at
the link's own claims. -/
def RanAtToSettlingAt : Prop :=
  ∀ (S Cl Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop),
    (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    ∀ (L : Link S Cl) (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl),
    L.hear = h₁ ++ b :: h₂ → L.close = c₁ ++ d :: c₂ →
    (∀ c ∈ h₂, c.Steps (Carries fork heard later sized)) →
    (∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) →
    CallsAt (Carries fork heard later sized) Q L.batched (claimsInBy L.each L.hear L.order) →
    (∀ c ∈ L.hear, c.AfterStep (Carries fork heard later sized)) →
    (∀ c ∈ c₁, c.Steps (Carries fork heard later sized)) →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft L.blocksInOrder s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls w w₁,
        Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
        (∃ c, foldBlocks ft (L.upTo c₁) s rs cols = .ok (w, behindOf (L.upTo c₁) rs, c)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d rs) gs = .ok w₁) ∧
        (∃ c, foldBlocks ft (L.upTo c₁ ++ [d]) s rs cols =
          .ok (w₁, behindOf (L.upTo c₁ ++ [d]) rs, c)) ∧
        RanUpTo fork heard later sized L h₁ b t₁ w cls

end Ledger

end VerifiableInference.Desc
