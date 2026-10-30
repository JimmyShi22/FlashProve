-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookFace.lean: the entries of the book of coins for one lookup of a key file, computed from
the lookup's public numbers. They say which mask entries the lookup's rounds use, and of which
earlier oracle message. The book (`ProverCoinCounts`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is
the public table of how many coins each part of an honest prover has. An entry of the book (`Ahead`;
below: a book entry) names a range of the coins of one part, the owner (`Ahead.owner`), that one
other part, the spender (`Ahead.spender`), is given too. A face (`K3.Face`,
Johnson/Desc/First/Look/K3LookupGeneral.lean) holds a lookup's public numbers; a place (`Place`) says
where in a protocol description a sub-protocol is. All definitions and theorems are general in the
face. They are about public data only: no prover, no value of a coin, no witness. The file has
executable definitions, five theorems with the small lemmas that carry them, and tests at a small
example face. The lines that begin with `#guard` are the tests: Lean's evaluator runs them when the
file is compiled, the kernel does not check them, and they prove nothing.

Why. In a key file a lookup's rounds use as many mask entries as they send scalars: for each masked
sumcheck the coefficients of its hiding polynomial, then one mask for each of its end values. The
library numbers them in the order of sending and calls them the lookup's hidden values. The mask
entries belong to two oracle messages that were sent before the lookup, so a lookup's prover is
meant to sample no coin of its own. The two end values of the last level of the key tree of each
part of the keys use entries of the index-mask message (below: the second message). All other hidden
values use entries of the message with the multiplicities (below: the first message). `caller`
(Johnson/Desc/Key/Link.lean) is the verifier's side of this. The frame gives a part a range of
another part's coins only if the book has an entry for it, with a name, the owner, the first coin,
the count and the spender. This file computes these entries from the face.

Two things are called parts: a part of the keys (an element of `Face.parts`) and a part of the
prover (`Part`, in the frame). Below, "part" by itself is a part of the prover.

  `entries_spans`: at every face f the rounds of the spans of `spansOf f` (`Span.entries`),
    concatenated, are `K3.entriesV f` (Johnson/Desc/First/Look/Via/Rounds.lean). That is the list of
    rounds of one of the library's definitions of how the verifier reads a lookup's rounds
    (`messagesV`, same file). It is not the definition that the key file's link calls: see the
    limits
  `homes_spans`: at every face f the flags of these spans (`Span.homes`), concatenated, are
    `K3.fromKeys f` (Johnson/Desc/First/Look/K3Key.lean): the library's public table by which the
    key file's verifier assigns each hidden value its mask entry (`homes`, same file; called by
    `caller`)
  `unroll_lay`: for every list of spans, the coins that the entries of `layFrom` name, one by one in
    the entries' order (`unroll`), are what two counters give along the spans' flags (`deal`). So
    coin number j of that list is the next unused coin of the owner that flag number j names.
    Hypothesis: the two owners have different addresses
  `unroll_book`: `unroll_lay` and `homes_spans` together: the coins of `bookEntries S f a b` are
    `deal (fromKeys f) a b`. The same hypothesis
  `scalars_span`: a span uses as many mask entries (`Span.run` plus `Span.ends`) as its own rounds
    send scalars (`scalarsAt`)
  `Span`: a definition: a range of a lookup's rounds that is one part in the list of parts at the
    lookup's place. It is either one round in which nothing is sent and challenges are sampled
    (`draw`), or one masked sumcheck (`sum`), given by its call (`MaskedSum.Call`,
    Johnson/Desc/Part/MaskedSum4.lean) and the flag "the mask entries of its end values are in the
    second message"
  `spansOf f`: a definition: the lookup's spans in the order of the rounds: `frontOf f`, then
    `keysOf f`, then `backOf f`
  `frontOf`, `keysOf`, `backOf`, `levels`, `levelCall`: definitions: the spans before the key trees;
    those of the key trees, one tree for each part of the keys; those after the key trees; the spans
    of several levels of a product tree; the call of one level's masked sumcheck
  `Span.entries`, `Span.rounds`, `Span.run`, `Span.ends`, `Span.homes`: definitions: a span's rounds
    as entries of the plan (`Fmt.Entry`), with the proof-of-work bits left 0; their number; the
    number of mask entries in its first range (its lead scalars' and the coefficients of its hiding
    polynomial; no call in `spansOf` has a lead scalar); the number in its second range (one for
    each end value); and for each of its hidden values, in the order of sending, the flag "its mask
    entry is in the second message"
  `Seat`: a structure: the lookup's place, and the two owners, each with its address and its name
  `layFrom`, `bookEntries`: definitions: the book entries of a list of spans; those of a lookup,
    which are `layFrom` at `spansOf f`, from part number 0
  `deal`, `unroll`: definitions: two counters that go along a list of flags; the coins that a list
    of book entries names, one by one
  `scalarsAt`: a definition: the number of scalars in the message of a round that is given by its
    entry of the plan
  `flatMap_same`, `entries_levels`: lemmas for `entries_spans`
  `foldl_add_sum`, `ownSlots_eq`, `run_level`, `run_bits`, `sum_two_below`, `sum_leaf`,
    `run_leaves`: lemmas: the first range's count (`ownRun`) at a level's call, the bits' call and
    the leaves' call
  `homes_draw`, `homes_level`, `homes_leaves`, `homes_bits`, `flatMap_replicate`, `flatMap_many`,
    `homes_levels_own`, `homes_levels_keys`, `homes_front`, `homes_back`: lemmas for `homes_spans`:
    the flags of each kind of span and of each of the three lists
  `scalars_entry`, `scalars_vars`: lemmas for `scalars_span`
  `deal_false`, `deal_true`, `unroll_append`, `unroll_one`: lemmas for `unroll_lay`
  `toyFace`, `toySeat`: definitions: the small example face and a `Seat` for the tests

By what. No theorem of another file of the library is called: the proofs unfold definitions and use
the lemmas listed above and general lemmas on lists. The definitions of other files: `entriesV`,
`noVar`, `leafVars`, `bitsCall`, `drawEntry` (Johnson/Desc/First/Look/Via/Rounds.lean);
`ProdV.runEntries`, `ProdV.levelEntries`, `ProdV.levelEnds` (Johnson/Desc/First/ProdV/Level.lean);
`fromKeys`, `own` (Johnson/Desc/First/Look/K3Key.lean); `MaskedSum.entries`, `MaskedSum.entry`,
`MaskedSum.ownSlots`, `MaskedSum.Call.all` (Johnson/Desc/Part/MaskedSum4.lean); `ownRun`
(Johnson/Desc/ProofFile/Honest/Sum.lean); `scalarsIn`, `cutOfNames`
(Johnson/Desc/ProofFile/Honest/BookOf.lean); `runName`, by which `layFrom` names its entries
(Johnson/Desc/ProofFile/Honest/ForKinds.lean).

Limits.
- The theorems hold at every face, also at one that fails `Face.ok` (no part of the keys, one plane,
  mu = 0). There they say no more than the library's two lists `entriesV f` and `fromKeys f` say. At
  a face without a part of the keys no entry is built for the second message.
- The key file's link (`lookupLink`, Johnson/Desc/Key/Link.lean) calls another definition of the
  lookup, `K3.lookupKind` (Johnson/Desc/First/Look/K3LookupGeneral.lean), whose rounds the planner computes
  (`PG.entries`). That these are `K3.entriesV f`, apart from the proof-of-work bits, is a test
  (`entriesFit`, Johnson/Desc/First/Look/Via/Rounds.lean). `blockV` (same file), the block that
  reads by `messagesV`, asks that test; `lookupKind` does not. At the full size (`keyFull`),
  E2E/KeyBookAtWritten.lean compares `entriesV` at the two lookups' faces with the library's written
  rounds, apart from the proof-of-work bits, by evaluation. `K3.fromKeys`, in contrast, is the very
  table that the link reads, through `caller`.
- That the cut of the rounds into parts by the rounds' names (`cutOfNames`) is
  `(spansOf f).map Span.rounds` is only tested here, at the small face. It is proved, at faces with
  at least two planes, in E2E/KeyBookHeldK3.lean (`cut_spans`).
- `spansOf` lists a second time what the list of honest parts lists for itself (`stages`,
  Johnson/Desc/ProofFile/Honest/K3/Stages.lean), and some small lemmas here have counterparts in
  Johnson/Desc/ProofFile/Honest/K3/RowLaw.lean. This is on purpose: a book is a check only if it is
  computed separately from the definitions of the prover's parts, so `layFrom` does not call their
  list. It shares one count with them, `ownRun`. The two lists are shown to agree item by item, at
  faces with at least two planes, in E2E/KeyBookHeldK3.lean (`spans_of_stages`).
- `unroll` reads an entry's owner, first coin and count, the last two in the extension field. It
  does not read the entry's name, its spender or whether it is marked as spent: for these see
  E2E/KeyBookRow.lean.
- `deal` counts from two given numbers. Two things are not stated here: that the verifier's ledgers
  of the two messages (`takeMasksP`, called by `caller`) give out just these numbers (consecutive
  free mask entries, with the pad's entries skipped), and which coin of an owner a free mask entry
  is. Both are left to whoever calls `bookEntries`, who supplies the two first coins.
- A book entry says who may be given a range of coins. Nothing here says that a prover reads the
  range, or how.
- No honest prover is defined.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.First.Look.K3Key
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open OnBytes (zeroE)
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K3 (Face fromKeys entriesV noVar leafVars bitsCall drawEntry)
open ProofFile.Honest (Addr Ahead Due runName ownRun cutOfNames scalarsIn)

/-! ## 1 The spans of a lookup -/

/-- A range of a lookup's rounds that is one part of the prover. -/
inductive Span where
  /-- one round: nothing is sent; n elements are sampled -/
  | draw (name : String) (n : Nat)
  /-- one masked sumcheck. second: the mask entries of its end values are in the second message -/
  | sum (k : MaskedSum.Call) (second : Bool)

/-- The call of the masked sumcheck of a product tree's level with m variables, as in
`ProdV.levelEntries` (Johnson/Desc/First/ProdV/Level.lean). -/
def levelCall (m : Nat) : MaskedSum.Call :=
  { lead := 0, vs := List.replicate m (.point zeroE 3), ends := some ProdV.levelEnds }

/-- The spans of n consecutive levels, with m0, m0 + 1, … variables: for each level a masked
sumcheck and the round "LINE". keys: the levels are the key tree of a part of the keys; then the
mask entries of the last level's end values are in the second message. -/
def levels (m0 n : Nat) (keys : Bool) : List Span :=
  (List.range n).flatMap fun i => [.sum (levelCall (m0 + i)) (keys && i + 1 == n), .draw "LINE" 1]

/-- The spans before the key trees. The round that samples the shift, if the face has one. The round
that samples the point alpha. The masked sumchecks that tie the two sides' roots: one at
`noVar 3 3`, then `planes - 2` at `noVar 3 2`. The `parts.length - 1` masked sumchecks at
`noVar 2 2` that lead from the product of the roots of the parts of the keys to each root. The round
"JOIN", which samples the planes' point. -/
def frontOf (f : Face) : List Span :=
  (if f.shifted then [.draw "LKP shift" 1] else []) ++ [.draw "LKP" 1] ++
    [.sum (noVar 3 3) false] ++
    List.replicate (f.planes - 2) (.sum (noVar 3 2) false) ++
    List.replicate (f.parts.length - 1) (.sum (noVar 2 2) false) ++
    [.draw "JOIN" f.mu]

/-- The spans of the key trees: for each part of the keys, of 2 ^ v keys, a tree of v levels. -/
def keysOf (f : Face) : List Span := f.parts.flatMap fun v => levels 0 v true

/-- The spans after the key trees. The d levels of the table side's trees, taken as one tree, from
mu variables up. The masked sumcheck on its leaves, which has no end value. The round "ZERO", which
samples the bits' point. The masked sumcheck that the bits are bits. -/
def backOf (f : Face) : List Span :=
  levels f.mu f.d false ++
    [.sum { lead := 0, vs := leafVars f #[], ends := none } false, .draw "ZERO" (f.mu + f.d),
      .sum (bitsCall (List.replicate (f.mu + f.d) zeroE)) false]

/-- The lookup's spans, in the order of the rounds. -/
def spansOf (f : Face) : List Span := frontOf f ++ keysOf f ++ backOf f

/-- A span's rounds as entries of the plan, with the proof-of-work bits left 0. -/
def Span.entries : Span → List Fmt.Entry
  | .draw s n => [drawEntry s n]
  | .sum k _ => MaskedSum.entries k

/-- The number of a span's rounds. -/
def Span.rounds (p : Span) : Nat := p.entries.length

/-- The number of mask entries in a span's first range: its lead scalars' and the coefficients of
its hiding polynomial (`ownRun`, Johnson/Desc/ProofFile/Honest/Sum.lean). -/
def Span.run : Span → Nat
  | .draw _ _ => 0
  | .sum k _ => ownRun k

/-- The number in its second range: one for each end value. -/
def Span.ends : Span → Nat
  | .draw _ _ => 0
  | .sum k _ => (k.ends.map (·.n)).getD 0

/-- For each hidden value of a span, in the order of sending: whether its mask entry is in the
second message. -/
def Span.homes : Span → List Bool
  | .draw _ _ => []
  | .sum k s => List.replicate (ownRun k) false ++ List.replicate ((k.ends.map (·.n)).getD 0) s

/-! ## 2 The book entries -/

/-- A lookup's place, and the two owners: the parts whose coins the lookup's parts are given. -/
structure Seat where
  /-- the lookup's place -/
  place : Place
  /-- the first message: its name as an owner, and the address of the part that sends it -/
  ownName : String
  own : Addr
  /-- the second message: the same two -/
  keyName : String
  key : Addr

/-- The book entries of a list of spans. part: the number, in the list of parts at the place, of the
list's first span. a, b: the numbers of the next unused coins of the extension field, of the first
and of the second owner. A masked sumcheck gets one entry for its first range (use "sum") and, if
its call has ends, one for its second range (use "ends"), in this order; a round that sends nothing
gets none. The spender of a span's entries is the part with the span's number at the place. All
entries are marked as spent. -/
def layFrom (S : Seat) : List Span → Nat → Nat → Nat → List Ahead
  | [], _, _, _ => []
  | .draw _ _ :: l, part, a, b => layFrom S l (part + 1) a b
  | .sum k second :: l, part, a, b =>
    let dest : Addr := ⟨S.place, part⟩
    let n := (k.ends.map (·.n)).getD 0
    [⟨runName S.ownName dest "sum", S.own, ⟨0, a⟩, ⟨0, ownRun k⟩, dest, true⟩] ++
      (if k.ends.isNone then []
       else if second then [⟨runName S.keyName dest "ends", S.key, ⟨0, b⟩, ⟨0, n⟩, dest, true⟩]
       else [⟨runName S.ownName dest "ends", S.own, ⟨0, a + ownRun k⟩, ⟨0, n⟩, dest, true⟩]) ++
      layFrom S l (part + 1) (a + ownRun k + if second then 0 else n) (b + if second then n else 0)

/-- A lookup's book entries. a, b: the first coins that it takes of the two owners. -/
def bookEntries (S : Seat) (f : Face) (a b : Nat) : List Ahead := layFrom S (spansOf f) 0 a b

/-- Two counters that go along a list of flags: each flag is paired with the number that its counter
shows (`false`: the first counter; `true`: the second), and that counter then goes up by one. -/
def deal : List Bool → Nat → Nat → List (Bool × Nat)
  | [], _, _ => []
  | false :: l, a, b => (false, a) :: deal l (a + 1) b
  | true :: l, a, b => (true, b) :: deal l a (b + 1)

/-- The coins of the extension field that a list of book entries names, one by one, in the entries'
order. For each coin: whether its owner is the second owner, and its number among the owner's coins.
-/
def unroll (S : Seat) (es : List Ahead) : List (Bool × Nat) :=
  es.flatMap fun e => (List.range e.count.e).map fun i => (e.owner == S.key, e.start.e + i)

/-! ## 3 The spans' rounds are the library's list -/

theorem flatMap_same {α β : Type} (g : α → List β) (x : α) (n : Nat) :
    (List.replicate n x).flatMap g = (List.range n).flatMap fun _ => g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]

theorem entries_levels (m0 n : Nat) (b : Bool) :
    (levels m0 n b).flatMap Span.entries = ProdV.runEntries m0 n := by
  simp [levels, ProdV.runEntries, ProdV.levelEntries, List.flatMap_assoc, Span.entries, levelCall,
    drawEntry]

/-- **The spans' rounds, concatenated, are `entriesV f`**: the list of rounds that goes with
`messagesV f`, one of the library's definitions of how the verifier reads a lookup's rounds. -/
theorem entries_spans (f : Face) : (spansOf f).flatMap Span.entries = entriesV f := by
  unfold spansOf frontOf keysOf backOf entriesV
  simp only [List.flatMap_append, List.flatMap_assoc, entries_levels, flatMap_same,
    List.flatMap_cons, List.flatMap_nil, Span.entries, List.append_nil, List.append_assoc]
  cases f.shifted <;> simp [Span.entries]

/-! ## 4 The spans' flags are the library's table -/

theorem foldl_add_sum {α : Type} (g : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun n v => n + g v) a = a + (l.map g).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, Nat.add_assoc]

theorem ownSlots_eq (vs : List MaskedSum.Var) :
    MaskedSum.ownSlots vs = 1 + (vs.map fun v => v.d - 1).sum := foldl_add_sum _ vs 1

theorem run_level (m : Nat) : ownRun (levelCall m) = 2 * m + 3 := by
  simp [ownRun, levelCall, MaskedSum.Call.all, ProdV.levelEnds, ownSlots_eq, MaskedSum.Var.d]
  omega

theorem run_bits (n : Nat) : ownRun (bitsCall (List.replicate n zeroE)) = 2 * n + 3 := by
  simp [ownRun, bitsCall, MaskedSum.Call.all, ownSlots_eq, MaskedSum.Var.d]
  omega

theorem sum_two_below (d n : Nat) (h : n ≤ d) :
    ((List.range n).map fun j => (if j < d then 3 else 2) - 1).sum = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n < d := h
    simp [List.range_succ, ih (Nat.le_of_succ_le h), hn]
    omega

theorem sum_leaf (d m : Nat) :
    ((List.range (m + d)).map fun j => (if j < d then 3 else 2) - 1).sum = m + 2 * d := by
  induction m with
  | zero => simpa using sum_two_below d d (Nat.le_refl d)
  | succ m ih =>
    have e : m + 1 + d = (m + d) + 1 := by omega
    have hn : ¬ (m + d < d) := by omega
    rw [e, List.range_succ]
    simp [ih, hn]
    omega

theorem run_leaves (f : Face) :
    ownRun { lead := 0, vs := leafVars f #[], ends := none } = 1 + f.mu + 2 * f.d := by
  have h := sum_leaf f.d f.mu
  simp only [ownRun, MaskedSum.Call.all, ownSlots_eq, leafVars, List.map_map]
  have e : ((fun v : MaskedSum.Var => v.d - 1) ∘ fun j =>
      MaskedSum.Var.point ((#[] : Array OnBytes.E).getD j zeroE) (if j < f.d then 3 else 2)) =
      fun j => (if j < f.d then 3 else 2) - 1 := by
    funext j; rfl
  rw [e, h]
  omega

theorem homes_draw (s : String) (n : Nat) : Span.homes (.draw s n) = [] := rfl

theorem homes_level (m : Nat) (s : Bool) :
    Span.homes (.sum (levelCall m) s) = List.replicate (2 * m + 3) false ++ [s, s] := by
  show List.replicate (ownRun (levelCall m)) false ++ List.replicate 2 s = _
  rw [run_level]
  rfl

theorem homes_leaves (f : Face) :
    Span.homes (.sum { lead := 0, vs := leafVars f #[], ends := none } false) =
      List.replicate (1 + f.mu + 2 * f.d) false := by
  show List.replicate (ownRun _) false ++ List.replicate 0 false = _
  rw [run_leaves]
  simp

theorem homes_bits (n : Nat) :
    Span.homes (.sum (bitsCall (List.replicate n zeroE)) false) =
      List.replicate (1 + 2 * n + 2 + 1) false := by
  show List.replicate (ownRun _) false ++ List.replicate 1 false = _
  rw [run_bits, List.replicate_append_replicate]
  congr 1
  omega

theorem flatMap_replicate {α β : Type} (g : α → Nat) (x : β) (l : List α) :
    (l.flatMap fun a => List.replicate (g a) x) = List.replicate (l.map g).sum x := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, List.replicate_append_replicate]

theorem flatMap_many {α β : Type} (g : α → List β) (p : α) (c : Nat) (x : β)
    (h : g p = List.replicate c x) (n : Nat) :
    (List.replicate n p).flatMap g = List.replicate (c * n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, h, List.replicate_append_replicate]
    congr 1
    rw [Nat.mul_succ, Nat.add_comm]

theorem homes_levels_own (m0 n : Nat) :
    (levels m0 n false).flatMap Span.homes =
      List.replicate ((List.range n).map fun l => 2 * (m0 + l) + 5).sum false := by
  rw [← flatMap_replicate]
  simp only [levels, List.flatMap_assoc]
  congr 1
  funext i
  simp only [List.flatMap_cons, List.flatMap_nil, homes_level, homes_draw, Bool.false_and,
    List.append_nil]
  show List.replicate (2 * (m0 + i) + 3) false ++ List.replicate 2 false = _
  rw [List.replicate_append_replicate]

theorem homes_levels_keys (v : Nat) :
    (levels 0 v true).flatMap Span.homes =
      (List.range v).flatMap fun k =>
        if k + 1 == v then VerifiableInference.Desc.K3.own (2 * k + 3) ++ [true, true]
        else VerifiableInference.Desc.K3.own (2 * k + 5) := by
  simp only [levels, List.flatMap_assoc]
  congr 1
  funext k
  simp only [List.flatMap_cons, List.flatMap_nil, homes_level, homes_draw, Bool.true_and,
    List.append_nil, Nat.zero_add, VerifiableInference.Desc.K3.own]
  cases k + 1 == v with
  | true => rfl
  | false =>
    show List.replicate (2 * k + 3) false ++ List.replicate 2 false =
      List.replicate (2 * k + 5) false
    rw [List.replicate_append_replicate]

theorem homes_front (f : Face) :
    (frontOf f).flatMap Span.homes =
      VerifiableInference.Desc.K3.own (7 + 6 * (f.planes - 2) + 5 * (f.parts.length - 1)) := by
  have h33 : Span.homes (.sum (noVar 3 3) false) = List.replicate 7 false := rfl
  have h32 : Span.homes (.sum (noVar 3 2) false) = List.replicate 6 false := rfl
  have h22 : Span.homes (.sum (noVar 2 2) false) = List.replicate 5 false := rfl
  have hs : (if f.shifted then [Span.draw "LKP shift" 1] else []).flatMap Span.homes = [] := by
    cases f.shifted <;> rfl
  unfold frontOf VerifiableInference.Desc.K3.own
  simp only [List.flatMap_append, hs, flatMap_many _ _ _ _ h32, flatMap_many _ _ _ _ h22,
    List.flatMap_cons, List.flatMap_nil, h33, homes_draw, List.append_nil, List.nil_append,
    List.replicate_append_replicate]

theorem homes_back (f : Face) :
    (backOf f).flatMap Span.homes =
      VerifiableInference.Desc.K3.own (((List.range f.d).map fun l => 2 * (f.mu + l) + 5).sum +
        (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1)) := by
  have hz : Span.homes (.draw "ZERO" (f.mu + f.d)) = [] := rfl
  unfold backOf VerifiableInference.Desc.K3.own
  simp only [List.flatMap_append, homes_levels_own, List.flatMap_cons, List.flatMap_nil,
    homes_leaves, homes_bits, hz, List.append_nil, List.nil_append,
    List.replicate_append_replicate, Nat.add_assoc]

/-- **The spans' flags, concatenated, are `fromKeys f`**: the library's public table that says of
each hidden value whether its mask entry is in the second message. -/
theorem homes_spans (f : Face) : (spansOf f).flatMap Span.homes = fromKeys f := by
  unfold spansOf fromKeys keysOf
  simp only [List.flatMap_append, homes_front, homes_back, List.flatMap_assoc, homes_levels_keys]

/-- The number of scalars in a round's message: the frame's own count (`scalarsIn`,
Johnson/Desc/ProofFile/Honest/BookOf.lean), at the round that is given by its entry of the plan. -/
def scalarsAt (e : Fmt.Entry) : Nat := scalarsIn { entry := e }

theorem scalars_entry (name : String) (sent drawn never0 : Nat) :
    scalarsAt (MaskedSum.entry name sent drawn never0) = sent := by
  simp [scalarsAt, scalarsIn, MaskedSum.entry]

theorem scalars_vars (l : List MaskedSum.Var) :
    ((l.map fun v => MaskedSum.entry "PSC round" (v.d - 1) 1 0).map scalarsAt).sum =
      (l.map fun v => v.d - 1).sum := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.map_cons, List.sum_cons, ih, scalars_entry]

/-- **A span uses as many mask entries as its own rounds send scalars.** -/
theorem scalars_span (s : Span) : (s.entries.map scalarsAt).sum = s.run + s.ends := by
  cases s with
  | draw n m =>
    show (([drawEntry n m] : List Fmt.Entry).map scalarsAt).sum = 0 + 0
    simp only [drawEntry, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, scalars_entry]
  | sum k second =>
    show ((MaskedSum.entries k).map scalarsAt).sum = ownRun k + (k.ends.map (·.n)).getD 0
    unfold MaskedSum.entries ownRun MaskedSum.Call.all
    rw [ownSlots_eq]
    cases k.ends with
    | none =>
      simp only [List.map_append, List.sum_append, scalars_vars, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, scalars_entry, Option.map_none, Option.getD_none,
        List.append_nil]
      omega
    | some e =>
      have hd : (MaskedSum.Var.point zeroE (e.dY + 1)).d = e.dY + 1 := rfl
      simp only [List.map_append, List.sum_append, scalars_vars, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, scalars_entry, Option.map_some, Option.getD_some, hd]
      omega

/-! ## 5 The entries' coins, one by one -/

theorem deal_false (n : Nat) (l : List Bool) (a b : Nat) :
    deal (List.replicate n false ++ l) a b =
      ((List.range n).map fun i => (false, a + i)) ++ deal l (a + n) b := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, deal, ih, List.range_succ_eq_map]
    simp [Nat.add_assoc, Nat.add_comm 1, Function.comp_def]

theorem deal_true (n : Nat) (l : List Bool) (a b : Nat) :
    deal (List.replicate n true ++ l) a b =
      ((List.range n).map fun i => (true, b + i)) ++ deal l a (b + n) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, deal, ih, List.range_succ_eq_map]
    simp [Nat.add_assoc, Nat.add_comm 1, Function.comp_def]

theorem unroll_append (S : Seat) (l₁ l₂ : List Ahead) :
    unroll S (l₁ ++ l₂) = unroll S l₁ ++ unroll S l₂ := List.flatMap_append

theorem unroll_one (S : Seat) (e : Ahead) :
    unroll S [e] = (List.range e.count.e).map fun i => (e.owner == S.key, e.start.e + i) := by
  simp [unroll]

/-- **The entries' coins, one by one, are what the two counters give along the spans' flags.**
Hypothesis h: the two owners have different addresses. -/
theorem unroll_lay (S : Seat) (h : S.own ≠ S.key) (ps : List Span) (part a b : Nat) :
    unroll S (layFrom S ps part a b) = deal (ps.flatMap Span.homes) a b := by
  have h0 : (S.own == S.key) = false := beq_eq_false_iff_ne.2 h
  induction ps generalizing part a b with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | draw s n => simpa [layFrom, Span.homes] using ih (part + 1) a b
    | sum k second =>
      simp only [layFrom, unroll_append, unroll_one, ih, List.flatMap_cons, Span.homes,
        List.append_assoc, deal_false, h0]
      congr 1
      cases k.ends with
      | none => simp [unroll]
      | some e =>
        cases second with
        | false => simp [unroll_one, h0, deal_false, Nat.add_assoc]
        | true => simp [unroll_one, deal_true]

/-- The same for a lookup's book entries and the library's table `fromKeys f`. -/
theorem unroll_book (S : Seat) (h : S.own ≠ S.key) (f : Face) (a b : Nat) :
    unroll S (bookEntries S f a b) = deal (fromKeys f) a b := by
  rw [← homes_spans]
  exact unroll_lay S h (spansOf f) 0 a b

/-! ## 6 Tests at a small example face -/

/-- A small face: a count has 4 places for bits, 3 of them real; two parts of the keys, of 2 and of
4 keys; a table of 2 rows; no shift, no padding. -/
def toyFace : Face :=
  { shifted := false, mu := 2, planes := 3, parts := [1, 2], d := 1
    orders := fun _ m => OnBytes.Model.orderDefault m, padding := [], leaf := fun _ _ _ => zeroE }

/-- A `Seat` for the tests. -/
def toySeat : Seat :=
  { place := ⟨1, some 0, 2, .K3⟩
    ownName := "the first", own := ⟨⟨1, none, 2, .K1⟩, 0⟩
    keyName := "the second", key := ⟨⟨1, none, 1, .K1⟩, 0⟩ }

#guard toyFace.ok
-- 16 spans; 59 hidden values, 4 of them with a mask entry in the second message
#guard (spansOf toyFace).length == 16
#guard ((spansOf toyFace).map fun p => p.run + p.ends).sum == toyFace.slots
#guard toyFace.slots == 59
#guard (fromKeys toyFace).count true == 2 * toyFace.parts.length
-- the cut of the rounds into parts by the rounds' names gives the spans' numbers of rounds
#guard cutOfNames .K3 ((entriesV toyFace).map (·.name)) == (spansOf toyFace).map Span.rounds
#guard (spansOf toyFace).map Span.rounds ==
  [1, 3, 3, 3, 1, 3, 1, 3, 1, 4, 1, 5, 1, 4, 1, 6]
-- two entries for a sumcheck with ends, one for the leaves'; names differ; the last coins taken
#guard (bookEntries toySeat toyFace 10 100).length == 2 * 8 + 1
#guard ((bookEntries toySeat toyFace 10 100).map (·.name)).eraseDups.length == 17
#guard (unroll toySeat (bookEntries toySeat toyFace 10 100)).getLast? ==
  some (false, 10 + 59 - 4 - 1)
#guard ((unroll toySeat (bookEntries toySeat toyFace 10 100)).filter (·.1)).map (·.2) ==
  [100, 101, 102, 103]
-- the parts that are given the second owner's coins: the last level of each key tree
#guard ((bookEntries toySeat toyFace 10 100).filter (·.owner == toySeat.key)).map
  (·.spender.part) == [5, 9]
#guard ((bookEntries toySeat toyFace 10 100).head?.map (·.name)) == some "the first to 1.0.2.1: sum"
-- the comparisons can fail: with the parts of the keys in another order the flags differ; with
-- one more plane the rounds differ
#guard (spansOf toyFace).flatMap Span.homes != fromKeys { toyFace with parts := [2, 1] }
#guard (spansOf toyFace).flatMap Span.entries != entriesV { toyFace with planes := 4 }
-- with a shift and one part of the keys: one more span at the start, a round that sends nothing
#guard (spansOf { toyFace with shifted := true, parts := [2] }).map Span.rounds ==
  [1, 1, 3, 3, 1, 3, 1, 4, 1, 5, 1, 4, 1, 6]

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.entries_spans
#print axioms AtPublicFiles.KeyBook.homes_spans
#print axioms AtPublicFiles.KeyBook.scalars_span
#print axioms AtPublicFiles.KeyBook.unroll_lay
#print axioms AtPublicFiles.KeyBook.unroll_book
#print axioms AtPublicFiles.KeyBook.Span
#print axioms AtPublicFiles.KeyBook.levelCall
#print axioms AtPublicFiles.KeyBook.levels
#print axioms AtPublicFiles.KeyBook.frontOf
#print axioms AtPublicFiles.KeyBook.keysOf
#print axioms AtPublicFiles.KeyBook.backOf
#print axioms AtPublicFiles.KeyBook.spansOf
#print axioms AtPublicFiles.KeyBook.Span.entries
#print axioms AtPublicFiles.KeyBook.Span.rounds
#print axioms AtPublicFiles.KeyBook.Span.run
#print axioms AtPublicFiles.KeyBook.Span.ends
#print axioms AtPublicFiles.KeyBook.Span.homes
#print axioms AtPublicFiles.KeyBook.Seat
#print axioms AtPublicFiles.KeyBook.layFrom
#print axioms AtPublicFiles.KeyBook.bookEntries
#print axioms AtPublicFiles.KeyBook.deal
#print axioms AtPublicFiles.KeyBook.unroll
#print axioms AtPublicFiles.KeyBook.flatMap_same
#print axioms AtPublicFiles.KeyBook.entries_levels
#print axioms AtPublicFiles.KeyBook.foldl_add_sum
#print axioms AtPublicFiles.KeyBook.ownSlots_eq
#print axioms AtPublicFiles.KeyBook.run_level
#print axioms AtPublicFiles.KeyBook.run_bits
#print axioms AtPublicFiles.KeyBook.sum_two_below
#print axioms AtPublicFiles.KeyBook.sum_leaf
#print axioms AtPublicFiles.KeyBook.run_leaves
#print axioms AtPublicFiles.KeyBook.homes_draw
#print axioms AtPublicFiles.KeyBook.homes_level
#print axioms AtPublicFiles.KeyBook.homes_leaves
#print axioms AtPublicFiles.KeyBook.homes_bits
#print axioms AtPublicFiles.KeyBook.flatMap_replicate
#print axioms AtPublicFiles.KeyBook.flatMap_many
#print axioms AtPublicFiles.KeyBook.homes_levels_own
#print axioms AtPublicFiles.KeyBook.homes_levels_keys
#print axioms AtPublicFiles.KeyBook.homes_front
#print axioms AtPublicFiles.KeyBook.homes_back
#print axioms AtPublicFiles.KeyBook.scalarsAt
#print axioms AtPublicFiles.KeyBook.scalars_entry
#print axioms AtPublicFiles.KeyBook.scalars_vars
#print axioms AtPublicFiles.KeyBook.deal_false
#print axioms AtPublicFiles.KeyBook.deal_true
#print axioms AtPublicFiles.KeyBook.unroll_append
#print axioms AtPublicFiles.KeyBook.unroll_one
#print axioms AtPublicFiles.KeyBook.toyFace
#print axioms AtPublicFiles.KeyBook.toySeat
