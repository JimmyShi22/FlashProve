-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/FiveFieldsAt.lean: THE FIVE OF Johnson/Bind/ForProver/FiveAt.lean AND
FiveAtIndex.lean LAID INTO THE STRUCTURE `ProofFile.Honest.K14.FiveFields`
(Johnson/Desc/ProofFile/Honest/K14/FiveFields.lean), WHICH STATES WHAT THE LAWS ON THE HONEST SIDE
OF THE LINEAR CLAIM'S SHARED ROUNDS (THE SHARED CHAIN) TAKE FROM "THE INPUT IS VALID" ON THE
COMMITTED TABLE AND THE KEY; AND A LAW THAT CARRIES THAT STRUCTURE TO A NARROWER PREDICATE.
Statements and proofs; no definition.

Why. FiveAt.lean and FiveAtIndex.lean prove the five (cols, tab, key, seeds, ans) as sentences
written out, in a form that was read off the text of the structure `ProofFile.Honest.K14.K14Asks`
(Johnson/Desc/ProofFile/Honest/K14/Asks.lean): there a reader compares the two forms, not Lean.
`FiveFields` states these five fields of `K14Asks` on parameters (which inputs are valid, the stored
table, the reader of the index, the reader of the coins): cols, key and seeds in its words; tab and
ans with `rowsK` for the rows that it names, and without the run's coins, which these rows do not
read. It imports no file under Johnson/Desc/ProofFile/Honest/Thread/. Each of the four theorems
`fiveFieldsK14…` builds a term of it from one theorem of these two files: SO LEAN COMPARES THE FORMS
OF THESE TWO FILES WITH `FiveFields`: by the shared chain's own names `noZeroFactor` and
`RowAnswer`, and by `rowsK`, which FiveFields.lean declares in the place of the rows that `K14Asks`
names (the field Rw of `holds2`). That `rowsK` is these rows is said in
Johnson/Desc/ProofFile/Honest/K14/FiveFieldsAsks.lean (`rw_holds2`), a file that is not imported
here.

Main names (namespace `Bind.ForProver`). In the four `fiveFieldsK14…` the parameters are
`Desc.K14.p14Of Z.p.chains l`, the shared chain's own off Z, and the reader of the coins is
`fun rc => rc 0`: the coins of the item 0. The list l is these parameters' field `beforePoint`,
which no field of `FiveFields` reads.
  **`fiveFieldsK14_at`**: from `fiveFields_at`: at a value Z of `ProofFile.Pub`, where the test `rowsFit`
    passes and the code has at most 2^32 positions: `FiveFields` at the predicate
    `validAt (shapeOf Z) Z`, the stored table being `storedW Z` at the input's index and coins, the
    reader of the index the identity.
  **`fiveFieldsK14_inScope`**: from `fiveFields_inScope`: the same at public files in the goals'
    scope, at every second hash function o and every Z that the maker of the public part
    (`ProofFile.pubPlain`) returns of them, with no other premise on Z. That the maker returns at any
    files is not said here: see the limits of FiveAt.lean.
  **`fiveFieldsK14Idx_at`**, **`fiveFieldsK14Idx_inScope`**: from `fiveFieldsIdx_at` and
    `fiveFieldsIdx_inScope`: the same at inputs whose index is read as `Cm.Idx`: at the predicate
    `validIdxAt (shapeOf Z) Z`, the reader of the index being
    `fun i => ⟨OnBytes.HonestTrace.entryOf i⟩`.
  **`fiveFields_of_imp`**: a law on the structure, at all parameters; plain monotony: `FiveFields`
    at a predicate and a stored table gives `FiveFields` at every predicate that implies the first
    and every stored table that agrees with the first, at the inputs of the second predicate, at
    the parameters' item: the one item at which the five fields read the stored table.

A limit on the coins, before the others. The rule of use that follows is set here to the letter,
between the outer marks « »; it has fourteen lines; each begins at the margin, and where it is
wrapped its further lines are set in by two blanks. (With the outer marks off, each of the fourteen
joined out of its wrapped lines by one blank, the two blanks dropped, and a line feed behind each,
its sha256 is 3932bf675906858e61b2b8357e478daa31c5762609bd99ca1f2c25782d3696e3.)
«A LIMIT ON THE COINS: THE RULE OF USE, AT ITS ONE HOME.
THE LABEL, in one spelling, wherever it stands: «NOT IN FRONT OF A LAW OVER COINS».
THE WORDS. A LETTER is an open parameter of a statement: something that the statement binds and does
  not write out as a term. THE COINS are the committer's randomness (pads, tails, encoding
  randomness) and a run's coins. THE COMMITTER is the honest construction that makes the key, the
  stored table and the explicit input of index, coins and seed. A premise TIES a letter to the coins
  if, at a fixed value of that letter, it can hold at some values of the coins and fail at others. A
  premise that names no coin ties nothing; nor does one that holds at every value of the coins
  whatever the letter is.
WHAT A LAW OVER COINS IS: a statement whose END says how what is sent or shown is DISTRIBUTED over
  the coins: a measure, a simulator's equation, a bound on a distance. A theorem that merely binds
  the coins by "for all" is none.
WHAT IS NONE, THOUGH A MEASURE STANDS IN IT: a bound on the probability that an honest proof is
  REJECTED (the library's Complete and CompleteOn). It says nothing of what a verifier learns, and
  the statements that bear this label are made to feed it. There Lean itself asks what matters: each
  premise is shown at each sample point, or its failure's probability goes into the bound.
THE THOUGHT: a premise that ties a letter to the coins picks among the coins. Such a letter may be a
  key, a stored table, a reader of it, an explicit input, a seed, or a predicate ("valid") that
  reads one of these. Whoever uses a statement with such a premise on the way to a law over coins,
  AND LEAVES THE LETTER A LETTER, has conditioned, without saying so, the very measure of which that
  law speaks.
THE BAR: a statement that bears the label is not used on the way to a law over coins.
THE "UNLESS": the bar lifts in one case alone: EVERY letter that a premise ties to the coins is
  dealt with as follows, and EACH such premise is shown, by a lemma, at EVERY value of the coins. A
  letter for a VALUE (a key, a table, a reader, an explicit input) is replaced by the TERM that the
  committer makes of index and coins (and of the seed, where that term takes one). A letter for a
  PREDICATE is not replaced: the lemma shows the predicate AT THAT MADE INPUT, at every value of the
  coins. Then the statement holds at every value of the coins and conditions on none. It may then be
  called under the law's own binder over the coins, by name, and that law's measure takes in the
  making of these terms.
WHERE THE LEMMA IS NAMED: beside the call, in the file that lifts the bar; the labelled file's own
  ground may name it too. So «the bar is flat» says: this file names no such lemma. A lemma lifts
  the bar; a sentence never does.
THE SEED: in a law over coins the seed too is the term that the committer makes of index and coins:
  no letter for the seed beside the coins. A lemma that holds at every seed may be CALLED at that
  term; what is barred is a LAW that keeps a letter for the seed.
WHO INHERITS: a statement that calls a labelled one and keeps one of its tied letters a letter bears
  the label in its turn, with a ground of its own.
A SECOND KIND OF PREMISE reads no coin, but the hidden input or the Script (the cells are the
  index's; the request can be served). It conditions no measure; it narrows the inputs of which a
  law speaks. A statement with such a premise stands in front of a law over coins only if that law
  NAMES the premise in its own statement, as a premise on the hidden input or on the Script, and
  never tells it as public.
EACH FILE THAT BEARS THE LABEL TELLS ITS OWN GROUND: which letter stands under which premise, and of
  which of the two kinds that premise is; and which made term and which lemma, by name, lift the
  bar, or «none: the bar is flat».
This is a rule of use. It is no theorem, and it says of nothing that it is hidden.»
This file's own ground. `fiveFieldsK14_at`, `fiveFieldsK14_inScope`, `fiveFieldsK14Idx_at` and
`fiveFieldsK14Idx_inScope` bear the label. The letter: w.key, the key of the input w over which each
field of the structure ranges. The premise that ties it to the coins, a premise of the first kind:
`validAt` in the first two, `validIdxAt` in the last two: it says that w.key is the key made of
w.w₀, w.rc and some seed. Their other premises (hfit, ha; hP, h) speak of Z and the public files:
they read no coin, no hidden input and no Script: of neither kind. Their stored table is no letter:
it is the term `storedW` at the input's own index and coins. What lifts the bar: the made term is
`oodSh sh Z ⟨w₀, rc, sd⟩`, at `Cm.Idx` `oodIdxSh sh Z ⟨i, rc, sd⟩`; the lemma that shows the premise
at it, at every value of the coins, is `validAt_oodSh` (Johnson/Bind/ForProver/FiveAt.lean), at
`Cm.Idx` `validIdxAt_oodIdxSh` (Johnson/Bind/ForProver/FiveAtIndex.lean). In both lemmas the seed sd
is a letter: the rule on the seed binds whoever states a law. `fiveFields_of_imp` bears the label
too. There `valid`, `stored`, `valid'` and `stored'` are all letters: the first two under F, whose
fields `tab` and `ans` reach the coins; the last two under hv and hs. hv and hs are bound over every
input and by themselves pick among no coins: what picks is `valid' w`, which stands in front of each
field of the conclusion. No made term and no lemma is named for them: the bar is flat.
The sealed limit on the same matter, in the words of Johnson/Bind/ForProver/FiveAtIndex.lean under
the heading "A limit on the coins, before the others.", in two pieces. The one sentence between them
is left out: it names the two lemmas above as the safe forms among these files, says that there the
coins come first and the key is made of them, and points on to later files by the ends of their
theorems' names.
«UNDER validAt, AT A FIXED INDEX AND KEY, THE PADS THAT THE ANSWERS READ ARE NO COINS. (Alike under
`validIdxAt`; why: Johnson/Bind/ForProver/FiveAt.lean, under the same heading.) That is the
protocol's own state and no fault. BUT: a law that takes the committer's pads as uniform and
independent and ranges over w.rc with w.key a letter under validAt (the form hw : Vd wr → validIdxAt
… wr) would range over one point in the pads: hollow in them, in silence.»
«In a safe form the key is never a letter: it is written as the term made of index, coins and seed.
Where a statement stands at single values, the seed may be a letter, bound with index and coins.
Where it states a distribution over the coins, the seed too is written as the term made of index and
coins, at the run's own name (Johnson/Bind/ForProver/Ood.lean, Limits): no letter for the seed
beside the coins. And no strategy or simulator may branch on validAt: it reads index and pads.»
(Why the first sentence of the first piece holds is reckoned by hand, off the texts, in
Johnson/Bind/ForProver/FiveAt.lean under the same heading; by that file's own word no theorem of it
says so.) The premise hv of `fiveFields_of_imp` (`∀ w, valid' w → valid w`), taken at `validAt` or
`validIdxAt` for `valid`, has the form that is written out in the first piece (`hw : Vd wr →
validIdxAt … wr`): whoever proves hv at a thread's own "valid" brings this limit to that thread. The
head of Johnson/Desc/ProofFile/Honest/K14/FiveFields.lean says of the structure itself that under a
"valid" that leaves the key and the stored table letters, `ans` and `tab` fix the pads and tails.

Limits. `FiveFields` AT `validAt` OR `validIdxAt` IS NOT "THE FIVE FIELDS OF `K14Asks` ARE MET".
These two are predicates of this folder: that any thread's own "valid" implies one of them, and that
its stored table agrees with `storedW Z` at the item 0, is not said here, of
`ProofFile.Honest.SharedThread.lettersShared` or of any other thread. These two facts are the premises hv
and hs of `fiveFields_of_imp`, which then gives `FiveFields` at the thread's own valid and stored
table; it says of no predicate and no table that its premises hold, and at a predicate with no
member its conclusion says nothing. What a thread's "valid" may itself say of a key, and what has to
be proved from how the committer makes the key, is ruled at (V) in the head of
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean; that rule is not retold here. `storedW Z` holds
nothing at any other item; a thread's table may. `K14Asks` is not imported here and no term of it is
built: that `FiveFields` at a thread's own valid and stored table gives its five fields is said in
FiveFieldsAsks.lean (`five_gives`), which this file does not import. `tab` and `ans` reach the text
of `K14Asks` through `rw_holds2` alone, in that file. The five are five of its sixteen fields. WHAT
`validAt` IS: it lays none of the five into "valid": it says that the input's key is `oodSh`
(Johnson/Bind/ForProver/Ood.lean) at the input's own index and coins, at some typed seed; `key`,
`seeds` and `ans` are then theorems on `oodSh`. `validIdxAt` likewise, with `oodIdxSh`. It is a
clause on the input's key: a thread whose "valid" is meant to bear no such clause takes it of the
run's own input, not of "valid" (not shown in this file). The stored table is tied by no predicate:
it is laid as the parameter. The seed is any typed seed: the four statements tie it to no hash, no
root and no table's name. NOTHING NEW IS PROVED OF THE TABLE OR THE KEY: each of the four proofs
lays the five parts of a theorem that stands into the structure, through
`ProofFile.Honest.K14.fiveFields_of_texts`, and each part meets its field by unfolding; new is only that
Lean has checked that they meet. `key` and `seeds` hold by the way the seed is made: its type admits
no factor 0, and it is written out in words below the prime; they say nothing of seeds that are read
off bytes. `cols` and `tab` hold at every input, valid or not. NO HONEST PROVER IS WRITTEN HERE: the
stored table is `storedW Z`, not a prover's, and the key is the input's, not one that a prover
reads. Stored table and key are one committed table's; which of the protocol's tables it is, the
first or a copy, is not said here. The coins are read at the item 0 alone: a thread that reads them
at the parameters' item reads the same, because that item is 0 (`p14Of_item`,
Johnson/Bind/ForProver/JoinsK14.lean); a thread that reads them at another item is not served. In
the sentences of FiveAt.lean and FiveAtIndex.lean the coins stand as `⟨(rc 0).pad, (rc 0).tail⟩`:
that is `rc 0` by the structure's eta; `fun rc => rc 0` types because the `TableRand` of
`FiveFields` is the frame's (`ProofFile.Honest.TableRand`). The limits of FiveAt.lean and FiveAtIndex.lean
stand, but for "THAT THEIR FORMS FIT A CALLER IS NOT COMPILED HERE" (FiveAt.lean; in small letters
in FiveAtIndex.lean), which is lifted as far as `FiveFields` goes and no further. At the reading
`Reading.gl` and at no other. No completeness of any protocol, no index privacy; nothing on any
program.
Who calls it. AtFullSide/K14/FiveValid.lean and E2E/KeyFiveFields.lean, among others. The join of
the five to `K14Asks` is `asks_of_five` (from `FiveFields` and `K14Asks`' eleven other fields:
Johnson/Desc/ProofFile/Honest/K14/FiveFieldsAsks.lean), which is not imported here.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.FiveAtIndex
import Johnson.Desc.ProofFile.Honest.K14.FiveFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (TableKey)
open ProofFile.Honest (Weights TableRand Common)
open ProofFile.Honest.K14 (FiveFields fiveFields_of_texts)

/-- **The structure at `validAt`.** Where `rowsFit` passes and the code has at most 2^32 positions:
`FiveFields` at the predicate `validAt`, the stored table `storedW Z`, the index read as it is, the
coins at the item 0.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem fiveFieldsK14_at (Z : ProofFile.Pub) (l : List (ℕ × ℕ))
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (ha : (shapeOf Z).a ≤ 32) :
    FiveFields (Desc.K14.p14Of Z.p.chains l) (validAt (shapeOf Z) Z)
      (fun w => storedW Z w.w₀ w.rc) id (fun rc => rc 0) :=
  have e := fiveFields_at Z l (Desc.K14.p14Of Z.p.chains l) rfl hfit ha
  fiveFields_of_texts e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

/-- **The structure at `validAt`, at files in scope.** The same conclusion at every Z that the maker
of the public part returns of public files in the goals' scope.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem fiveFieldsK14_inScope {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true) {o : ProofFile.SecondHashFunctionArgument}
    {Z : ProofFile.Pub} (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z) (l : List (ℕ × ℕ)) :
    FiveFields (Desc.K14.p14Of Z.p.chains l) (validAt (shapeOf Z) Z)
      (fun w => storedW Z w.w₀ w.rc) id (fun rc => rc 0) :=
  have e := fiveFields_inScope hP h l (Desc.K14.p14Of Z.p.chains l) rfl
  fiveFields_of_texts e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

/-- **The structure at `validIdxAt`.** As `fiveFieldsK14_at`, at inputs whose index is a `Cm.Idx`,
read through `OnBytes.HonestTrace.entryOf`.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem fiveFieldsK14Idx_at (Z : ProofFile.Pub) (l : List (ℕ × ℕ))
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true)
    (ha : (shapeOf Z).a ≤ 32) :
    FiveFields (Desc.K14.p14Of Z.p.chains l) (validIdxAt (shapeOf Z) Z)
      (fun w => storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc)
      (fun i : Cm.Idx => (⟨OnBytes.HonestTrace.entryOf i⟩ : Weights)) (fun rc => rc 0) :=
  have e := fiveFieldsIdx_at Z l (Desc.K14.p14Of Z.p.chains l) rfl hfit ha
  fiveFields_of_texts e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

/-- **The structure at `validIdxAt`, at files in scope.** The same conclusion at every Z that the
maker of the public part returns of public files in the goals' scope.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem fiveFieldsK14Idx_inScope {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true)
    {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub} (h : ProofFile.pubPlain o P.pol P.lay P.KL = .ok Z)
    (l : List (ℕ × ℕ)) :
    FiveFields (Desc.K14.p14Of Z.p.chains l) (validIdxAt (shapeOf Z) Z)
      (fun w => storedW Z ⟨OnBytes.HonestTrace.entryOf w.w₀⟩ w.rc)
      (fun i : Cm.Idx => (⟨OnBytes.HonestTrace.entryOf i⟩ : Weights)) (fun rc => rc 0) :=
  have e := fiveFieldsIdx_inScope hP h l (Desc.K14.p14Of Z.p.chains l) rfl
  fiveFields_of_texts e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2

/-- **The structure passes to a narrower predicate.** A law on the structure
`ProofFile.Honest.K14.FiveFields`, at all its parameters; plain monotony in the predicate: each of the
five fields begins "at every valid input". From a predicate `valid` and a stored table `stored` to
every predicate `valid'` that implies `valid` and every table `stored'` that agrees with `stored`,
at the inputs of `valid'`, at the item `Q.item`: the one item at which the five fields read the
table; what the two tables hold at other items is not compared. It says of no `valid'` and no
`stored'` that these two premises hold; at a `valid'` with no member they hold idly and the
conclusion says nothing.
«NOT IN FRONT OF A LAW OVER COINS: valid' and stored' are letters; no lemma here shows valid' at a
made input, nor stored' to be the made table there: the bar is flat. Whoever shows both at the made
input at every value of the coins lifts it, by these lemmas' names.» (Set here to the letter, like
the rule of use in this file's head, which says what the label means.) -/
theorem fiveFields_of_imp {W₀ Rc : Type} {Q : Desc.K14.P14}
    {valid valid' : Common W₀ Rc TableKey → Prop}
    {stored stored' : Common W₀ Rc TableKey → ℕ → ℕ → Option (List UInt64)}
    {weights : W₀ → Weights} {rand : Rc → TableRand}
    (F : FiveFields Q valid stored weights rand) (hv : ∀ w, valid' w → valid w)
    (hs : ∀ w, valid' w → ∀ x, stored' w Q.item x = stored w Q.item x) :
    FiveFields Q valid' stored' weights rand where
  cols w hw p hp := by
    have e : stored' w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p =
        stored w (Desc.K14.readsAtLoc Q.S.fold Q.item).item p := hs w hw p
    rw [e]
    exact F.cols w (hv w hw) p hp
  tab w hw x hx r hr := by
    rw [hs w hw x]
    exact F.tab w (hv w hw) x hx r hr
  key w hw := F.key w (hv w hw)
  seeds w hw := F.seeds w (hv w hw)
  ans w hw := F.ans w (hv w hw)

end Bind.ForProver

#print axioms Bind.ForProver.fiveFieldsK14_at
#print axioms Bind.ForProver.fiveFieldsK14_inScope
#print axioms Bind.ForProver.fiveFieldsK14Idx_at
#print axioms Bind.ForProver.fiveFieldsK14Idx_inScope
#print axioms Bind.ForProver.fiveFields_of_imp
