-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesSentBeforeTestFromSentTable.lean: the table that a sending's part sends (the kind K1)
shows the sending's own written column, and that column reads its caller's rows inside the messages'
tables alone. The two halves are `col_treeTable`, at every place of the kind K1 that passes its test
on the plan, and `sentCol_congr`, at every place of the kind. From them `old_of_table` proves
`OldAt` (ColsTerm.lean in this folder) at a job made of one sending (`jobOne`, JobOne.lean in this
folder), under the hypotheses below. `OldAt` is a hypothesis of `cols_term` (ColsTerm.lean), a
theorem on a proximity test: it ties the tables that are available before the test to the job's
trees. The one tree of `jobOne` has the sending's own written column, at rows that the job computes
anew. One definition; theorems with their proofs.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. A sending is a sub-protocol of
the kind K1 (Johnson/Desc/K1/Own.lean). Its place P (`K1.Par`, Johnson/Desc/K1/Send.lean) has its
public numbers: among them the codes, and the oracle messages in the order of sending (`P.sent`).
`shapeAt P k` is the shape of message number k. `Rows` is what a caller gives of one oracle message:
every row and every row's tail, as field values; a family of rows V gives a `Rows` for each
message's number. `col P V τ x` is the written column of the place's tree number τ at the position
x: a list of words (`UInt64`). These three are in Johnson/Prover/Send/Core.lean. A table (`Table`,
the frame) has two numbers, `logLength` and `words`, and a symbol at every natural number;
`Table.col` writes the symbol at a position as words. A part (`Part`, the frame) is the prover's
side of a stretch of a sub-protocol's rounds. The sending's part is `sendPart`
(Johnson/Desc/ProofFile/Honest/K1/Part.lean): its first move, where it returns, sends `treeTables`
at the part's own rows. The available tables are a structure E (`Env`,
Johnson/Desc/ProofFile/Honest/Side.lean): `E.tree` gives the table for a source, and `E.sent` is how
many trees the chain has sent so far. The source `own n` (`Fmt.TreeSource`, Decl/Declared.lean) names
tree number n of those that the chain sends. A job (`TestJob`, Test.lean in this folder) is what a
caller supplies for its proximity test. w is the prover's input, fr a front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean: what the job's functions are given of the run before the
test), C a family of coins (`TestCoins`, Test.lean). The job's rows are `Q.rows w (C.mem 0) Pst`
(`OneSent.rows`, JobOne.lean), where Pst is the first stage's state
`(jobOne p Q rec₀).first w fr C`.

  `old_of_table`: under the hypotheses below: `OldAt E T₀ src₀`. T₀ is the list of trees of
    `jobOne p Q rec₀` at w, fr and C: one tree, whose column is `col Q.P` of tree number 0 at the
    job's rows. src₀ is `own n` at number 0
  `col_treeTable`: the table that the sending's part makes of tree number τ (`treeTables`,
    Johnson/Desc/ProofFile/Honest/K1/Part.lean) shows, at every position, the written column. In
    Lean: where `K1.planOkOwn P` passes and T is entry number τ of `treeTables P V`:
    `T.col x = col P V τ x`, at every natural number x
  `sentCol_congr`: two families V and V' with `SameRows P V V' k` at every k below `P.sent.size`
    have the same written column: `col P V τ x = col P V' τ x`, at every τ and x. No hypothesis on
    the place
  `SameRows P V V' k`: two families of rows agree at message number k: on its main rows below the
    code's message length, on their tails below the tail's length; the like for its mask rows. A
    definition: a structure of six propositions, one for each field of `Rows`. The rows are those
    below the shape's two numbers of rows; the codes are those that the shape names
  `canonW_col`: every word of the written column is the written form `ofF y` of an element y of the
    base field (`CanonW`, TableCol.lean in this folder). No hypothesis
  `col_of_sym`: for a table with `words` n whose symbol at a position pos has, as entry i, word
    number i of `c pos` read by `toF` (0 where there is no such word): its `Table.col` at x is
    `c x`, where `c x` has the length n and meets `CanonW`
  `mainSyms_congr`, `maskSyms_congr`: under `SameRows P V V' k`, the two lists of words of which
    `col` is made, `mainSyms` and `maskSyms` (Core.lean) of message number k at a position, are the
    same at V and at V'
  `symF_congr`: `symF` (Core.lean: a code word's symbol over the base field) is the same at two
    messages that agree below the code's `l` and two tails that agree below its `r`
  `canonW_words3`: the three words (`words3`, Johnson/Prover/Link/SwitchCols.lean) of `ofE y`, the
    written form of an element y of the extension field, meet `CanonW`
  `flatMap_congr'`: two functions that agree on a list's elements have the same `flatMap` over it

By what. `sentCol_congr` unfolds `col` and calls `flatMap_congr'` with `mainSyms_congr` and
`maskSyms_congr`; these call `symF_congr` and `symG_congr` (Johnson/Prover/Link/Base.lean: the same
for a symbol over the extension field). `col_treeTable`: at a place that passes `K1.planOkOwn` the
trees' layout is there (`lay_some`) and the written column has the tree's width (`length_col`; both
Johnson/Prover/Send/Enc.lean); `Own.treesMade_eq` (Johnson/Desc/Own/TreesAgree.lean) rewrites
`P.trees`; then `col_of_sym` with `canonW_col`. `col_of_sym` goes entry by entry, by `toF_ofF`
(OnBytes/Slice/Field.lean). `old_of_table`: the field `inFront` of `OldAt` is hn; the field `cols`
follows by unfolding `colAt` (PlanOpens.lean in this folder), by hE, by `col_treeTable` at tree
number 0 and by `sentCol_congr`.

Hypotheses of `old_of_table`. hP: `K1.planOkOwn Q.P` passes (Johnson/Desc/K1/Own.lean: tests on the
plan only). hn: n is below `E.sent`: more than n trees are sent so far. hE: the available table for
the source `own n` is T, from a place pl that nothing reads. hT: T is entry number 0 of
`treeTables Q.P V₁`. hV: `SameRows Q.P V₁ V' k`, with V' the job's rows, at every k below
`Q.P.sent.size`. All of p, Q, rec₀, w, fr, C, E, n, V₁, pl and T are free parameters.

Limits.
- That the available table is the sending's table itself (hE with hT), and that the two families of
  rows agree (hV), are hypotheses: neither is proved here.
- The first can be derived from no thread of the frame (`Thread`,
  Johnson/Desc/ProofFile/Honest/Thread/Thr.lean; its statement at a border of a chain is `Thr`) at
  all the states of a run and available tables at which that statement holds. A thread compares the
  available table with its own by `Table.same` only (`Thread.handAt`; both in that file): the two
  numbers, and the columns below the length. So `old_of_table` is a theorem at one family of
  available tables. The form whose hypothesis on the table can be proved from a thread is
  `oldAt_of_same` (TreesSentBeforeTestFromSameColumns.lean in this folder): there that hypothesis is `Table.same` between the
  two tables.
- The second is a matter of the coins that the book carries (CoinsTieBook.lean). The book is `ProverCoinCounts`
  (the frame): the book of coins, public data that goes with a description. `same_one`
  (SameAtOne.lean in this folder) derives hV at one family V₁ from `CoinsTie`, and
  `coinsTie_of_book` (CoinsTieBook.lean in this folder) derives `CoinsTie` from `BookTies`, each
  under further hypotheses.
- That the place passes its own test on the plan (`K1.planOkOwn`) is a hypothesis of `col_treeTable`
  and of `old_of_table`.
- `SameRows` asks more than `col` reads: it asks the main rows and their tails over both fields
  (`mainE`, `mainTlE`, `mainF`, `mainTlF`), whatever the shape's `mainDeg`, while `mainSyms` reads
  those over the extension field where `mainDeg == 3` and those over the base field otherwise.
- `old_of_table` is stated at `jobOne` only: a job with one tree.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobOne
import Johnson.Desc.ProofFile.Honest.K12.ColsTerm
import Johnson.Desc.ProofFile.Honest.K12.TableCol
import Johnson.Desc.ProofFile.Honest.K1.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open Johnson.Prover.Send (Rows col shapeAt mainSyms maskSyms length_col lay_some)

variable {W X : Type}

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Two families of rows V and V' agree at message number k, inside its tables: at the rows below
the shape's number of rows, at a row's entries below its code's message length `l`, and at its
tail's entries below the tail's length `r`. -/
structure SameRows (P : K1.Par) (V V' : ℕ → Rows) (k : ℕ) : Prop where
  mainE : ∀ r j, r < (shapeAt P k).mainRows →
    j < (codeOf (P.codes.base.getD (shapeAt P k).code default)).l →
    (V k).mainE r j = (V' k).mainE r j
  mainTlE : ∀ r q, r < (shapeAt P k).mainRows →
    q < (codeOf (P.codes.base.getD (shapeAt P k).code default)).r →
    (V k).mainTlE r q = (V' k).mainTlE r q
  mainF : ∀ r j, r < (shapeAt P k).mainRows →
    j < (codeOf (P.codes.base.getD (shapeAt P k).code default)).l →
    (V k).mainF r j = (V' k).mainF r j
  mainTlF : ∀ r q, r < (shapeAt P k).mainRows →
    q < (codeOf (P.codes.base.getD (shapeAt P k).code default)).r →
    (V k).mainTlF r q = (V' k).mainTlF r q
  mask : ∀ r j, r < (shapeAt P k).maskRows →
    j < (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)).l →
    (V k).mask r j = (V' k).mask r j
  maskTl : ∀ r q, r < (shapeAt P k).maskRows →
    q < (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)).r →
    (V k).maskTl r q = (V' k).maskTl r q

theorem symF_congr (C : Fmt.M1.Code) (x : ℕ) (m m' r r' : ℕ → GF) (hm : ∀ j, j < C.l → m j = m' j)
    (hr : ∀ q, q < C.r → r q = r' q) :
    Johnson.Prover.Send.symF C x m r = Johnson.Prover.Send.symF C x m' r' := by
  unfold Johnson.Prover.Send.symF
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun q hq => by rw [hr q (Finset.mem_range.1 hq)])
    (Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_range.1 hj)])

theorem mainSyms_congr (P : K1.Par) (V V' : ℕ → Rows) (k x : ℕ) (h : SameRows P V V' k) :
    mainSyms P V k x = mainSyms P V' k x := by
  unfold mainSyms
  refine flatMap_congr' _ fun r hr => ?_
  have hr' := List.mem_range.1 hr
  rw [symG_congr _ x _ _ _ _ (fun j hj => h.mainE r j hr' hj) (fun q hq => h.mainTlE r q hr' hq),
    symF_congr _ x _ _ _ _ (fun j hj => h.mainF r j hr' hj) (fun q hq => h.mainTlF r q hr' hq)]

theorem maskSyms_congr (P : K1.Par) (V V' : ℕ → Rows) (k x : ℕ) (h : SameRows P V V' k) :
    maskSyms P V k x = maskSyms P V' k x := by
  unfold maskSyms
  refine flatMap_congr' _ fun r hr => ?_
  have hr' := List.mem_range.1 hr
  rw [symG_congr _ _ _ _ _ _ (fun j hj => h.mask r j hr' hj) (fun q hq => h.maskTl r q hr' hq)]

/-- **Families of rows that agree inside the messages' tables have the same written column.** h:
`SameRows` at every message of the place. -/
theorem sentCol_congr (P : K1.Par) (V V' : ℕ → Rows) (τ x : ℕ)
    (h : ∀ k, k < P.sent.size → SameRows P V V' k) : col P V τ x = col P V' τ x := by
  unfold col
  have hk : ∀ k ∈ (List.range P.sent.size).filter fun k =>
      ((Own.treesMade P.codes P.sent).getD {}).tree[k]? == some τ, k < P.sent.size :=
    fun k hk => List.mem_range.1 (List.mem_of_mem_filter hk)
  exact congrArg₂ (· ++ ·)
    (flatMap_congr' _ fun k hm => mainSyms_congr P V V' k x (h k (hk k hm)))
    (flatMap_congr' _ fun k hm => maskSyms_congr P V V' k x (h k (hk k hm)))

theorem canonW_words3 (y : GE) : CanonW (words3 (ofE y)) := fun w hw => by
  simp only [words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

/-- Every word of the written column is the written form of an element of the base field. -/
theorem canonW_col (P : K1.Par) (V : ℕ → Rows) (τ x : ℕ) : CanonW (col P V τ x) := by
  intro w hw
  unfold col at hw
  rcases List.mem_append.1 hw with hw | hw
  · obtain ⟨k, -, hw⟩ := List.mem_flatMap.1 hw
    unfold mainSyms at hw
    obtain ⟨r, -, hw⟩ := List.mem_flatMap.1 hw
    split at hw
    · exact canonW_words3 _ w hw
    · exact ⟨_, List.mem_singleton.1 hw⟩
  · obtain ⟨k, -, hw⟩ := List.mem_flatMap.1 hw
    unfold maskSyms at hw
    obtain ⟨r, -, hw⟩ := List.mem_flatMap.1 hw
    exact canonW_words3 _ w hw

/-- A table made of a column function shows it, where the column has the stated width. hl: `c x` has
the length n. hc: every word of `c x` is the written form of an element of the base field. -/
theorem col_of_sym (a n : ℕ) (c : ℕ → List UInt64) (x : ℕ) (hl : (c x).length = n)
    (hc : CanonW (c x)) :
    (⟨a, n, fun pos i => toF ((c pos).getD i.val 0)⟩ : Table).col x = c x := by
  refine List.ext_getElem (by simp [Table.col, hl]) fun i h1 h2 => ?_
  simp only [Table.col, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]
  obtain ⟨y, hy⟩ := hc _ (List.getElem_mem h2)
  rw [hy, toF_ofF]

/-- **The sending's table shows the written column.** hP: the place passes `K1.planOkOwn`. hT: T is
entry number τ of `treeTables P V`. x is any natural number. -/
theorem col_treeTable (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (τ x : ℕ)
    (T : Table) (hT : (K1.treeTables P V)[τ]? = some T) : T.col x = col P V τ x := by
  obtain ⟨Ly, hL, eL⟩ := lay_some P hP
  have eT : P.trees = Ly.shapes.toList := by
    unfold K1.Par.trees
    rw [Own.treesMade_eq, hL]
    rfl
  unfold K1.treeTables at hT
  rw [List.getElem?_map, List.getElem?_zipIdx, eT] at hT
  cases ht : Ly.shapes.toList[τ]? with
  | none =>
    rw [ht] at hT
    cases hT
  | some t =>
    rw [ht] at hT
    obtain rfl := Option.some.inj hT
    have hτ : τ < Ly.shapes.size := by
      have := (List.getElem?_eq_some_iff.1 ht).1
      simpa using this
    have hg : Ly.shapes.getD τ {} = t := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ht]
      rfl
    have hl := length_col P V hP τ x (by rw [eL]; exact hτ)
    rw [eL, hg] at hl
    have e0 : 0 + τ = τ := Nat.zero_add τ
    show (⟨t.logN, t.mainWidth + t.maskWidth,
      fun pos i => toF ((col P V (0 + τ) pos).getD i.val 0)⟩ : Table).col x = _
    rw [e0]
    exact col_of_sym _ _ (col P V τ) x hl (canonW_col P V τ x)

/-- **`OldAt` at the job made of a sending.** n: the tree's number among the chain's own. hE with
hT: the available table for the source `own n` is the sending's table of tree number 0 at the rows
V₁. hV: V₁ and the job's rows agree at every message of the place. hn: more than n trees are sent so
far. -/
theorem old_of_table (p : P12) (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (C : TestCoins) (E : Env) (n : ℕ) (V₁ : ℕ → Rows) (pl : VerifiableInference.Desc.Place)
    (T : Table)
    (hP : K1.planOkOwn Q.P = true) (hn : n < E.sent) (hE : E.tree (.own n) = some (pl, T))
    (hT : (K1.treeTables Q.P V₁)[0]? = some T)
    (hV : ∀ k, k < Q.P.sent.size →
      SameRows Q.P V₁ (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) k) :
    OldAt E ((jobOne p Q rec₀).trees₀ w fr C.mem ((jobOne p Q rec₀).first w fr C))
      (fun k => [Fmt.TreeSource.own n].getD k (.own 0)) := by
  refine ⟨fun k hk m hm => ?_, fun k hk x _ => ?_⟩
  · have k0 : k = 0 := Nat.lt_one_iff.1 hk
    subst k0
    have e : Fmt.TreeSource.own n = .own m := hm
    injection e with e'
    exact e' ▸ hn
  · have k0 : k = 0 := Nat.lt_one_iff.1 hk
    subst k0
    show colAt E.tree (.own n) x =
      col Q.P (Q.rows w (C.mem 0) ((jobOne p Q rec₀).first w fr C)) 0 x
    unfold colAt
    rw [hE]
    show T.col x = _
    rw [col_treeTable Q.P V₁ hP 0 x T hT, sentCol_congr Q.P _ _ 0 x hV]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.flatMap_congr'
#print axioms ProofFile.Honest.K12.symF_congr
#print axioms ProofFile.Honest.K12.mainSyms_congr
#print axioms ProofFile.Honest.K12.maskSyms_congr
#print axioms ProofFile.Honest.K12.sentCol_congr
#print axioms ProofFile.Honest.K12.canonW_words3
#print axioms ProofFile.Honest.K12.canonW_col
#print axioms ProofFile.Honest.K12.col_of_sym
#print axioms ProofFile.Honest.K12.col_treeTable
#print axioms ProofFile.Honest.K12.old_of_table
#print axioms ProofFile.Honest.K12.SameRows
