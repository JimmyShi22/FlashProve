-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookThird.lean: the third of the tests on a book of coins is derived, for one chain of a
description, from a test on numbers, and these numbers are derived from the description's rounds'
data. The tests on a book are `ProverCoinCounts.clauses` in the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean). The third has the name "a place states more mask words
than its parts have coins" and is `masksOk` at each of the three chains. It reads the oracle
messages that the sub-protocols declare: at each place, the mask words of all tenants. Two facts
bound these without reading a tenant: `mask_zero` and `mask_le_words`. General in the description:
sections 2 and 3 hold at every list of sub-protocols, section 4 at every description whose `data`
returns, sections 5 and 6 at all lists and all rounds' data. Definitions and theorems.

In the list: a description F (`FileDescription`, Johnson/Desc/Block.lean) has three chains, numbered from
0: the first, the shared and the second. A chain is here the list bs of its sub-protocols (`Block`;
`Chain.blocksInOrder`), each at a place (`Place`: where it is in the description). A sub-protocol declares
its rounds, each with the number of roots that it sends (`entry.roots`), and for each root the
oracle message under it (`oracles`). An oracle message (`Oracle`, Johnson/Desc/Oracle.lean) has the
words of one symbol (`words`) and the tenants that share a symbol (`SymbolComponent`), each with main words
and mask words. `maskWords b` (the frame) adds up the mask words of all tenants of all oracle
messages of b. `sentOf bs` (Johnson/Desc/Block.lean) lists the log-length and the words of every
oracle message of bs; `Sound.sentAt F c` (Johnson/Desc/Sound/OraclesAre.lean) is that list at chain
number c of F. A chain's rows are `rowsOf bs` (Johnson/RunOne/Sound/KeyListsAtFK.lean): for each
sub-protocol its place and its number of rounds. A book (`ProverCoinCounts`, the frame) is public data that goes
with a description. This file reads only its table l for one chain; a row of l is an address
(`Addr`: a place, and the number of a prover's part there) and a count of coins (`Due`: f elements
of the base field, e of the extension field). Below, f + 3 e at a place is taken of `placeDue l`
there: the counts of all rows of l at that place, added up. `masksOk bs l` says: for every b in bs,
`maskWords b` ≤ f + 3 e at the place of b. The rounds' data D (`WholeD`, OnBytes/Maker/Whole.lean)
are what `F.data file` returns: for each chain a list of rounds (`ds₁`, `ds₂`, `ds₃`; a round:
`RDT`), each with its entry and the shapes of the trees whose roots it sends. A tree's width is the
field `W` of its shape (`Fmt.Shape`).

  `masksOk_of`: for a chain bs, a table l and a number W, under the three hypotheses below:
    `masksOk bs l` passes
  `thirdCheck rows roots W l`: a definition: the test on numbers. It cuts the list roots along the
    rows (`alongN`). At every row: all numbers that are cut out for it are 0, or W ≤ f + 3 e at the
    row's place
  `mask_zero`, `mask_le_words`: the two facts, for a sub-protocol b that is shaped (`Block.shaped`):
    if no round of b sends a root, `maskWords b` is 0; and `maskWords b` ≤ `wordsOf b`
  `wordsOf b`: a definition: the words of one symbol of each oracle message of b, added up
  `told_sum`: where `F.data file` returns D and `F.planOk` passes: the words of all oracle messages
    of chain number c add up to `widths D` from the chain's first tree on (`baseOf`,
    Johnson/Desc/Sound/OraclesAre.lean), over as many trees as the chain declares oracle messages
  `sent_length`: where `blocksOk bs` passes, bs declares as many oracle messages as its rounds send
    roots; `oracles_count`: the same for one shaped sub-protocol
  `widths D base n`: a definition: the widths of the n trees of D with the numbers base, base + 1
    and so on, added up; a number at which D has no tree counts 0
  `widths_chains`: for each of the three chains, `widths D` from the chain's first tree on, over the
    number of the chain's trees, is the sum of the widths of the trees in the chain's own list of
    rounds. No hypothesis
  `roots_later`, `roots_first`: where `F.data file` returns D, the declared rounds' numbers of roots
    are those of the entries in D: list for list at the shared and the second chain. At the first
    chain, if it declares a round, they are the list of `ds₁` followed by 0: D leaves that chain's
    last round out, and that round sends no root
  `entries_of`: for a list of rounds of the data and a list of declared rounds that agree round by
    round (`RoundAsG`, Johnson/Desc/Sound/DataRounds.lean): the declared numbers of roots are those
    of the data's entries, and they are the data's numbers of trees
  `thirdThin idx W l s rows`: a definition: the test on numbers on a short list. idx: numbers of
    rounds; s: the number of the first row's first round. At every row: no element of idx is the
    number of one of the row's rounds, or W ≤ f + 3 e at the row's place. It is written for
    evaluation in Lean's kernel: it does not cut a list that has a number for every round
  `check_of_thin`: if `thirdThin idx W l s rows` passes, and every number in es that is not 0 has
    its position, counted from s, in idx, then `thirdCheck rows es W l` passes
  `with_zero`: that hypothesis on es goes over to es with a 0 appended
  `sendersAre i ds T`: a definition: a test that walks a chain's list of rounds ds, numbered from i.
    A round whose entry has no root and which has no tree is passed over. Every other round must be
    the next element of T: its number, and the widths of its trees. At the end T must be used up
  `senders_spec`: where `sendersAre i ds T` passes: every round of ds whose entry has a root has its
    number in T, and the widths of all trees of ds, in order, are the widths in T, in order
  `alongN rows es`: a definition: each row's place with the next numbers of es, as many as the row
    has rounds; `along_rounds`: the numbers of roots of a chain's rounds, cut along the chain's
    rows, are each sub-protocol's own
  `shaped_parts`: what `Block.shaped` says, as a proposition, without its clause on the tenants'
    degrees; `shaped_of`: `blocksOk bs` gives `Block.shaped` of every b in bs
  `maskWords_eq`, `sent_words`: `maskWords b` as a sum over the oracle messages of b; the words in
    `sentOf bs` add up to the sum of `wordsOf` over bs
  `treeSh_flat`, `sum_lengths`: the shape of a chain's tree number n (`treeShT`) is element number n
    of the chain's rounds' trees, concatenated; how many these are
  `sum_flatMap`, `le_sum_of_mem`, `mem_zip_right`, `map_of_zip`, `sum_getD`: lemmas on lists

By what. `masksOk_of` takes a sub-protocol b of bs. By `along_rounds`, `thirdCheck` says of b that
none of its rounds sends a root, or that W ≤ f + 3 e at its place. In the first case `mask_zero`
gives 0 mask words. In the second, `maskWords b` ≤ `wordsOf b` (`mask_le_words`), which is at most
the sum over bs (`le_sum_of_mem`, `sent_words`), which is at most W. The two facts unfold
`Block.shaped` (Johnson/Desc/Block.lean): a round has as many oracle messages as roots, and the
tenants' main and mask words add up to the words of a symbol. `maskWords_eq` calls `foldl_add_sum`
(E2E/KeyBookFace.lean). `told_sum` follows from `toldShape` (Johnson/Desc/Sound/OraclesAre.lean):
the words that a chain's sub-protocols declare for a tree are the tree's width in D. The hypothesis
`F.sentFit` of `toldShape` comes from `sentFit_of_planOk` (same file). `sent_words` and
`sent_length` call `sentOf_eq` (same file). `roots_later` and `roots_first` call `roundsOfData`
(Johnson/Desc/Sound/DataRounds.lean), and `roots_first` also `counts_of_data`
(Johnson/Desc/Sound/TakenBelowOfData.lean). `widths_chains` unfolds `WholeD.shape`
(OnBytes/Maker/ViewTests.lean); `treeSh_flat` calls `treeShT_cons` (OnBytes/Maker/Trees.lean).

Hypotheses of `masksOk_of`. hb: `blocksOk bs` passes: every sub-protocol of bs passes its own test
on the plan (`Block.planOk`) and is shaped; the proof uses the second only. hW: the words in
`sentOf bs` add up to at most W. hc: `thirdCheck` passes at the rows of bs, the numbers of roots of
the rounds of bs in order, W and l.

Limits.
- The bound is crude: every place that sends a root is compared with W, an upper bound on the words
  of all oracle messages of its whole chain together, and not with its own mask words. Only the
  direction from `thirdThin` to `thirdCheck` to `masksOk` is proved: the test on numbers can fail
  where `masksOk` passes.
- Nothing is evaluated here. E2E/KeyBookThirdNamed.lean evaluates the test on numbers at the key
  file, where the crude bound is enough (`full_third`, `third_named`).
- `masksOk_of` is on one chain. The frame's third test at a description, `masksOk` at all three
  chains, is not stated here (`thirdAt`, E2E/KeyBookPassesNamed.lean).
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookTests
import Johnson.Desc.Sound.OraclesAre
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.Sound.TakenBelowOfData

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (toldShape baseOf sentFit_of_planOk sentOf_eq)
open OnBytes.Maker (WholeD RDT)
open Johnson.RunOne.Sound (rowsOf)
open ProofFile.Honest (Addr Due maskWords masksOk placeDue)

variable {S Cl : Type}

/-! ## 1 Lists -/

theorem sum_flatMap {α β : Type} (f : α → List β) (g : β → Nat) (l : List α) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, ih]

theorem le_sum_of_mem {α : Type} (g : α → Nat) {l : List α} {a : α} (h : a ∈ l) :
    g a ≤ (l.map g).sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

theorem mem_zip_right {α β : Type} : ∀ (as : List α) (bs : List β), bs.length = as.length →
    ∀ y ∈ bs, ∃ x ∈ as, (x, y) ∈ as.zip bs
  | [], [], _, _, hy => by cases hy
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], _, _, hy => by cases hy
  | a :: as, b :: bs, h, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, List.mem_cons_self⟩
    · obtain ⟨x, hx, hz⟩ := mem_zip_right as bs (Nat.succ.inj h) y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hz⟩

theorem map_of_zip {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (as : List α) (bs : List β),
    bs.length = as.length → (∀ x ∈ as.zip bs, g x.2 = f x.1) → bs.map g = as.map f
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: as, b :: bs, h, hz => by
    rw [List.map_cons, List.map_cons, hz (a, b) List.mem_cons_self,
      map_of_zip f g as bs (Nat.succ.inj h) fun x hx => hz x (List.mem_cons_of_mem _ hx)]

/-! ## 2 A shaped sub-protocol -/

/-- The words of one symbol (`Oracle.words`) of each oracle message that a sub-protocol declares,
added up. -/
def wordsOf (b : Block S Cl) : Nat := ((b.oracles.flatMap id).map (·.words)).sum

theorem shaped_parts {b : Block S Cl} (h : b.shaped = true) :
    b.oracles.length = b.rounds.length ∧
      ∀ x ∈ b.rounds.zip b.oracles, x.2.length = x.1.entry.roots ∧
        ∀ o ∈ x.2, (o.tenants.map fun t => t.main + t.mask).sum = o.words := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have hx' := h.2 x hx
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hx'
  refine ⟨hx'.1, fun o ho => ?_⟩
  have ho' := hx'.2 o ho
  rw [Bool.and_eq_true, beq_iff_eq] at ho'
  exact ho'.1

theorem maskWords_eq (b : Block S Cl) :
    maskWords b = ((b.oracles.flatMap id).map fun o => (o.tenants.map (·.mask)).sum).sum := by
  unfold maskWords
  rw [foldl_add_sum (fun t : SymbolComponent => t.mask), Nat.zero_add, sum_flatMap]

/-- A shaped sub-protocol's mask words are at most the words of its oracle messages' symbols. -/
theorem mask_le_words {b : Block S Cl} (h : b.shaped = true) : maskWords b ≤ wordsOf b := by
  obtain ⟨hl, hz⟩ := shaped_parts h
  rw [maskWords_eq]
  unfold wordsOf
  apply List.sum_le_sum
  intro o ho
  obtain ⟨l, hlm, hol⟩ := List.mem_flatMap.1 ho
  obtain ⟨r, -, hrl⟩ := mem_zip_right b.rounds b.oracles hl l hlm
  rw [← (hz (r, l) hrl).2 o hol]
  apply List.sum_le_sum
  intro t _
  omega

/-- A shaped sub-protocol none of whose rounds sends a root declares no mask word. -/
theorem mask_zero {b : Block S Cl} (h : b.shaped = true)
    (h0 : ∀ r ∈ b.rounds, r.entry.roots = 0) : maskWords b = 0 := by
  obtain ⟨hl, hz⟩ := shaped_parts h
  have : b.oracles.flatMap id = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro l hlm
    obtain ⟨r, hr, hrl⟩ := mem_zip_right b.rounds b.oracles hl l hlm
    have := (hz (r, l) hrl).1
    rw [h0 r hr] at this
    exact List.length_eq_zero_iff.1 this
  rw [maskWords_eq, this]
  rfl

/-- A shaped sub-protocol declares as many oracle messages as its rounds send roots. -/
theorem oracles_count {b : Block S Cl} (h : b.shaped = true) :
    (b.oracles.flatMap id).length = (b.rounds.map (·.entry.roots)).sum := by
  obtain ⟨hl, hz⟩ := shaped_parts h
  rw [List.length_flatMap]
  exact congrArg List.sum (map_of_zip (fun r : Fmt.DeclaredRound => r.entry.roots)
    (fun l : List Oracle => (id l).length) b.rounds b.oracles hl fun x hx => (hz x hx).1)

/-! ## 3 A chain: a list of sub-protocols -/

theorem shaped_of {bs : List (Block S Cl)} (h : blocksOk bs = true) :
    ∀ b ∈ bs, b.shaped = true := by
  intro b hb
  have := List.all_eq_true.1 h b hb
  rw [Bool.and_eq_true] at this
  exact this.2

theorem sent_words (bs : List (Block S Cl)) :
    ((sentOf bs).map (·.2)).sum = (bs.map wordsOf).sum := by
  rw [sentOf_eq, List.map_map]
  unfold oraclesOf
  exact sum_flatMap _ _ _

theorem sent_length {bs : List (Block S Cl)} (h : blocksOk bs = true) :
    (sentOf bs).length = ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum := by
  rw [sentOf_eq, List.length_map, sum_flatMap]
  unfold oraclesOf
  rw [List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  exact oracles_count (shaped_of h b hb)

/-- Cuts a list of numbers along rows (place, number of rounds): each place gets the next numbers,
as many as it has rounds, or fewer where the list ends. -/
def alongN : List (Place × Nat) → List Nat → List (Place × List Nat)
  | [], _ => []
  | r :: l, es => (r.1, es.take r.2) :: alongN l (es.drop r.2)

/-- The numbers of roots of a chain's rounds, cut along the chain's rows, are each sub-protocol's
own. -/
theorem along_rounds (bs : List (Block S Cl)) :
    alongN (rowsOf bs) ((bs.flatMap (·.rounds)).map (·.entry.roots)) =
      bs.map fun b => (b.place, b.rounds.map (·.entry.roots)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hl : (b.rounds.map (·.entry.roots)).length = b.rounds.length := List.length_map _
    show (b.place, _) :: alongN (rowsOf bs) _ = _
    rw [List.flatMap_cons, List.map_append, List.take_left' hl, List.drop_left' hl, ih]
    rfl

/-- The test on numbers. At every row: all numbers that `alongN` cuts out of roots for it are 0 (the
place sends no root), or W ≤ f + 3 e, where f and e are the counts of the book's rows at that place,
added up (`placeDue`). -/
def thirdCheck (rows : List (Place × Nat)) (roots : List Nat) (W : Nat) (l : List (Addr × Due)) :
    Bool :=
  (alongN rows roots).all fun x =>
    x.2.all (· == 0) || decide (W ≤ (placeDue l x.1).f + 3 * (placeDue l x.1).e)

/-- **The third test at a chain, from numbers**: if `blocksOk bs` passes, the words of all oracle
messages of bs add up to at most W, and `thirdCheck` passes at the rows and the numbers of roots of
bs, then `masksOk bs l` passes. -/
theorem masksOk_of {bs : List (Block S Cl)} (hb : blocksOk bs = true) (l : List (Addr × Due))
    (W : Nat) (hW : ((sentOf bs).map (·.2)).sum ≤ W)
    (hc : thirdCheck (rowsOf bs) ((bs.flatMap (·.rounds)).map (·.entry.roots)) W l = true) :
    masksOk bs l = true := by
  unfold thirdCheck at hc
  rw [along_rounds, List.all_eq_true] at hc
  unfold masksOk
  rw [List.all_eq_true]
  intro b hbm
  have hs := shaped_of hb b hbm
  have h := hc _ (List.mem_map_of_mem (f := fun b : Block S Cl =>
    (b.place, b.rounds.map (·.entry.roots))) hbm)
  rw [decide_eq_true_eq]
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [mask_zero hs]
    · exact Nat.zero_le _
    · intro r hr
      have := List.all_eq_true.1 h _ (List.mem_map_of_mem (f := fun r : Fmt.DeclaredRound =>
        r.entry.roots) hr)
      exact beq_iff_eq.1 this
  · have h1 := mask_le_words hs
    have h2 : wordsOf b ≤ (bs.map wordsOf).sum := le_sum_of_mem wordsOf hbm
    rw [← sent_words] at h2
    have h3 : W ≤ (placeDue l b.place).f + 3 * (placeDue l b.place).e := of_decide_eq_true h
    omega

/-! ## 4 The numbers, from the rounds' data -/

/-- The widths of the n trees of the rounds' data with the numbers base, base + 1 and so on, added
up. A number at which the data have no tree counts 0. -/
def widths (D : WholeD) (base n : Nat) : Nat :=
  ((List.range n).map fun i => ((D.shape (base + i)).map (·.W)).getD 0).sum

section Data
variable {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}

/-- The words of all oracle messages of chain number c, from 0, add up to the widths of as many
trees of the data, from the chain's first tree on. -/
theorem told_sum (h : F.data file = .ok D) (hp : F.planOk = true) (c : Nat) :
    ((Sound.sentAt F c).map (·.2)).sum =
      widths D (baseOf D.t₁ D.t₂ c) (Sound.sentAt F c).length := by
  have ht := toldShape Xi F file D h (sentFit_of_planOk F hp) c
  unfold widths
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    have hi : i < (Sound.sentAt F c).length := by simpa using h1
    obtain ⟨sh, e1, -, e3⟩ := ht i _ (List.getElem?_eq_getElem hi)
    rw [e1]
    exact e3.symm

theorem entries_of : ∀ {ds : List RDT} {l : List Fmt.DeclaredRound}, List.Forall₂ RoundAsG ds l →
    l.map (·.entry.roots) = ds.map (·.entry.roots) ∧
      l.map (·.entry.roots) = ds.map (·.trees.length)
  | _, _, .nil => ⟨rfl, rfl⟩
  | _, _, .cons h t => by
    obtain ⟨i1, i2⟩ := entries_of t
    exact ⟨by rw [List.map_cons, List.map_cons, i1, h.1],
      by rw [List.map_cons, List.map_cons, i2, h.2.2.2.1]⟩

/-- The declared rounds of the shared and of the second chain send as many roots as the data's
entries say. -/
theorem roots_later (h : F.data file = .ok D) :
    F.roundsDeclaredByBlocks.2.1.map (·.entry.roots) = D.ds₂.map (·.entry.roots) ∧
      F.roundsDeclaredByBlocks.2.2.map (·.entry.roots) = D.ds₃.map (·.entry.roots) := by
  obtain ⟨-, a₂, a₃⟩ := roundsOfData F file D h
  exact ⟨(entries_of a₂).1, (entries_of a₃).1⟩

/-- The same for the first chain: the data leave its last declared round out, and that round sends
no root. -/
theorem roots_first (h : F.data file = .ok D) (hne : F.roundsDeclaredByBlocks.1 ≠ []) :
    F.roundsDeclaredByBlocks.1.map (·.entry.roots) = D.ds₁.map (·.entry.roots) ++ [0] := by
  obtain ⟨a₁, -, -⟩ := roundsOfData F file D h
  obtain ⟨e1, e2⟩ := entries_of a₁
  have ht : D.t₁ = F.t₁ := (counts_of_data h).1
  have hd : F.roundsDeclaredByBlocks.1 = F.roundsDeclaredByBlocks.1.dropLast ++ [F.roundsDeclaredByBlocks.1.getLast hne] :=
    (List.dropLast_append_getLast hne).symm
  have hs : F.t₁ = (F.roundsDeclaredByBlocks.1.dropLast.map (·.entry.roots)).sum +
      (F.roundsDeclaredByBlocks.1.getLast hne).entry.roots := by
    show (F.roundsDeclaredByBlocks.1.map (·.entry.roots)).sum = _
    conv_lhs => rw [hd]
    simp
  have h0 : (F.roundsDeclaredByBlocks.1.getLast hne).entry.roots = 0 := by
    have : D.t₁ = (F.roundsDeclaredByBlocks.1.dropLast.map (·.entry.roots)).sum := by rw [e2]; rfl
    omega
  conv_lhs => rw [hd]
  rw [List.map_append, e1, List.map_cons, List.map_nil, h0]

end Data

/-! ## 5 The same test on short lists, for evaluation in Lean's kernel -/

/-- Walks the rounds' data, numbered from i. A round whose entry has no root and which has no tree
is passed over. Every other round must be the next element of T: the round's number, and the widths
of its trees. At the end T must be used up. -/
def sendersAre : Nat → List RDT → List (Nat × List Nat) → Bool
  | _, [], [] => true
  | _, [], _ :: _ => false
  | i, d :: ds, T =>
    if d.entry.roots == 0 && d.trees.isEmpty then sendersAre (i + 1) ds T
    else
      match T with
      | [] => false
      | t :: T' => (t.1 == i && d.trees.map (·.W) == t.2) && sendersAre (i + 1) ds T'

/-- Where the walk passes: every round whose entry has a root has its number in T, and the widths of
all trees, in order, are the widths in T, in order. -/
theorem senders_spec : ∀ (i : Nat) (ds : List RDT) (T : List (Nat × List Nat)),
    sendersAre i ds T = true →
      (∀ j v, (ds.map (·.entry.roots))[j]? = some v → v ≠ 0 → i + j ∈ T.map (·.1)) ∧
        (ds.flatMap (·.trees)).map (·.W) = T.flatMap (·.2)
  | _, [], [], _ => ⟨fun j v h => by simp at h, rfl⟩
  | _, [], _ :: _, h => by cases h
  | i, d :: ds, T, h => by
    unfold sendersAre at h
    split at h
    · rename_i h0
      rw [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h0
      obtain ⟨a, b⟩ := senders_spec (i + 1) ds T h
      refine ⟨fun j v hj hv => ?_, ?_⟩
      · cases j with
        | zero =>
          rw [List.map_cons, List.getElem?_cons_zero] at hj
          exact absurd ((Option.some.inj hj).symm.trans h0.1) hv
        | succ j =>
          rw [List.map_cons, List.getElem?_cons_succ] at hj
          have := a j v hj hv
          rwa [Nat.add_assoc, Nat.add_comm 1 j] at this
      · rw [List.flatMap_cons, h0.2, List.nil_append]
        exact b
    · cases T with
      | nil => cases h
      | cons t T' =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        obtain ⟨a, b⟩ := senders_spec (i + 1) ds T' h3
        refine ⟨fun j v hj hv => ?_, ?_⟩
        · rw [List.map_cons]
          cases j with
          | zero => exact List.mem_cons.2 (Or.inl h1.symm)
          | succ j =>
            rw [List.map_cons, List.getElem?_cons_succ] at hj
            have := a j v hj hv
            rw [Nat.add_assoc, Nat.add_comm 1 j] at this
            exact List.mem_cons_of_mem _ this
        · rw [List.flatMap_cons, List.map_append, h2, b, List.flatMap_cons]

/-- The test on numbers, on short lists. s: how many rounds come before the rows. idx: the numbers
of the rounds that send a root. At every row: no element of idx is the number of one of the row's
rounds, or W ≤ f + 3 e at the row's place. -/
def thirdThin (idx : List Nat) (W : Nat) (l : List (Addr × Due)) :
    Nat → List (Place × Nat) → Bool
  | _, [] => true
  | s, r :: rows =>
    ((idx.all fun i => !(decide (s ≤ i) && decide (i < s + r.2))) ||
      decide (W ≤ (placeDue l r.1).f + 3 * (placeDue l r.1).e)) && thirdThin idx W l (s + r.2) rows

theorem check_of_thin (idx : List Nat) (W : Nat) (l : List (Addr × Due)) :
    ∀ (rows : List (Place × Nat)) (s : Nat) (es : List Nat), thirdThin idx W l s rows = true →
      (∀ j v, es[j]? = some v → v ≠ 0 → s + j ∈ idx) → thirdCheck rows es W l = true
  | [], _, _, _, _ => rfl
  | r :: rows, s, es, h, he => by
    unfold thirdThin at h
    rw [Bool.and_eq_true] at h
    have ih := check_of_thin idx W l rows (s + r.2) (es.drop r.2) h.2 fun j v hj hv => by
      rw [List.getElem?_drop] at hj
      have := he _ v hj hv
      rwa [← Nat.add_assoc] at this
    unfold thirdCheck at ih ⊢
    show (((es.take r.2).all (· == 0) || _) && (alongN rows (es.drop r.2)).all _) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, ih⟩
    rcases Bool.or_eq_true_iff.1 h.1 with h1 | h1
    · rw [Bool.or_eq_true_iff]
      left
      rw [List.all_eq_true]
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      rw [beq_iff_eq]
      by_contra hne
      have hjn : j < r.2 := by
        have := hj
        rw [List.length_take] at this
        omega
      have hg : es[j]? = some (es.take r.2)[j] := by
        rw [List.getElem_take]
        exact List.getElem?_eq_getElem _
      have hm := List.all_eq_true.1 h1 _ (he j _ hg hne)
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hm
      omega
    · rw [Bool.or_eq_true_iff]
      exact Or.inr h1

/-- The hypothesis of `check_of_thin` on es also holds of es with a 0 appended: a last round that
sends no root changes nothing. -/
theorem with_zero {es : List Nat} {idx : List Nat} {s : Nat}
    (h : ∀ j v, es[j]? = some v → v ≠ 0 → s + j ∈ idx) :
    ∀ j v, (es ++ [0])[j]? = some v → v ≠ 0 → s + j ∈ idx := by
  intro j v hj hv
  by_cases hl : j < es.length
  · rw [List.getElem?_append_left hl] at hj
    exact h j v hj hv
  · rw [List.getElem?_append_right (by omega)] at hj
    cases hk : j - es.length with
    | zero =>
      rw [hk, List.getElem?_cons_zero] at hj
      exact absurd (Option.some.inj hj).symm hv
    | succ k =>
      rw [hk] at hj
      simp at hj

/-! ## 6 The widths, chain by chain -/

theorem treeSh_flat : ∀ (ds : List RDT) (n : Nat),
    OnBytes.Maker.treeShT ds n = (ds.flatMap (·.trees))[n]?
  | [], _ => rfl
  | d :: ds, n => by
    rw [OnBytes.Maker.treeShT_cons, List.flatMap_cons]
    split
    · rename_i h
      rw [List.getElem?_append_left h]
    · rename_i h
      rw [List.getElem?_append_right (by omega), treeSh_flat ds]

theorem sum_lengths (ds : List RDT) :
    (ds.map (·.trees.length)).sum = (ds.flatMap (·.trees)).length := by
  rw [List.length_flatMap]

theorem sum_getD {α : Type} (g : α → Nat) (l : List α) :
    ((List.range l.length).map fun i => (l[i]?.map g).getD 0).sum = (l.map g).sum := by
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi]
    rfl

/-- For each chain: the widths of its trees, added up by their numbers in the data (`widths`), are
the sum of the widths of the trees in the chain's own list of rounds. -/
theorem widths_chains (D : WholeD) :
    widths D (baseOf D.t₁ D.t₂ 0) D.t₁ = ((D.ds₁.flatMap (·.trees)).map (·.W)).sum ∧
      widths D (baseOf D.t₁ D.t₂ 1) D.t₂ = ((D.ds₂.flatMap (·.trees)).map (·.W)).sum ∧
      widths D (baseOf D.t₁ D.t₂ 2) (D.ds₃.map (·.trees.length)).sum =
        ((D.ds₃.flatMap (·.trees)).map (·.W)).sum := by
  have t1 : D.t₁ = (D.ds₁.flatMap (·.trees)).length := sum_lengths _
  have t2 : D.t₂ = (D.ds₂.flatMap (·.trees)).length := sum_lengths _
  have b0 : baseOf D.t₁ D.t₂ 0 = 0 := rfl
  have b1 : baseOf D.t₁ D.t₂ 1 = D.t₁ := rfl
  have b2 : baseOf D.t₁ D.t₂ 2 = D.t₁ + D.t₂ := rfl
  rw [b0, b1, b2]
  refine ⟨?_, ?_, ?_⟩
  · rw [← sum_getD (fun s : Fmt.Shape => s.W) (D.ds₁.flatMap (·.trees)), ← t1]
    unfold widths
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' : i < D.t₁ := List.mem_range.1 hi
    have : D.shape (0 + i) = (D.ds₁.flatMap (·.trees))[i]? := by
      unfold WholeD.shape
      rw [Nat.zero_add, if_pos hi', treeSh_flat]
    rw [this]
  · rw [← sum_getD (fun s : Fmt.Shape => s.W) (D.ds₂.flatMap (·.trees)), ← t2]
    unfold widths
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hi' : i < D.t₂ := List.mem_range.1 hi
    have : D.shape (D.t₁ + i) = (D.ds₂.flatMap (·.trees))[i]? := by
      unfold WholeD.shape
      rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hi', treeSh_flat]
    rw [this]
  · rw [sum_lengths, ← sum_getD (fun s : Fmt.Shape => s.W) (D.ds₃.flatMap (·.trees))]
    unfold widths
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    have : D.shape (D.t₁ + D.t₂ + i) = (D.ds₃.flatMap (·.trees))[i]? := by
      have e : D.t₁ + D.t₂ + i - D.t₁ - D.t₂ = i := by omega
      unfold WholeD.shape
      rw [if_neg (by omega), if_neg (by omega), e, treeSh_flat]
    rw [this]

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.mask_le_words
#print axioms AtPublicFiles.KeyBook.mask_zero
#print axioms AtPublicFiles.KeyBook.sent_length
#print axioms AtPublicFiles.KeyBook.along_rounds
#print axioms AtPublicFiles.KeyBook.masksOk_of
#print axioms AtPublicFiles.KeyBook.told_sum
#print axioms AtPublicFiles.KeyBook.roots_later
#print axioms AtPublicFiles.KeyBook.roots_first
#print axioms AtPublicFiles.KeyBook.senders_spec
#print axioms AtPublicFiles.KeyBook.check_of_thin
#print axioms AtPublicFiles.KeyBook.widths_chains
#print axioms AtPublicFiles.KeyBook.sum_flatMap
#print axioms AtPublicFiles.KeyBook.le_sum_of_mem
#print axioms AtPublicFiles.KeyBook.mem_zip_right
#print axioms AtPublicFiles.KeyBook.map_of_zip
#print axioms AtPublicFiles.KeyBook.wordsOf
#print axioms AtPublicFiles.KeyBook.shaped_parts
#print axioms AtPublicFiles.KeyBook.maskWords_eq
#print axioms AtPublicFiles.KeyBook.oracles_count
#print axioms AtPublicFiles.KeyBook.shaped_of
#print axioms AtPublicFiles.KeyBook.sent_words
#print axioms AtPublicFiles.KeyBook.alongN
#print axioms AtPublicFiles.KeyBook.thirdCheck
#print axioms AtPublicFiles.KeyBook.widths
#print axioms AtPublicFiles.KeyBook.entries_of
#print axioms AtPublicFiles.KeyBook.sendersAre
#print axioms AtPublicFiles.KeyBook.thirdThin
#print axioms AtPublicFiles.KeyBook.with_zero
#print axioms AtPublicFiles.KeyBook.treeSh_flat
#print axioms AtPublicFiles.KeyBook.sum_lengths
#print axioms AtPublicFiles.KeyBook.sum_getD
