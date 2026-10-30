-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudOwn.lean: the letter `bud` of Sim/ExactPlan.lean
(`budOpened`) holds at the list that a session of the frame makes for a proximity test's second part
(`asksFrom`, Johnson/Desc/ProofFile/Honest/Law/Rule/Session.lean), where the positions read of a
tree are those that the test's own declared rounds read. On positions alone. No property is claimed.
General in the job J, the declared rounds decls, the numbers chain, firstTree and sent, the
arguments stored and tree of `readsOf`, and the challenges ds₁ and ds, under the hypotheses listed
below. Statements and proofs.

Terms. …/K12/ is Johnson/Desc/ProofFile/Honest/K12/, Sim/ is a folder in it, and …/Law/ is the
folder Law/ next to K12/. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean, with Side.lean next
to it. A part (`Part`, Frame.lean) is the prover's side of some rounds in a row. A member (`Member`,
Side.lean) is a part with its number, its declared rounds and a term of type `Sim`. A job J
(`TestJob`, …/K12/Test.lean) is what a caller supplies for its proximity test; `J.p.nums.stages` is
the test's list of stages. `J.laid` has the test's declared rounds, each with its oracle messages; a
round has one root for each of these messages. The first part has the test's first `firstLen` rounds
(…/K12/Parts.lean), the second part all the others. A tree is a table that a round of a chain sends
as an oracle message; a chain's trees are numbered from 0. The term is `testAll` (…/K12/Test.lean),
the function that computes the test's rounds. `depthAt J r` (same file) gives the depth of the tree
that round r sends, if it sends one, and `sentBefore J r` (…/K12/SentTables.lean) counts the rounds
before r at which `depthAt` gives a depth. `readsOf` (Frame.lean) lists what declared rounds read at
given challenges; chain is the chain's number. A letter is a free parameter. `bud` is a parameter of
the frame's structure `Good` (Side.lean): for each part, by its number, which positions may be read
at given challenges. Sim/ExactPlan.lean puts `budOpened` in its place: at the number 1, every
position that a list has at a round's root number 0 is among those that the next reading round
samples (`openedTr`, Sim/CoreText.lean); at every other number it asks nothing. A session is the
function `session` of …/Law/Rule/Session.lean; it builds each part's list of positions by `asksFrom`
(in `cutRow`). `asksFrom f roots n` lists, by round and by root, what the function f gives at the
trees' numbers from n on; roots has each round's number of roots. In "Limits": the function "tree"
is the first argument of `asksFrom`, not the theorems' parameter tree, which is an argument of
`readsOf`; the file's whole plan is the description of all the rounds of the three chains
(`FileDescription`); in "No member is given by name", a member is a choice of values at which the
hypotheses hold together.

  `bud_own`: the statement: `budOpened J.p.nums.stages 1 ds` at the list
    `asksFrom f roots (sent + sentBefore J (firstLen J.p.nums.stages))`. Here f m has the positions
    of those reads in `readsOf chain firstTree stored tree decls (ds₁ ++ ds)` whose source is the
    chain's tree number m, and roots is a free parameter, under the hypothesis hroots
  `bud_own_rest`: the same at the second member `restMember J Js` (Sim/Row.lean): at its number,
    which is 1, and with its rounds' numbers of roots for roots. `tablesFitB J = true` takes the
    place of hroots. The member's number and rounds do not depend on Js (`SimJob`, Sim/Sims.lean)
  `sent_sum`: where each entry of roots is 1 if `depthAt` gives a depth at its round and 0 if not,
    the first i entries add up to the number of trees that these i rounds send:
    `sentBefore J a + (roots.take i).sum = sentBefore J (a + i)`
  `roots_fit`: where the public test `tablesFitB` (…/K12/FitsAll.lean) passes, a declared round has
    one root if `depthAt` gives a depth at its number, and none if not
  `sentBefore_succ`, `sum_take_succ`: one step of each count: `sentBefore J (r + 1)` is
    `sentBefore J r`, and one more if `depthAt` gives a depth at r; the first i + 1 entries of a
    list of numbers add up to the sum of the first i and entry number i

By what. `bud_of_asksFrom` (Sim/BudRun.lean) brings `budOpened` at a list of `asksFrom` down to one
clause for each round that has a root: all that f gives at the number of the tree that the round
sends is in `openedTr` at that round. `own_reads_tr` (Sim/OpensTr.lean) proves that clause for the
reads of decls. `openedTr_congr` (Sim/ExactPlan.lean) shows that `openedTr` there is the same at the
challenges `ds₁ ++ ds`, by number, and at `laterOf J.p.nums.stages ds`. The rest is counting: the
rounds' numbers of roots against the number of trees sent before a round.

Hypotheses of `bud_own`.
  F: `OpensFit J decls depths src₀ sent` (…/K12/ColsTerm.lean): the openings that the rounds decls
    declare are the term's (`opensTest`, same file), and these rounds read no stored table. depths
    and src₀ are free parameters: the depths and the stated sources, by the number k, of the trees
    that `opensTest` lists as `From.old k` (…/K12/TermOpens.lean: the job's tree number k). sent:
    meant for how many trees the chain has sent before the test; a free parameter too: that it is
    that number is not stated
  hst: the test has two stages or more
  hk: at the first stage s, `s.k = (sgOf s).h + (sgOf s).g`
  hold: if a stated source `src₀ k`, k below `depths.length`, is a tree of this chain, its number is
    below sent
  h1: ds₁ has `firstLen J.p.nums.stages` challenges
  hroots: entry number i of roots is 1 if `depthAt` gives a depth at the round
    `firstLen J.p.nums.stages + i`, and 0 if not

Limits.
- The function "tree" here lists what the test's own rounds read. The frame's session takes what all
  rounds of the three chains read (`treeAsks`, …/Law/Rule/Bare.lean): that no round outside the test
  reads a tree that the test sends is the file's whole plan, and is shown nowhere: so this is not
  yet `bud` at a session's list.
- `OpensFit` is a hypothesis; it is proved at the key file's test on the ranges, for the jobs there
  whose first fresh table has come earlier (`opensFit_KR`, …/K12/OpensFitB.lean). That file proves
  `OpensFit` at three values only: this one and two small made-up jobs (`opensFit_toy`,
  `opensFit_came`). At all three `J.fresh` is not `none`: the first fresh table has come earlier.
  Where `J.fresh` is `none`, the first fold sends its own table; for that case the file has one
  `#guard` on its test `opensFitB` only: an evaluation by Lean's evaluator, outside the kernel,
  which leaves no theorem. So in that case no theorem there gives a value that meets F, though
  `bud_own` and `bud_own_rest` are stated in both cases. At that `#guard`'s values (the depths
  [5, 4, 4], the sources `own 0`, `own 1`, `own 2`, and 2 for sent) hold is false, by reading: the
  source `own 2` is the chain's tree number 2, and 2 is not below sent.
- That no tree before the test has the number of a tree that the test sends is a hypothesis too
  (hold).
- Only `OpensFit` ties decls to the job.
- No member is given by name.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.OpensTr
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (oNext)

variable {V W X Pb : Type}

/-! ## 1 Counting -/

theorem sentBefore_succ (J : TestJob W X) (r : ℕ) :
    sentBefore J (r + 1) = sentBefore J r + if (depthAt J r).isSome = true then 1 else 0 := by
  unfold sentBefore
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : (depthAt J r).isSome <;> simp [h]

theorem sum_take_succ (l : List ℕ) (i : ℕ) (h : i < l.length) :
    (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0 := by
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  simp

/-- Where each entry of roots is 1 if `depthAt` gives a depth at its round and 0 if not (hroots),
the first i entries add up to the number of trees that these i rounds send. a: the number in the
test of the round of the list's first entry. -/
theorem sent_sum (J : TestJob W X) (a : ℕ) (roots : List ℕ)
    (hroots : ∀ i, i < roots.length →
      roots.getD i 0 = if (depthAt J (a + i)).isSome = true then 1 else 0) :
    ∀ i, i ≤ roots.length → sentBefore J a + (roots.take i).sum = sentBefore J (a + i)
  | 0, _ => by simp
  | i + 1, h => by
    rw [sum_take_succ roots i (by omega), hroots i (by omega), ← Nat.add_assoc,
      sent_sum J a roots hroots i (by omega), ← Nat.add_assoc a i 1, sentBefore_succ]

/-- Where `tablesFitB J` passes, a declared round has one root if `depthAt` gives a depth at its
number, and none if not. The rounds are `J.laid` without its first a, so entry number i is the
test's round number a + i. -/
theorem roots_fit (J : TestJob W X) (hT : tablesFitB J = true) (a i : ℕ)
    (hi : i < ((J.laid.drop a).map (·.2.length)).length) :
    ((J.laid.drop a).map (·.2.length)).getD i 0 =
      if (depthAt J (a + i)).isSome = true then 1 else 0 := by
  have hlt : a + i < (laidOf J.p).length := by
    rw [List.length_map, List.length_drop] at hi
    have : J.laid.length = (laidOf J.p).length := rfl
    omega
  have h := eq_of_beq (List.all_eq_true.1 hT (a + i) (List.mem_range.2 hlt))
  have hl := congrArg List.length h
  rw [List.length_map, List.length_map, List.getElem?_eq_getElem hlt] at hl
  rw [List.getD_eq_getElem _ _ hi, List.getElem_map, List.getElem_drop]
  have hl' : (depthAt J (a + i)).toList.length = ((laidOf J.p)[a + i]).2.length := hl
  show ((laidOf J.p)[a + i]).2.length = _
  rw [← hl']
  cases depthAt J (a + i) <;> rfl

/-! ## 2 The statement -/

/-- **`budOpened` at the list that `asksFrom` makes of the test's own reads.** ds₁, ds: the
challenges of the first and of the second part. roots: the second part's rounds' numbers of roots.
The hypotheses are described in the head. -/
theorem bud_own (J : TestJob W X) (decls : List Fmt.DeclaredRound) (depths : List ℕ)
    (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ) (F : OpensFit J decls depths src₀ sent)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) → n < sent)
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table))
    (ds₁ ds : List Fmt.Drawn) (h1 : ds₁.length = firstLen J.p.nums.stages) (roots : List ℕ)
    (hroots : ∀ i, i < roots.length → roots.getD i 0 =
      if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0) :
    budOpened J.p.nums.stages 1 ds
      (asksFrom (fun m => ((readsOf chain firstTree stored tree decls (ds₁ ++ ds)).filter fun q =>
        q.src == some (chain, m)).map (·.pos)) roots
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  refine bud_of_asksFrom _ ds _ roots _ fun i hi q hq => ?_
  have hil : i < roots.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ roots hroots i (Nat.le_of_lt hil)] at hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  obtain ⟨hm, hs⟩ := List.mem_filter.1 hq'
  have h := own_reads_tr J decls depths src₀ sent chain firstTree F s (next :: rest) hst hold stored
    tree (fun n => (ds₁ ++ ds).getD n noDraw) (ds₁ ++ ds)
    (fun n hn => (List.getD_eq_getElem _ _ hn).symm) (firstLen J.p.nums.stages + i) hsome q' hm
    (eq_of_beq hs)
  have hn₀ : firstLen J.p.nums.stages = 2 + s.k := by rw [hst]; rfl
  have e : firstLen J.p.nums.stages + i - 1 = 1 + ((sgOf s).h + (sgOf s).g) + i := by
    rw [hn₀, hk]
    omega
  rw [e] at h
  have hc : openedTr (laterOf J.p.nums.stages ds) (next :: rest) s 1
      (1 + ((sgOf s).h + (sgOf s).g) + i) =
      openedTr (fun n => (ds₁ ++ ds).getD n noDraw) (next :: rest) s 1
        (1 + ((sgOf s).h + (sgOf s).g) + i) :=
    openedTr_congr _ _ (next :: rest) s 1 _ fun n hn => by
      unfold oNext at hn
      show ds.getD (n - firstLen J.p.nums.stages) noDraw = (ds₁ ++ ds).getD n noDraw
      rw [List.getD_append_right _ _ _ _ (by rw [h1, hn₀, hk]; omega), h1]
  have hd : J.p.nums.stages.drop 1 = next :: rest := by rw [hst]; rfl
  have hh : J.p.nums.stages.headD default = s := by rw [hst]; rfl
  rw [hd, hh, hc]
  exact h

/-- **The same at the second member's own rounds.** roots is
`(restMember J Js).rounds.map (·.2.length)`, and `roots_fit` proves hroots from hT. -/
theorem bud_own_rest (J : TestJob W X) (Js : SimJob Pb) (decls : List Fmt.DeclaredRound)
    (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent chain firstTree : ℕ)
    (F : OpensFit J decls depths src₀ sent) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf chain (src₀ k) = (chain, n) → n < sent)
    (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table))
    (ds₁ ds : List Fmt.Drawn) (h1 : ds₁.length = firstLen J.p.nums.stages) :
    budOpened J.p.nums.stages (restMember J Js : Member V W X Pb).number ds
      (asksFrom (fun m => ((readsOf chain firstTree stored tree decls (ds₁ ++ ds)).filter fun q =>
        q.src == some (chain, m)).map (·.pos))
        ((restMember J Js : Member V W X Pb).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) :=
  bud_own J decls depths src₀ sent chain firstTree F s next rest hst hk hold stored tree ds₁ ds h1 _
    fun i hi => roots_fit J hT _ i hi

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.sentBefore_succ
#print axioms ProofFile.Honest.K12.sum_take_succ
#print axioms ProofFile.Honest.K12.sent_sum
#print axioms ProofFile.Honest.K12.roots_fit
#print axioms ProofFile.Honest.K12.bud_own
#print axioms ProofFile.Honest.K12.bud_own_rest
