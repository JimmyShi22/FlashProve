-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WidthsOwn.lean: the kind "the code switch" (K2): THE WIDTH OF
THE THREAD's TABLE, AS THE THREAD READS IT, AT THE ONE TREE THAT A SWITCH OPENS OF THE SWITCH IN
FRONT: FROM THE FRAME's FORM `OwnTreesAt` (Honest/Thread/ScriptLots.lean) AT THAT EARLIER SWITCH.
Two statements with their proofs: joins; no definition.

  `words_of_ownAt`    GENERAL IN THE THREAD AND THE KIND: under `OwnTreesAt`, at a stand of the pair
                      behind the sender, the thread's table has the words of the asker's own table
  `link_width_own`    under the library's head and the opening, general in a thread over the
                      head's chain: the clause of "the widths" at that tree

Why. The first half of "it plays" at a switch (`switch_movedS`, Honest/K2/Law/MovedAtLinks.lean)
asks, at a stand of the pair in front of the member, that each tree which the second round opens
has, as the thread's table read by `Thread.tableAt`, the width that the numbers' list `read` states.
`OwnTreesAt` at an earlier sender is just that form: the table read there shows what the sender's
own table shows (`Table.same`): so it has its words. For a switch's own table the words are had in
Honest/K2/Law/ReadOwn.lean (`link_read_table`).

THE PREMISES OF `link_width_own`, ALL OF THEM. The head, the opening, i < 22, the plan's sizes and
the two switches' numbers, t in the later switch's list `read` at the earlier switch's own tree
number j. ON THE THREAD: its list of sub-protocols is the head's chain's · `OwnTreesAt` at the
earlier switch's member, at the table `switchTableAt` of the kind's one lot's half at p' · a stand
of the pair at a later border. CARRIED ALONG FROM `link_read_table`, AT THE STAND's COINS, ITS INPUT
AND THE LIST OF CHALLENGES AT WHICH THE THREAD READS THE TABLE: the book lends the part its coins ·
`closingOk` at p' · `publicOk` at the input's public instance. THEY ARE ENOUGH; THAT THEY ARE NEEDED
IS NOT SHOWN. By the term's own text (`switchTableAt`, Honest/K2/Seated.lean): where the book does
not lend, or the part's first move refuses, the term is a table without a word, and its width is
then not a stated one that is above 0.

Limits. `OwnTreesAt` IS A PREMISE: NOT SHOWN HERE AT ANY THREAD. ONE TREE OF THE THREE THAT A SWITCH
OPENS: the other two are another kind's sendings. Nothing at the switch into group 1, at the head's
switch or the last. The frame's file beneath is in no sealed library. On a table's width: nothing on
what it holds. Closed facts by Lean's kernel lie beneath, replayed by no independent checker.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ReadOwn
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (OwnTreesAt)

/-- **Under `OwnTreesAt` the thread's table has the words of the asker's own.** -/
theorem words_of_ownAt {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk St Cl V W X Pb}
    {Said : Nat → Coins Bk → Mid W X → Prop} {b₀ r₀ : Nat}
    {tbl : Nat → Coins Bk → W → List Fmt.Drawn → Place × Table}
    (h : OwnTreesAt T Said b₀ r₀ tbl) {j : Nat} (hj : j < r₀) {b : Nat} {k : Coins Bk} {s : St}
    {m : Mid W X} {E : Env} (hb : b₀ < b) (hT : ThrS T Said b k s m E) :
    (T.tableAt (.own (treesTo T.bs b₀ + j)) k m).2.words =
      (tbl j k m.st.input (m.st.heard.take (T.fixed (.own (treesTo T.bs b₀ + j))))).2.words := by
  have e := (h j hj b k s m E hb hT).2
  simp only [Table.same, Bool.and_eq_true, beq_iff_eq] at e
  exact e.1.2

variable {Wp : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **The clause of "the widths" at the tree that the switch in front has sent.** -/
theorem link_width_own {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}
    (h : AtMg OnBytes.secondHashFunction Wp D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (hi : i < 22) {Pp : Prep} {n' n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn' : numsAt Pp (some (i + 1)) = some n') (hn : numsAt Pp (some (i + 2)) = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {j : Nat} (hj : j < n'.roots)
    (e : t.1 = treesTo cF.blocksInOrder (14 * (i + 1) + 2) + j)
    {p' : SwitchPlace} (hp' : p' ∈ switchPlaces Zp Bs.G₀) (hl : p'.place.link = some (i + 1))
    (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (hbs : T.bs = cF.blocksInOrder) (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Dt : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (hO : OwnTreesAt T Said (14 * (i + 1) + 2) n'.roots fun j k w hd =>
      (p'.place, switchTableAt Bk T.chain (coreSender freshTable) Dt readers
        (lotClosingAt lay segs) p' k w hd j))
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hb : 14 * (i + 1) + 2 < b) (hT : ThrS T Said b k s m E)
    (c₀ : SwitchCoins p'.sizes p'.others p'.foldVars p'.carries)
    (hc : lendPart Bk (Bk.rowsOf T.chain) (k.look T.chain) ⟨p'.place, 0⟩
      (switchPart (coreSender freshTable) p'.sizes p'.others p'.foldVars p'.carries) = .ok c₀)
    (hcl : closingOk freshTable (segs.take p'.link) p' = true)
    (hv : publicOk Dt lay p' (segs.take p'.link) m.st.input.x = true) :
    (T.tableAt (.own t.1) k m).2.words = t.2.2 := by
  rw [e, ← hbs]
  refine (words_of_ownAt hO hj hb hT).trans ?_
  exact link_read_table h O hi hP hn' hn ht hj e hp' hl Bk T.chain Dt readers lay segs k
    m.st.input _ c₀ hc hcl hv

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.words_of_ownAt
#print axioms ProofFile.Honest.K2.Law.link_width_own
