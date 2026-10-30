-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ReadOwn.lean: the kind "the code switch" (K2): OF THE TREES
THAT THE SWITCH INTO A LATER GROUP OPENS, THE ONE THAT THE SWITCH IN FRONT HAS SENT IS STATED WITH
THAT SWITCH's OWN DEPTH AND WIDTH: under the library's head and the opening, at the switches into
the groups 2 to 23. A PUBLIC FACT ON THE PLAN's NUMBERS. One definition, a closed test with code;
four statements with their proofs.

  `readOwnB`            the test, at the written plan; shift: 0 is the test, another number a
                        control
  `readOwnW`            its yes: A CLOSED FACT BY LEAN's KERNEL
  `readOwnW_can_fail`   the control: with every width raised by one it says no
  `link_read_own`       THE LAW UNDER THE HEAD
  `link_read_table`     so the table that the switch in front sends, as a term, has the stated width

WHAT THE TEST ASKS, at each m < 22, of the numbers n' of the switch into group m + 1 and n of the
switch into group m + 2: n' has a root; each own tree of n' (the number of oracle messages told in
front of that switch's member, and j) stands ONCE in n's list `read`; and where it stands, its depth
and width are those of the j-th oracle message that n' states (`P1K2.oraclesAt`,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean). THE CONTROL IS OF THE WIDTH's CLAUSE ALONE: of the depth,
of "once" and of "a root" there is none.

Why: "it plays" at a switch asks that each tree which its second round opens has, as the thread's
table, the width that the numbers state. For the tree that the switch in front has sent,
`switchTable_at_plan` (Honest/K2/Law/TableWords.lean) has the table's width as that switch's own
stated oracle message's; this file ties that to the later switch's list. `link_read_table` is the
two in a row: on the table AS A TERM, free of any thread. That the thread's table at that tree IS
this term is not here.

By: `numsW`, `numsW_at_head`, `treesTo_at_head` (Honest/K2/Law/PublicAtWritten.lean,
PublicAtHead.lean, PlacesWritten.lean) · `switchTable_at_plan`. Near: `opensW`
(Honest/K2/Law/PublicAtWritten.lean): of the same trees, that they are told in front of the switch.

Limits. A CLOSED FACT BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. THE FULL SIZE AND THE
FORMAT's EARLIER HASH ALONE. THE OTHER TREES THAT A SWITCH OPENS ARE OTHER KINDS' SENDINGS: nothing
on them; nothing at the switch into group 1, which opens no switch's tree, at the head's switch or
the last. On numbers and a table's shape: nothing on what a table holds. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.TableWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open P1K2 (Prep Nums numsAt prepOf oraclesAt)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The test**, at the written plan. shift: 0 is the test; another number is a control. -/
def readOwnB (shift : Nat) : Bool :=
  (List.range 22).all fun i =>
    (numsW (some (i + 1))).any fun n' => (numsW (some (i + 2))).any fun n =>
      decide (0 < n'.roots) && (List.range n'.roots).all fun j =>
        (n.read.filter fun t => t.1 == treesTold toldFull (14 * (i + 1) + 2) + j).length == 1 &&
        n.read.all fun t => t.1 != treesTold toldFull (14 * (i + 1) + 2) + j ||
          ((oraclesAt n'.grp n'.codes n'.sent)[j]?).any fun o =>
            o.words + shift == t.2.2 && o.logLength == t.2.1

set_option maxRecDepth 1000000 in
theorem readOwnW : readOwnB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem readOwnW_can_fail : readOwnB 1 = false := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **THE LAW UNDER THE HEAD.** n': the numbers of the switch into group i + 1; n: of the switch
into group i + 2; t: a tree that the latter opens; j: its number among the former's own. -/
theorem link_read_own (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (hi : i < 22) {Pp : Prep} {n' n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn' : numsAt Pp (some (i + 1)) = some n') (hn : numsAt Pp (some (i + 2)) = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {j : Nat} (hj : j < n'.roots)
    (e : t.1 = treesTo cF.blocksInOrder (14 * (i + 1) + 2) + j) :
    ∃ o, (oraclesAt n'.grp n'.codes n'.sent)[j]? = some o ∧ o.words = t.2.2 ∧
      o.logLength = t.2.1 := by
  have w := List.all_eq_true.1 readOwnW i (List.mem_range.2 hi)
  rw [numsW_at_head h O hP, numsW_at_head h O hP, hn', hn] at w
  simp only [Option.any_some, Bool.and_eq_true] at w
  have w1 := List.all_eq_true.1 w.2 j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true] at w1
  have w2 := List.all_eq_true.1 w1.2 t ht
  simp only [Bool.or_eq_true] at w2
  rw [treesTo_at_head h O] at e
  rcases w2 with a | a
  · exact absurd e (bne_iff_ne.1 a)
  · cases ho : (oraclesAt n'.grp n'.codes n'.sent)[j]? with
    | none =>
      rw [ho] at a
      cases a
    | some o =>
      rw [ho] at a
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at a
      exact ⟨o, rfl, a.1, a.2⟩

/-- **The table that the switch in front sends, as a term, has the width that the later switch's
numbers state for it.** p': the member of `switchPlaces` at the switch in front. Left as premises:
the book lends the part its coins; `closingOk`; `publicOk` at the input's public instance. -/
theorem link_read_table {W₀ Rc Xi Tr : Type} (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {i : Nat} (hi : i < 22) {Pp : Prep} {n' n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn' : numsAt Pp (some (i + 1)) = some n') (hn : numsAt Pp (some (i + 2)) = some n)
    {t : Nat × Nat × Nat} (ht : t ∈ n.read) {j : Nat} (hj : j < n'.roots)
    (e : t.1 = treesTo cF.blocksInOrder (14 * (i + 1) + 2) + j)
    {p' : SwitchPlace} (hp' : p' ∈ switchPlaces Zp Bs.G₀) (hl : p'.place.link = some (i + 1))
    (Bk : ProverCoinCounts) (chain : Nat) (Dt : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (c₀ : SwitchCoins p'.sizes p'.others p'.foldVars p'.carries)
    (hc : lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p'.place, 0⟩
      (switchPart (coreSender freshTable) p'.sizes p'.others p'.foldVars p'.carries) = .ok c₀)
    (hcl : closingOk freshTable (segs.take p'.link) p' = true)
    (hv : publicOk Dt lay p' (segs.take p'.link) w.x = true) :
    (switchTableAt Bk chain (coreSender freshTable) Dt readers (lotClosingAt lay segs) p' k w hd
      j).words = t.2.2 := by
  obtain ⟨o, ho, e1, -⟩ := link_read_own h O hi hP hn' hn ht hj e
  have s := switchTable_at_plan hP hp' (by rw [hl]; exact hn') Bk chain Dt readers lay segs k w hd
    c₀ hc (serves_at_head h O p' hp') (roomy_at_head h O p' hp') (fits_at_head h O p' hp') hcl hv j
    o ho
  exact (congrArg Prod.snd s).trans e1

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.readOwnW
#print axioms ProofFile.Honest.K2.Law.readOwnW_can_fail
#print axioms ProofFile.Honest.K2.Law.link_read_own
#print axioms ProofFile.Honest.K2.Law.link_read_table
