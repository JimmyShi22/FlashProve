-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/RowAt.lean: what the first chain's table of joints says at the 25 closings of a
segment (kind K10), at the full size: which items the closing's row owes, which it asks, and that what it asks is open
before it. First on the library's two written lists, `P5J.At.links` (the 25 segments' sorts) and `P5J.At.ps` (the
chain's 358 places) (Johnson/P5J/LettersAt.lean); then at the first chain's thread under the library's head.
No definition; one local notation.

The words. The table (Johnson/Desc/First/Borders.lean) gives each sub-protocol a row of items. Read forward
(Honest/Thread/FirstRows.lean) a row has three lists: what it asks (these items hold before the sub-protocol), what it
owes (these have to be proved after it) and what it shuts (these are open before it and not after it). Border b is the
position in the chain before sub-protocol number b; `fwdOpen` (Honest/Thread/Thr.lean) computes the list of items that
are open there. The closing of segment l is sub-protocol number 14 l + `IM.nAt l` + 5, where `IM.nAt l` is 9 at l = 24
and 7 elsewhere (Johnson/IMR/WrittenList.lean). A thread is the structure of parameters of one chain's invariant
(`Thread`, `Thr`: Honest/Thread/Thr.lean). The head is the library's hypothesis `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean), here at the older hash; the head's thread is the field `thread` of `lettersHead` at its
parameters (Honest/Thread/FirstHead.lean).

On the written lists. Both lists are closed terms: they have no variable, so a statement on them can be evaluated.
  `one_pass_full`   the test in one pass of Honest/Thread/FirstFits.lean says yes: along all 358 places, whatever a
      forward row asks or shuts is open before it. It is, to the letter, the premise hone of `fits_head`
      (Honest/Thread/FitsHead.lean)
  `owes_all`, `asks_all`   at each l in `List.range 25`: the row at the closing's number owes `carry l` and
      `pinKept l`, in this order, and nothing else; it asks `rowsOf l ++ pinsOf l`
  `owes_at`, `asks_at`   the same at each l < 25
  `front_open`   at each l < 25 every item of `rowsOf l ++ pinsOf l` is open at the border before the closing: from
      `one_pass_full` and `asks_at`, by `asks_open` (Honest/Thread/FirstFits.lean)
So the segment that the table's row names at the closing's number is l itself.

What `decide +kernel` is. The first three are proved by this tactic. It takes the decision procedure that Lean finds
for the statement (here: comparing finite lists of items, or a test's value with true) and hands Lean's kernel the
proof "this procedure evaluates to true"; the kernel evaluates it by its own rules of computation while it checks the
proof, as it checks any other. No compiled code is trusted, and the tactic adds no axiom; that sets it apart from
the variant that runs compiled code, which is not used. The lines `#print axioms` at the file's end list what each result depends on.
`one_pass_full` is one walk along the 358 places; the two others look up 25 places.

At the head's thread.
  `thread_opened`, `thread_row`   its open sets and its rows are those of the two written lists: by unfolding
  `owes_at_head`, `front_open_at_head`   `owes_at` and `front_open` there
  `exchange_owes_at`   at one l < 25: hc and hp are `ExchangeAtS` (Honest/Thread/SharesS.lean) at the closing's
      number, at `carry l` and at `pinKept l`; the conclusion is `ExchangeAtS` there at every item that the row owes.
      This is the form of the premise hX of `owesS_head` (Honest/Thread/GatherHead.lean) at that number
  `exchange_of_two`   the same at all l < 25, with one more hypothesis in front of the conclusion: if the item is open
      before the closing, it is no `pin`, not `pinI`, not `pinW`, and no `constr` at one of the four parts of
      `P5J.parts4`. It is stated so for a caller whose premise has that hypothesis; no such caller is imported here.
      The hypothesis is not used

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out in the notation's own line.
It declares no new name, neither a definition nor a theorem: each use is that text, elaborated anew. A field of it is
written with brackets, `(𝕋).row`: without them Lean reads `𝕋.row` as one name. When a notation is declared, Lean
looks through its text for names that are not bound, and that early look has no case for a field access.
`set_option quotPrecheck false in` turns that one look off for the one command behind it; it loosens nothing in what
Lean checks of a theorem.

Limits. Lists alone: nothing is said on what an item says. The full size alone. The first part has no premise. In the
second part the head h occurs in the thread's own text only: no field of it is used. The prover H, the book Bk and the
further parameters of `lettersHead` (Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) are variables of every
statement there, and so is Said. hc and hp, the two premises of `exchange_owes_at` and `exchange_of_two`, are shown in
this file of no thread. `ExchangeAtS` is a definition, meant as a hypothesis; where the invariant holds at no state of
a border it holds there for nothing. It is not shown that the invariant holds in any run. No property of the protocol
is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (Item start rowsOf pinsOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## On the written lists -/

/-- Along the 358 written places, whatever a forward row asks or shuts is open before it. -/
theorem one_pass_full :
    (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all fun x =>
      ((FirstRows.rowAt P5J.At.links x.2).asks ++ (FirstRows.rowAt P5J.At.links x.2).shuts).all
        x.1.contains) = true := by
  decide +kernel

/-- At each of the 25 closings' numbers the forward row owes the segment's carry and its kept pins, and nothing else. -/
theorem owes_all : ∀ l ∈ List.range 25,
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).owes =
      [Item.carry l, Item.pinKept l] := by
  decide +kernel

/-- At each of the 25 closings' numbers the forward row asks the segment's rows and its three pins. -/
theorem asks_all : ∀ l ∈ List.range 25,
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).asks = rowsOf l ++ pinsOf l := by
  decide +kernel

/-- **The row at the closing of segment l, for l < 25, owes `carry l` and `pinKept l` and nothing else.** -/
theorem owes_at (l : Nat) (hl : l < 25) :
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).owes =
      [Item.carry l, Item.pinKept l] :=
  owes_all l (List.mem_range.2 hl)

/-- The row at the closing of segment l, for l < 25, asks the segment's rows and its three pins. -/
theorem asks_at (l : Nat) (hl : l < 25) :
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).asks = rowsOf l ++ pinsOf l :=
  asks_all l (List.mem_range.2 hl)

/-- **The segment's rows and its three pins are open at the border before its closing.** -/
theorem front_open (l : Nat) (hl : l < 25) : ∀ j ∈ rowsOf l ++ pinsOf l,
    j ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (14 * l + IM.nAt l + 5) := by
  intro j hj
  have ha : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).asks := by
    rw [asks_at l hl]
    exact hj
  have h := FirstRows.asks_open P5J.At.links P5J.At.ps (start P5J.At.links) one_pass_full
    (14 * l + IM.nAt l + 5)
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h j (List.mem_append_left _ ha))

/-! ## At the head's thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notation, and the
-- option in front of it".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- The thread's open set at a border is the forward open set of the two written lists. -/
theorem thread_opened (b : Nat) :
    (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b =
      fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) b := rfl

/-- The thread's row at a number is the forward row of the two written lists. -/
theorem thread_row (b : Nat) :
    (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b =
      FirstRows.rows P5J.At.links P5J.At.ps b := rfl

/-- The thread's row at the closing of segment l, for l < 25, owes `carry l` and `pinKept l` and nothing else. -/
theorem owes_at_head (l : Nat) (hl : l < 25) :
    ((𝕋).row (14 * l + IM.nAt l + 5)).owes = [Item.carry l, Item.pinKept l] := by
  rw [thread_row h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w]
  exact owes_at l hl

/-- The segment's rows and its three pins are open at the thread's border before its closing. -/
theorem front_open_at_head (l : Nat) (hl : l < 25) : ∀ j ∈ rowsOf l ++ pinsOf l,
    j ∈ (𝕋).opened (14 * l + IM.nAt l + 5) := by
  intro j hj
  rw [thread_opened h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w]
  exact front_open l hl j hj

/-- **At one closing, `ExchangeAtS` at `carry l` and at `pinKept l` gives `ExchangeAtS` at every item that the row
owes.** -/
theorem exchange_owes_at (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (hl : l < 25)
    (hc : ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) (Item.carry l))
    (hp : ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) (Item.pinKept l)) :
    ∀ j : Item, j ∈ ((𝕋).row (14 * l + IM.nAt l + 5)).owes →
      ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) j := by
  intro j hj
  rw [owes_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl] at hj
  rcases List.mem_cons.1 hj with e | hj'
  · rw [e]
    exact hc
  · rw [List.mem_singleton.1 hj']
    exact hp

/-- **The same at all 25 closings, with one more hypothesis on an item that is open before the closing**, which is not
used. -/
theorem exchange_of_two (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hc : ∀ l, l < 25 → ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) (Item.carry l))
    (hp : ∀ l, l < 25 → ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) (Item.pinKept l)) :
    ∀ l, l < 25 → ∀ j : Item, j ∈ ((𝕋).row (14 * l + IM.nAt l + 5)).owes →
      (j ∈ (𝕋).opened (14 * l + IM.nAt l + 5) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) j :=
  fun l hl j hj _ =>
    exchange_owes_at h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Said l hl (hc l hl) (hp l hl) j hj

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.one_pass_full
#print axioms ProofFile.Honest.K10.owes_all
#print axioms ProofFile.Honest.K10.asks_all
#print axioms ProofFile.Honest.K10.owes_at
#print axioms ProofFile.Honest.K10.asks_at
#print axioms ProofFile.Honest.K10.front_open
#print axioms ProofFile.Honest.K10.thread_opened
#print axioms ProofFile.Honest.K10.thread_row
#print axioms ProofFile.Honest.K10.owes_at_head
#print axioms ProofFile.Honest.K10.front_open_at_head
#print axioms ProofFile.Honest.K10.exchange_owes_at
#print axioms ProofFile.Honest.K10.exchange_of_two
