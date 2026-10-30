-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/PinKept.lean: `ExchangeAtS` (Honest/Thread/SharesS.lean) is proved at the item
`pinKept l`, at the closing of segment l (kind K10), for each of the 25 segments, at the first chain's thread under
the library's head. The head is the only premise. No definition; one local notation.

The words. A thread is the structure of parameters of one chain's invariant (`Thread`, `Thr`: Honest/Thread/Thr.lean).
The head is the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), here at the older hash; the head's thread
is the field `thread` of `lettersHead` at its parameters (Honest/Thread/FirstHead.lean). Border b is the position in
the chain before sub-protocol number b; the closing of segment l is sub-protocol number 14 l + `IM.nAt l` + 5
(`IM.nAt l` is 9 at l = 24 and 7 elsewhere). `ExchangeAtS T Said b i` says: wherever the invariant with its second
condition Said holds at border b, the challenges fit the sub-protocol's declared rounds, and the sub-protocol has
stepped from state s to state s' (the prover's side has played its rounds, the columns read are filled, and the
verifier's own step has accepted), the item i holds at s', at the run's witness at every continuation of the
challenges. `K10Keeps s s'` (Johnson/Desc/K10/Honest/Keeps.lean) says what an accepted closing leaves and what it
changes of the verifier's state.

What the item says (`Item.holds`, Johnson/Desc/First/Borders.lean; `ansJT`, Honest/Thread/Ans.lean). A tenant is a
message's position (tree, number in the tree). `pinKept l` says, of each tenant of segment l's group that the next
segment keeps: a member of the plan's list is committed there; the verifier's statement holds the sample of each such
member; and the witness's message has that sample's answers. The three items `pin l 0`, `pin l 1`, `pin l 2` say the
same of all tenants that the segment sends at its three moments.

How it is proved. The three pins are open before the closing (`front_open_at_head`, Xch/RowAt.lean), so the invariant
gives them at the state before the step, at the run's witness (`exchangeAtS_from`, Xch/From.lean). What is kept lies
in the segment's group, which is the three moments' tenants (the library's `P5J.AtMg.kept`,
Johnson/LPFE1R/K10KeptAt.lean). An accepting step of the block at the closing's number gives `K10Keeps`
(`keeps_step_link`, Johnson/Desc/K10/Honest/KeepsStep.lean), which leaves every message's first sample row as it was
(`k10Keeps_row`, Honest/Thread/PinForwardKinds.lean). A pin passes from s to s' if every first sample row that s holds
at a member's number is held at s' (`ansJT_rows_older`, Honest/Thread/PinForward.lean). So each pin passes to the state
after the step, and the kept pins are among them.

  `ansJT_keeps`   where `K10Keeps s s'` holds (hk), a pin's statement at s (h0) passes to s', at the same witness, at
      any oracles and at any p and p'
  `pinKept_of_pins`   at any numbers N and any meaning Mg. hin: what the successor of segment m keeps lies in m's
      group. hpass: every pin passes from (a, y) to (a', y'). hJ: the three pins of m hold at (a, y). Then `pinKept m`
      holds at (a', y')
  `means_pinKept_at_head`   at each l < 25: the two together, with `P5J.AtMg.kept`, at the meaning of the head's thread
  **`exchange_pinKept_at_head`**   `ExchangeAtS` at `pinKept l`, at b = 14 l + `IM.nAt l` + 5, at each l < 25 and
      every Said
  `exchange_of_carry`   hc: `ExchangeAtS` at `carry l` at the closing of each l < 25. Then, by `exchange_of_two`
      (Xch/RowAt.lean), `ExchangeAtS` at every item that a closing's row owes
  `kept_none_last`, `means_pinKept_last`   under the head nothing is kept at segment 24, so `pinKept 24` holds at
      every state, oracles and witness

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out in the notation's own line.
It declares no new name, neither a definition nor a theorem: each use is that text, elaborated anew. A field of it is
written with brackets, `(𝕋).row`: without them Lean reads `𝕋.row` as one name. When a notation is declared, Lean
looks through its text for names that are not bound, and that early look has no case for a field access.
`set_option quotPrecheck false in` turns that one look off for the one command behind it; it loosens nothing in what
Lean checks of a theorem.

Limits. The one premise of `exchange_pinKept_at_head` is the head h. The prover H, the book Bk, the further parameters
of `lettersHead` (Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) and Said are variables: it holds at each of them.
Of `Thread.Stepped` it uses that `play` returned and that the step was accepted; besides, that the challenges fit the
declared rounds, and the invariant's clauses on the challenges heard and on the open items. The lemmas beneath it are
implications, with the premises named above: hk and h0; hin, hpass and hJ; hk and hJ in `means_pinKept_at_head`. hc,
the premise of `exchange_of_carry`, is shown in this file of no thread. Where the main statement is idle: at l = 24
(`means_pinKept_last`: the item says nothing there); at a border at which the invariant holds at no state; at a step
that is not accepted. Under the head something is kept at each of the segments 0 to 23: the library's `P5J.kept_some`
(Johnson/P5J/K10KeptTests.lean) says it of the written numbers `P5T.N0Full`, and by `P5J.AtMg.N_core`
(Johnson/P5T/CoreAtMg.lean) the head's `keptOf` is theirs; no theorem of this file joins the two. `ExchangeAtS` is a
definition, meant as a hypothesis of a lemma that gathers a whole chain (`owesS_head`, Honest/Thread/GatherHead.lean);
it is none of the library's goals. It is not shown that the invariant holds in any run, that a pin holds at any state
of a run, or that a closing accepts. Whether the head can be had at any files is not shown here. The full size and the
older hash alone. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.From
import Johnson.Desc.ProofFile.Honest.K10.Xch.RowAt
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.K10.Honest.KeepsStep
import Johnson.LPFE1R.K10KeptAt
import Johnson.P5J.K10KeptTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Place Strs Wit)
open VerifiableInference.Desc.First (S Item Numbers Meaning pinsOf)
open VerifiableInference.Desc.Sound (MsgT Mem smpNamed)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## What an accepted closing leaves of a pin -/

/-- Where `K10Keeps s s'` holds, a pin's statement at s passes to s', at the same witness, at any oracles and at any p
and p'. -/
theorem ansJT_keeps (cs : OnBytes.Codes) {Cells Tok : Type} (arr : Nat → Nat → Nat) {P : Type}
    {seats : List (Nat × Nat)} {ms : List Mem} {j t : Nat} {p p' : P} {s s' : S} {y y' : Strs}
    {v : Wit Cells Tok MsgT} (hk : YesFree.K10Keeps s s')
    (h0 : ansJT cs arr (smpNamed cs seats) ms j t (p, s) y v) :
    ansJT cs arr (smpNamed cs seats) ms j t (p', s') y' v :=
  ansJT_rows_older cs arr (fun _ _ _ _ hr => (k10Keeps_row hk _).trans hr) h0

/-! ## From the three pins to the kept pins -/

/-- **The three pins of a segment give its kept pins**, where what is kept lies in the segment's group and every pin
passes from the one argument to the other. -/
theorem pinKept_of_pins {P Wt : Type} (N : Numbers) (Mg : Meaning P Wt) (m : Nat)
    (hin : ∀ t ∈ N.keptOf m, t ∈ N.group m) {a a' : P × S} {y y' : Strs} {v : Wt}
    (hpass : ∀ j t, Mg.pin j t a y v → Mg.pin j t a' y' v)
    (hJ : ∀ i ∈ pinsOf m, Item.holds N Mg i a y v) : Item.holds N Mg (Item.pinKept m) a' y' v := by
  have h0 : ∀ z ∈ N.sent m 0, Mg.pin z.1 z.2 a y v := hJ (Item.pin m 0) (by simp [pinsOf])
  have h1 : ∀ z ∈ N.sent m 1, Mg.pin z.1 z.2 a y v := hJ (Item.pin m 1) (by simp [pinsOf])
  have h2 : ∀ z ∈ N.sent m 2, Mg.pin z.1 z.2 a y v := hJ (Item.pin m 2) (by simp [pinsOf])
  show ∀ z ∈ N.keptOf m, Mg.pin z.1 z.2 a' y' v
  intro z hz
  have hg : z ∈ N.sent m 0 ++ N.sent m 1 ++ N.sent m 2 := hin z hz
  rcases List.mem_append.1 hg with hg' | hg'
  · rcases List.mem_append.1 hg' with hg'' | hg''
    · exact hpass _ _ (h0 z hg'')
    · exact hpass _ _ (h1 z hg'')
  · exact hpass _ _ (h2 z hg')

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

/-- At the meaning of the head's thread: where `K10Keeps s s'` holds, the three pins of segment l at s give its kept
pins at s', at the same witness. -/
theorem means_pinKept_at_head (l : Nat) (hl : l < 25) (u : Local W₀ Rc ProofFile.Inst Tr) {p p' : ProofFile.InstPub}
    {s s' : TS} {y y' : Strs} {v : WtF} (hk : YesFree.K10Keeps s s')
    (hJ : ∀ j ∈ pinsOf l, (𝕋).means u j (p, s) y v) : (𝕋).means u (Item.pinKept l) (p', s') y' v := by
  have hJ' : ∀ j ∈ pinsOf l, Item.holds (P5J.At.N Zp cF)
      ((lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg u) j (p, s) y v := hJ
  have hpass : ∀ j t, ((lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg u).pin j t (p, s) y v →
      ((lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg u).pin j t (p', s') y' v := by
    intro j t h0
    rw [head_pin h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w u] at h0 ⊢
    exact ansJT_keeps (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp) hk h0
  have e := pinKept_of_pins (P5J.At.N Zp cF) ((lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg u) l
    (h.toAtMg.kept l hl) hpass hJ'
  exact e

/-- **`ExchangeAtS` holds at the item `pinKept l` at the closing of segment l**, for each l < 25 and every Said, with
the head as the only premise. -/
theorem exchange_pinKept_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + IM.nAt l + 5)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ExchangeAtS 𝕋 Said b (Item.pinKept l) := by
  subst hb
  refine exchangeAtS_from 𝕋 Said (pinsOf l) (fun j hj => ?_) ?_
  · exact front_open_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl j (List.mem_append_right _ hj)
  · intro blk hblk k s m E ds y cols s' ds' _ hd hS hJ
    have e1 : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := hblk
    have e2 : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
    have e3 : cF.blocksInOrder[LPFK10.ixK10 l]? = some blk := by
      rw [e2]
      exact e1
    have hy := stepYes_of_stepped 𝕋 hd hS
    have hk : YesFree.K10Keeps s s' := YesFree.keeps_step_link h l hl blk e3 _ s s' hy
    exact means_pinKept_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl m.st.input hk hJ

/-- `ExchangeAtS` at `carry l` at all 25 closings gives `ExchangeAtS` at every item that a closing's row owes, stated
with the unused extra hypothesis of `exchange_of_two`. -/
theorem exchange_of_carry (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hc : ∀ l, l < 25 → ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) (Item.carry l)) :
    ∀ l, l < 25 → ∀ j : Item, j ∈ ((𝕋).row (14 * l + IM.nAt l + 5)).owes →
      (j ∈ (𝕋).opened (14 * l + IM.nAt l + 5) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS 𝕋 Said (14 * l + IM.nAt l + 5) j :=
  exchange_of_two h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hc fun l hl =>
    exchange_pinKept_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl rfl Said

/-! ### Where the item says nothing -/

include h in
/-- Under the head nothing of segment 24's group is kept. -/
theorem kept_none_last : (P5J.At.N Zp cF).keptOf 24 = [] := by
  rw [h.toAtMg.N_core.2.1]
  exact P5J.kept_none_24

/-- So the item `pinKept 24` holds at every state, oracles and witness: at segment 24 `exchange_pinKept_at_head` says
nothing. -/
theorem means_pinKept_last (u : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF) :
    (𝕋).means u (Item.pinKept 24) a y v := by
  intro z hz
  have hz' : z ∈ (P5J.At.N Zp cF).keptOf 24 := hz
  rw [kept_none_last h] at hz'
  cases hz'

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ansJT_keeps
#print axioms ProofFile.Honest.K10.pinKept_of_pins
#print axioms ProofFile.Honest.K10.means_pinKept_at_head
#print axioms ProofFile.Honest.K10.exchange_pinKept_at_head
#print axioms ProofFile.Honest.K10.exchange_of_carry
#print axioms ProofFile.Honest.K10.kept_none_last
#print axioms ProofFile.Honest.K10.means_pinKept_last
