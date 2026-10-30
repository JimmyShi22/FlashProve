-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/RidesOk.lean: the column `hR` of `owesS_head` (GatherHead.lean)
from a table. The column asks `RidesPastAtS` (SharesS.lean) at every sub-protocol number `b` and
every item that is open at `b` and that the forward row at `b` neither closes nor has in `owes`.
Which items these are is a fact on the library's written lists. Here a test `ok` on a place and an
item stands for "an item of this kind may pass over a sub-protocol at this place". If one executable
test on the written lists says that `ok` holds of every pair that the column asks about, then it is
enough to prove `RidesPastAtS` at the pairs at which `ok` holds. No definition: `ok` is an argument.

  1  `onePass_at`   a test that passes along the list of open sets (`opens`, FirstRows.lean) passes
     at the open set at every border
  2  `head_row_at`   the forward row at number `b` is the row of the place at `b`
  3  `head_hR_of_ok`   the column `hR`, from `ok`

Limits.
  * `hone`, the test on the written lists, has no free variable once `ok` is fixed. It is proved
    here for no `ok`.
  * With `ok` always true, `hone` holds and the lemma says nothing.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item)

/-- A test on a place and the open set before it that passes along the whole list passes at every
border. -/
theorem onePass_at (links : List ModelPart) (t : Place → List Item → Bool) :
    ∀ (ps : List Place) (O : List Item),
    (((opens links ps O).zip ps).all fun x => t x.2 x.1) = true →
    ∀ b p, ps[b]? = some p → t p (fwdOpen O (rows links ps) b) = true
  | [], _, _, b, p, hp => by
    rw [List.getElem?_nil] at hp
    cases hp
  | q :: ps, O, h, b, p, hp => by
    have h' : (t q O &&
        ((opens links ps (fwdStep O (rowAt links q))).zip ps).all fun x => t x.2 x.1) = true := h
    rw [Bool.and_eq_true] at h'
    cases b with
    | zero =>
      have e : q = p := Option.some.inj hp
      rw [← e]
      exact h'.1
    | succ b =>
      have hp' : ps[b]? = some p := hp
      rw [fwdOpen_cons]
      exact onePass_at links t ps _ h'.2 b p hp'

end ProofFile.Honest.FirstRows

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item start)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The forward row at number `b` is the row of the place at `b`. -/
theorem head_row_at {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b =
      FirstRows.rowAt P5J.At.links p := by
  show ((P5J.At.ps[b]?).map (FirstRows.rowAt P5J.At.links)).getD {} = _
  rw [hp]
  rfl

/-- **The column `hR` from a table.** `hone`: along the written lists, every open item is closed by
the row, or is in its `owes`, or passes `ok`. `hok`: `RidesPastAtS` wherever `ok` passes. -/
theorem head_hR_of_ok (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (ok : Place → Item → Bool)
    (hone : (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i || ok x.2 i) = true)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → ok p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i := by
  intro b hb i hi h1 h2
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (List.getElem?_eq_getElem hb)
  have er := head_row_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp
  rw [er] at h1 h2
  have ht := FirstRows.onePass_at P5J.At.links
    (fun p O => O.all fun i => (FirstRows.rowAt P5J.At.links p).shuts.contains i ||
      (FirstRows.rowAt P5J.At.links p).owes.contains i || ok p i)
    P5J.At.ps (start P5J.At.links) hone b _ hp
  have hi' := List.all_eq_true.1 ht i hi
  simp only [Bool.or_eq_true] at hi'
  rcases hi' with (c1 | c2) | c3
  · exact absurd (List.contains_iff_mem.1 c1) h1
  · exact absurd (List.contains_iff_mem.1 c2) h2
  · exact hok b _ i hp c3

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstRows.onePass_at
#print axioms ProofFile.Honest.FirstThread.head_row_at
#print axioms ProofFile.Honest.FirstThread.head_hR_of_ok
