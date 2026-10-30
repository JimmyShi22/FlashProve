-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Opened.lean: the items that are open at the border in front of
the member at an attention segment's own rounds (kind K5), as the chain's invariant counts them
(`fwdOpen` over the rows read forward, Honest/Thread/Thr.lean, FirstRows.lean), ARE the table's own
open set at that border (`openSets`, Johnson/Desc/First/Borders.lean), at the library's full lists.

Why it is no unfolding. A row read forward owes again what it reads and leaves, and one row owes one
item more than the table's; the two steps agree only where what is read is open and is not closed.
So the equation is decided on the written lists.

  `fwdOpen_shift`   GENERAL: the open set one border on, as the open set of the rows from the second
  `opens_get`       GENERAL in the lists: the forward open sets in one pass (`FirstRows.opens`) are
                    `fwdOpen`, border by border
  `opensB`, `opens_closed`, `opens_bite`   a test with code on the written lists: at each of the
                    twelve borders the forward open set in one pass is the table's; a closed fact,
                    by the kernel; a control: at the chain's last border the test's comparison says
                    no
  `opened_full`     CONDITIONAL (g is below 12): **`fwdOpen` at the kind's border is the table's
                    open set there**
  `opened_thrAt`    CONDITIONAL (g is below 12): at the first chain's `Thread` at the library's own
                    letters

Limits. At the full size and the written lists alone; at the twelve borders of the kind alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Ready

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (ModelPart Item start openSets)
open ProofFile.Honest.FirstRows (rowAt rows opens)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-- The open set one border on is the open set, at the border, of the rows from the second on, from
the first row's step. General. No premise. -/
theorem fwdOpen_shift {ι : Type} [DecidableEq ι] (O : List ι) (row : Nat → FwdRow ι) :
    ∀ b, fwdOpen O row (b + 1) = fwdOpen (fwdStep O (row 0)) (fun n => row (n + 1)) b
  | 0 => rfl
  | b + 1 => by
    show fwdStep (fwdOpen O row (b + 1)) (row (b + 1)) =
      fwdStep (fwdOpen (fwdStep O (row 0)) (fun n => row (n + 1)) b) (row (b + 1))
    rw [fwdOpen_shift O row b]

/-- **The forward open sets in one pass are `fwdOpen`, border by border.** General in the lists.
CONDITIONAL: the border lies within the list. -/
theorem opens_get (links : List ModelPart) : ∀ (ps : List Place) (O : List Item) (b : Nat),
    b ≤ ps.length → (opens links ps O)[b]? = some (fwdOpen O (rows links ps) b)
  | [], _, 0, _ => rfl
  | [], _, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, _, 0, _ => rfl
  | p :: ps, O, b + 1, h => by
    show (opens links ps (fwdStep O (rowAt links p)))[b]? = _
    rw [opens_get links ps _ b (Nat.le_of_succ_le_succ h), fwdOpen_shift]
    rfl

/-- A test with code on the written lists: at each of the twelve borders of the kind the forward
open set in one pass is the table's own. -/
def opensB : Bool :=
  (List.range 12).all fun g =>
    (opens P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]? ==
      (openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?

set_option maxRecDepth 1000000 in
/-- **The test says yes.** No premise: a closed fact, by the kernel. -/
theorem opens_closed : opensB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the chain's last border the same comparison says no: there the rows read forward
have one item more open than the table. No premise: a closed fact, by the kernel. -/
theorem opens_bite :
    ((opens P5J.At.links P5J.At.ps (start P5J.At.links))[P5J.At.ps.length]? ==
      (openSets P5J.At.links P5J.At.ps (start P5J.At.links))[P5J.At.ps.length]?) = false := by
  decide +kernel

/-- **`fwdOpen` at the kind's border is the table's open set there.** CONDITIONAL: g is below 12. -/
theorem opened_full {g : Nat} (hg : g < 12) :
    fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (borderOf g) =
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [] := by
  have h1 := List.all_eq_true.1 opens_closed g (List.mem_range.2 hg)
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hle : borderOf g ≤ P5J.At.ps.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hpl).1
  rw [← beq_iff_eq.1 h1, opens_get _ _ _ _ hle]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **At the first chain's `Thread` at the library's own letters: what is open at the kind's border
is the table's open set there.** CONDITIONAL: g is below 12. -/
theorem opened_thrAt {g : Nat} (hg : g < 12) :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened (borderOf g) =
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [] :=
  opened_full hg

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.fwdOpen_shift
#print axioms ProofFile.Honest.K5.opens_get
#print axioms ProofFile.Honest.K5.opens_closed
#print axioms ProofFile.Honest.K5.opens_bite
#print axioms ProofFile.Honest.K5.opened_full
#print axioms ProofFile.Honest.K5.opened_thrAt
