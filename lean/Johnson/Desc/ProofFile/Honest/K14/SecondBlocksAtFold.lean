-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondBlocksAtFold.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): THE PREMISE hR OF Honest/K14/SecondBlocks.lean, MET UNDER THE LIBRARY's HEAD AT
THE RETURN OF A FOLD OVER THE FIRST CHAIN's FLAT LIST; so, AT THE START's RETURN OF THAT STATE, the
third and the fourth test of secondRest5 are true, and secondDoor follows from these, ThrS at the
shared chain's last border, secondRest3 and sW. Statements with their proofs. No definition.

  shape_at_head   **under the head the first chain's shape of the linear claim (Zp.first.lin) is the
                  shape at which "K14, second part" asks its tests ((p14At Zp).S)**: both are the
                  written proof sizes' batch shape: by the library's pins_of_laid
                  (Johnson/Goal/Skeleton/PinsOfLaid.lean), first_written_in_scope
                  (Johnson/Goal/Numbers/MadeInScope.lean), key_in_scope_pure
                  (Johnson/Goal/Numbers/KeyInScope.lean) and made_of_pinned
                  (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean)
  rows_at_head    **hR at the state that foldBlocks 0 cF.blocksInOrder returns** of a state with no row on
                  the table: by rows_at_end (Honest/K13/WeightBlocksAtFlat.lean), which gives one
                  row whose weights are the library's own blocks, each times an element, at the
                  shape Zp.first.lin
  third_fourth_at_fold   **THE TWO Bools ARE TRUE**: under the head; the fold begins at the first
                  chain's own start (ProofFile.startS Zp p, at any p), which has no row on the table (the
                  library's start_rows, Johnson/LPFK9R/MasksByPlace.lean), and returns s₁, at any
                  rounds and columns; the start of the last chain returns s of s₁: at the border of
                  s (there is one: border_rows) each weight has kRow variables, and each can be cut
                  below the matrix's rows. The two Bools are written out: they are secondRest5's by
                  reading; by Lean through varsTest_blocks and cutTest_blocks, which rest5_of_three
                  lays where secondRest5 asks the two
  second_door_three_fold   **secondDoor from secondRest3 and sW**: second_door_three_saidS
                  (Honest/K14/SecondBlocksAtHead.lean) with hR met so

"FOLD" MEANS foldBlocks 0 cF.blocksInOrder, AT ANY ROUNDS AND COLUMNS AT WHICH IT RETURNS. NO RUN, NO PROVER
AND NO INSTANCE's WITNESS IS NAMED. That the IOP as written in Lean folds its first chain so, and
hands the return to the start of the last chain, stands in no premise here and is not shown here.

WHAT IS LEFT OF second_door_saidS's PREMISES (Honest/K14/OmegaAtHead.lean): its premise on the
weights is gone; of the five tests of secondRest5 the third and the fourth are gone. NEW IN THEIR
PLACE: hF: s₁, the state that the start of the last chain is handed, is that fold's return.

What stays a premise in second_door_three_fold: the head; ThrS at the shared chain's last border at
s₂; the start's return at s₁ and s₂; hF; sW (where W's pad lies); the three tests of secondRest3.

What is not claimed. That one of these premises holds at any run, or that they can hold together:
THE FOLD's RETURN IS SHOWN OF NO ROUNDS. That the head holds at other files than those at which the
library shows it. That the sub-protocol accepts: secondDoor is a list of this kind's own (door_owed,
Honest/K14/SecondDoor.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondBlocksAtHead
import Johnson.Desc.ProofFile.Honest.K13.WeightBlocksAtFlat
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.FoldJ1
import Johnson.LPFK9R.MasksByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linLayW E stretchBlocks tensorBelow)
open VerifiableInference.Desc (Chain Place foldBlocks OpenedColumn)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

section tie
open VerifiableInference VerifiableInference.PlanWritten VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree Lk6.AtPlan
open VerifiableInference.PlanWritten.Joined

/-- **Under the library's head the first chain's shape of the linear claim is the shape at which
"K14, second part" asks its tests.** -/
theorem shape_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    Zp.first.lin = (ToldDesc.p14At Zp).S := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hF := (first_written_in_scope h.scope h.laid.pub hy).2.1
  have hM : Zp.p.chains.made.sized.proof = proofSizedFull := by
    unfold madePinnedAt at hy
    rw [key_in_scope_pure h.scope h.laid.pub] at hy
    exact (made_of_pinned hy).1.1
  show Zp.first.lin = Zp.p.chains.made.sized.proof.batch.shape
  rw [hF, hM]

end tie

/-- **hR at a fold's return**: under the library's head, at the state that foldBlocks 0 cF.blocksInOrder
returns of a state with no row on the table. -/
theorem rows_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (s₀ : P5J.TS) (h0 : s₀.rows = [])
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s₁ : P5J.TS) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder s₀ rs cols = .ok (s₁, r', cl)) :
    ∀ row ∈ s₁.rows, ∀ v ∈ row.g,
      ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (a : E),
        firstRow + values.size ≤ (ToldDesc.p14At Zp).S.matrixRows ∧
          ∃ t ∈ stretchBlocks (ToldDesc.p14At Zp).S.kRow firstRow values fuel start,
            v = t.scale a := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨row, hrow, hsc⟩ := ProofFile.Honest.K13.rows_at_end h.scope h.reads O
    (P5J.flat_ok h.toAtMg) s₀ h0 rs cols s₁ r' cl hF
  intro x hx
  rw [hrow] at hx
  obtain rfl := List.mem_singleton.1 hx
  rw [← shape_at_head h]
  exact hsc

/-- **The third and the fourth test of secondRest5 are true**: under the library's head, where
foldBlocks 0 cF.blocksInOrder returns s₁ of the first chain's own start, at any rounds and columns, and the
start of the last chain returns s of s₁. That s has a border follows from hs (border_rows). -/
theorem third_fourth_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s₁ : P5J.TS) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl))
    (x : ProofFile.InstPub) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∀ b, s.loc.border = some b →
      b.g.all (·.vars == (ToldDesc.p14At Zp).S.kRow) = true ∧
        (b.g.all fun v => (tensorBelow v 0 (ToldDesc.p14At Zp).S.kRow
          (ToldDesc.p14At Zp).S.matrixRows).isSome) = true := by
  intro b hb
  have hB := blocks_at_border Zp Np cF x s₁ s₂ s hs
    (rows_at_head h _ (LPFK9.start_rows h.laid.pub p) rs cols s₁ r' cl hF) b hb
  exact ⟨varsTest_blocks _ _ hB, cutTest_blocks _ _ hB⟩

section top
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **secondDoor, with three tests of the list left as premises**: from the library's head; ThrS at
the shared chain's last border at s₂; the start's return s at s₁ and s₂; hF: foldBlocks 0 cF.blocksInOrder
returns s₁ of the first chain's own start; sW: where W's pad lies; and the three tests of
secondRest3. -/
theorem second_door_three_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl))
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h3 : ok (secondRest3 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  second_door_three_saidS Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w
    h Said hA x s₁ s hs
    (rows_at_head h _ (LPFK9.start_rows h.laid.pub p) rs cols s₁ r' cl hF) sW h3

end top

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shape_at_head
#print axioms ProofFile.Honest.K14.rows_at_head
#print axioms ProofFile.Honest.K14.third_fourth_at_fold
#print axioms ProofFile.Honest.K14.second_door_three_fold
