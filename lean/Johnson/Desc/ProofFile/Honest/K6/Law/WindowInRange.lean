-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/WindowInRange.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
TWO INEQUALITIES ON THE NUMBERS OF THE RECORD `K6HeadBelow` (Honest/K6/Law/ScriptBelowFree.lean),
WHICH THE RECORD ITSELF DOES NOT GIVE: UNDER h THE WINDOW OF K6's LEDGER SLOTS LIES INSIDE THE
HEAD's PLAN; UNDER THE RECORD AND ONE PUBLIC BOOL, "the book lends the row", THE BOOK's COUNT cnt IS
takesOf, AND EVERY SPENT COIN's ENTRY NUMBER LIES IN THE RANGE OF WHICH THE FIELDS sender AND reader
SPEAK. No definition; two theorems.

Why. In the record cnt is tied by the field stretch alone, and the field below bounds takesOf: so
nothing in it gives "elems + cnt ≤ free"; the field reader's range stops at the plan's number H.ns,
the fields sender and below at free: so nothing in it gives "elems + takesOf ≤ H.ns". A reader of
the record asked for the two, as fields or as lemmas. The record is out and does not turn.

  `k6_window_in_plan`   h ⊢ elems + takesOf ≤ H.ns: `within_of_takes` (Honest/K6/Law/DebtsLess.lean)
                        at the ceiling itself, under a name of its own
  `k6_spent_in_range`   the record, the Bool ⊢ cnt = takesOf, and at every j < cnt: elems + j < free
                        and elems + j < H.ns

By. `lendsRow`, `lendsRow_iff` (Honest/Small/LendsRow.lean: at every run's coins the frame's lendRow
returns just where that Bool of the book, the chain's number, the place and the parts' stated counts
is true); `cnt_is_takes_of_lent` (Honest/K6/Law/LentInside.lean). The second theorem binds no coin:
in its proof `lendsRow_iff` is called at the type's default member.

What it is not.
  * IT PAYS NONE OF THE RECORD's FIELDS: it stands on stretch and below.
  * THAT THE BOOL IS true AT ANY BOOK IS NOT SAID. At a book that lends the row at no coins cnt
    stays untied.
  * The record's own fields read coins (own, reader, sender, lent): handed on, not opened.
  * h: the full size and the format's second hash function alone.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptBelowFree
import Johnson.Desc.ProofFile.Honest.Small.LendsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes (E)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover Addr Due Cs lendsRow lendsRow_iff)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headRow headWit' cnt_is_takes_of_lent)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (cells : Tr → ProofFile.Honest.Cells) (weights : W₀ → ProofFile.Honest.Weights) (G : ProofFile.Ground)
  (o : Addr) (d : Due) (rowOf : Cs d → Nat → E) (own : Coins Bk → Cs d) (base cnt free : Nat)

include h in
/-- CONDITIONAL: the hypothesis h. **K6's window of ledger slots lies inside the head's plan.** -/
theorem k6_window_in_plan :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ≤
      (At.X Zp).H.ns :=
  within_of_takes h (Nat.le_refl _)

variable {h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
  base cnt free}

/-- CONDITIONAL: the record Dt; the public Bool "the book lends the row". **EVERY SPENT COIN's ENTRY
NUMBER LIES IN THE RANGE OF WHICH THE FIELDS sender AND reader SPEAK**; and cnt is takesOf. -/
theorem k6_spent_in_range
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free)
    (hb : lendsRow Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain
      IM.k6Place (headRow (X := X) (headWit' (Rc := Rc) cells weights Zp G)
        (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place) = true) :
    cnt = takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ∧
      ∀ j, j < cnt → OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + j < free ∧
        OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + j < (At.X Zp).H.ns := by
  obtain ⟨c, hl⟩ := (lendsRow_iff (default : Coins Bk) _ _ _).2 hb
  have e : cnt = takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) :=
    cnt_is_takes_of_lent (headWit' (Rc := Rc) cells weights Zp G)
      (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place default Dt.stretch hl
  have b1 := Dt.below
  have b2 := k6_window_in_plan h
  refine ⟨e, fun j hj => ?_⟩
  rw [e] at hj
  omega

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_window_in_plan
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_spent_in_range
