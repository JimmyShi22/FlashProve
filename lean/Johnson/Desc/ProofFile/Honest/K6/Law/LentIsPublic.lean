--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/LentIsPublic.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
WHETHER THE BOOK LENDS K6's ROW OF PARTS IS ONE BOOL OF THE BOOK, THE CHAIN's NUMBER, THE PLACE AND
THE PLACE's PUBLIC NUMBERS: OF NO RUN's COINS, NO INPUT, AND NOT OF THE MAKER OF THE SMALL INPUT. No
definition; four theorems.

Why no definition. The seated row is by its own text the row before it is seated, mapped:
`headRow wit p at_` is `(headParts p at_).map` of the frame's lift (Honest/K6/Part.lean);
`headParts p at_` is typed at Unit and the small input, and is made of p and the place alone.

  `k6_lends_at_row`            lendsRow at the seated row = lendsRow at headParts p at_: the right
                               side names no wit
  `k6_lent_iff`                at every run's coins the frame's lendRow returns at the seated row
                               just where that Bool is true
  `k6_lent_alike`              returns or not is one at any two runs' coins and any two makers wit
  `k6_spent_in_range_public`   `k6_spent_in_range` (Honest/K6/Law/WindowInRange.lean) with its
                               premise at headParts

By. `lendsRow_map`, `lendsRow_iff`, `lendRow_isSome` (Honest/Small/LendsRow.lean); the frame's lift
keeps a part's three counts (takes, spends, carries) by its text.

What it is not.
  * THAT ANY BOOK LENDS THE ROW IS NOT SAID.
  * Nothing on WHAT is lent, or on any value: a statement on counts.
  * K6 lays no lot of texts on a message's entries: of where such a text would answer nothing is
    said here.
  * It pays no field of `K6HeadBelow`.
  * A law, no part: modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.WindowInRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par)

variable {W₀ Rc Tr X : Type}

/-- GENERAL. **WHETHER THE BOOK LENDS K6's SEATED ROW IS WHETHER IT LENDS THE ROW BEFORE IT IS
SEATED**: the right side names neither wit nor any type of the prover's input. -/
theorem k6_lends_at_row (Bk : ProverCoinCounts) (ch : Nat) (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par)
    (at_ : Place) :
    lendsRow Bk ch at_ (headRow (X := X) wit p at_) = lendsRow Bk ch at_ (headParts p at_) :=
  lendsRow_map Bk ch at_ _ (fun _ => ⟨rfl, rfl, rfl⟩) (headParts p at_)

/-- GENERAL. **AT EVERY RUN's COINS THE ROW IS LENT JUST WHERE THAT BOOL IS true.** -/
theorem k6_lent_iff {Bk : ProverCoinCounts} (k : Coins Bk) (ch : Nat) (wit : Local W₀ Rc Inst Tr → HeadAsk)
    (p : Head.Par) (at_ : Place) :
    (∃ c, lendRow Bk (Bk.rowsOf ch) (k.look ch) at_ (headRow (X := X) wit p at_) 0 = .ok c) ↔
      lendsRow Bk ch at_ (headParts p at_) = true := by
  rw [← k6_lends_at_row (X := X) Bk ch wit p at_]
  exact lendsRow_iff k ch at_ _

/-- GENERAL. **LENT OR NOT IS ONE AT ANY TWO RUNS' COINS AND ANY TWO MAKERS OF THE SMALL INPUT.** -/
theorem k6_lent_alike {Bk : ProverCoinCounts} (k k' : Coins Bk) (ch : Nat)
    (wit wit' : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    (lendRow Bk (Bk.rowsOf ch) (k.look ch) at_ (headRow (X := X) wit p at_) 0).toOption.isSome =
      (lendRow Bk (Bk.rowsOf ch) (k'.look ch) at_
        (headRow (X := X) wit' p at_) 0).toOption.isSome := by
  rw [lendRow_isSome, lendRow_isSome, k6_lends_at_row, k6_lends_at_row]

end ProofFile.Honest.K6

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes (E)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover Addr Due Cs lendsRow)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headParts k6_lends_at_row)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x} {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
  {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
  {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {item n₁ n₂ b₀ : Nat} {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
  {Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop} {Kp : Place → TS → TS → Prop}
  {w : Local W₀ Rc ProofFile.Inst Tr}
  {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {cells : Tr → ProofFile.Honest.Cells} {weights : W₀ → ProofFile.Honest.Weights} {G : ProofFile.Ground}
  {o : Addr} {d : Due} {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d} {base cnt free : Nat}

/-- CONDITIONAL: the record Dt; the public Bool "the book lends the row", AT THE ROW BEFORE IT IS
SEATED: of the book, the chain's number, the place and the place's public numbers alone.
`k6_spent_in_range` with its premise in that form. -/
theorem k6_spent_in_range_public
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free)
    (hb : lendsRow Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain
      IM.k6Place (headParts (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place) = true) :
    cnt = takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ∧
      ∀ j, j < cnt → OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + j < free ∧
        OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + j < (At.X Zp).H.ns :=
  k6_spent_in_range Dt ((k6_lends_at_row Bk _ _ _ _).trans hb)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms ProofFile.Honest.K6.k6_lends_at_row
#print axioms ProofFile.Honest.K6.k6_lent_iff
#print axioms ProofFile.Honest.K6.k6_lent_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_spent_in_range_public
