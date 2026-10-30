-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/Lines/JoinLinks.lean: the run on shapes over the twenty-four links, the head's
link and the back, laid together as one fact `RunsAll` (Johnson/AtFull/Shape/JoinAll.lean), and that
fact handed to the table's last joint (Johnson/AtFull/Shape/JoinTable.lean). General laws: no kernel
line and no literal shape stands here.

The 358 members (Johnson/AtFull/Shape/Table.lean): the front at 0; link l at 14 l + 1 to 14 l + 14;
the head's link at 337 to 352; the back at 353 to 357, with the proximity test at 354.

Main names.
  `links_chain`   n links, each of 14 members, one behind the other, are one stretch from member 1.
  `run_to_test`   front, twenty-four links, the head's link and member 353: members 0 to 353.
  `run_whole`     the same and the back's other four: all 358 members.
  `table_yes_of_links`   the conclusion of `table_yes_of_runsAll`, from these pieces.
  `debts_of_links`, `debts_halved_of_links`   the two uses of JoinTable.lean, from these pieces.

Limits. Every piece is a premise: no `RunsAll` is shown here but the idle one over no members
(`runsAll_zero`). `RunsAll` holds emptily where
publicOfO returns nothing (JoinAll.lean, "Limits"); the uses take hsz beside it. All limits of
JoinTable.lean hold of the three last names. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Shape.JoinTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- No members: the run returns what it was given. -/
theorem runsAll_zero (start : Nat) (shape : ShA) : RunsAll start 0 shape shape :=
  fun _ _ => rfl

/-- **n links, one behind the other**: each is 14 members from member 14 l + 1 on. -/
theorem links_chain (border : Nat → ShA) (n : Nat)
    (links : ∀ l, l < n → RunsAll (14 * l + 1) 14 (border l) (border (l + 1))) :
    RunsAll 1 (14 * n) (border 0) (border n) := by
  induction n with
  | zero => exact runsAll_zero 1 (border 0)
  | succ n hypothesis =>
    have before := hypothesis fun l hl => links l (Nat.lt_succ_of_lt hl)
    have last : RunsAll (1 + 14 * n) 14 (border n) (border (n + 1)) := by
      rw [Nat.add_comm]
      exact links n (Nat.lt_succ_self n)
    exact RunsAll.chain before last

/-- **From the first shape to the proximity test**: members 0 to 353. -/
theorem run_to_test (border : Nat → ShA) (shape353 shape354 : ShA)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (border l) (border (l + 1)))
    (head : RunsAll 337 16 (border 24) shape353) (finish : RunsAll 353 1 shape353 shape354) :
    RunsAll 0 354 startShA shape354 := by
  have toLinks : RunsAll 0 (1 + 14 * 24) startShA (border 24) :=
    RunsAll.chain front (links_chain border 24 links)
  have toHead : RunsAll 0 (1 + 14 * 24 + 16) startShA shape353 := RunsAll.chain toLinks head
  have toTest : RunsAll 0 (1 + 14 * 24 + 16 + 1) startShA shape354 := RunsAll.chain toHead finish
  exact toTest

/-- **All 358 members.** -/
theorem run_whole (border : Nat → ShA) (shape353 shape354 shape358 : ShA)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (border l) (border (l + 1)))
    (head : RunsAll 337 16 (border 24) shape353) (finish : RunsAll 353 1 shape353 shape354)
    (back : RunsAll 354 4 shape354 shape358) : RunsAll 0 358 startShA shape358 := by
  have whole : RunsAll 0 (354 + 4) startShA shape358 :=
    RunsAll.chain (run_to_test border shape353 shape354 front links head finish) back
  exact whole

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- One piece of n members, in the form of `table_yes_of_runsAll`. -/
theorem one_piece_of_whole {n : Nat} {shape : ShA} (whole : RunsAll 0 n startShA shape) :
    ∀ k, k < 1 → RunsAll (ProofFile.Honest.border (fun _ => n) k) ((fun _ => n) k)
      ((fun k => if k = 0 then startShA else shape) k)
      ((fun k => if k = 0 then startShA else shape) (k + 1)) := by
  intro k hk
  obtain rfl : k = 0 := Nat.lt_one_iff.1 hk
  exact whole

/-- **`table_yes_of_runsAll`, from the pieces.** -/
theorem table_yes_of_links (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (border : Nat → ShA) (shape353 shape354 shape358 : ShA)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (border l) (border (l + 1)))
    (head : RunsAll 337 16 (border 24) shape353) (finish : RunsAll 353 1 shape353 shape354)
    (back : RunsAll 354 4 shape354 shape358) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true :=
  table_yes_of_runsAll hsz h hB (fun _ => 358) (fun k => if k = 0 then startShA else shape358) 1
    (one_piece_of_whole (run_whole border shape353 shape354 shape358 front links head finish back))
    rfl rfl

open ProofFile.Honest (Thread Coins Mid ProverCoinCounts FitsAt Values NextJ AcceptedJ shapeJ) in
/-- **`debts_of_runsAll`, from the pieces.** -/
theorem debts_of_links (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (border : Nat → ShA) (shape353 shape354 shape358 : ShA)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (border l) (border (l + 1)))
    (head : RunsAll 337 16 (border 24) shape353) (finish : RunsAll 353 1 shape353 shape354)
    (back : RunsAll 354 4 shape354 shape358)
    {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (hF : ∀ b, b < 358 → FitsAt T b)
    (hV : ∀ b, b < 358 → Values T (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  debts_of_runsAll hsz h hB (fun _ => 358) (fun k => if k = 0 then startShA else shape358) 1
    (one_piece_of_whole (run_whole border shape353 shape354 shape358 front links head finish back))
    rfl rfl T hbs Said fall hF hV

open ProofFile.Honest (Thread Coins Mid ProverCoinCounts ValuesJ NextJ AcceptedJ shapeJ halved) in
/-- **`debts_halved_of_runsAll`, from the pieces.** -/
theorem debts_halved_of_links (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (border : Nat → ShA) (shape353 shape354 shape358 : ShA)
    (front : RunsAll 0 1 startShA (border 0))
    (links : ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (border l) (border (l + 1)))
    (head : RunsAll 337 16 (border 24) shape353) (finish : RunsAll 353 1 shape353 shape354)
    (back : RunsAll 354 4 shape354 shape358)
    {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (h4 : halved cF.blocksInOrder T.hs = true)
    (hV : ∀ b, b < 358 →
      ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA)
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  debts_halved_of_runsAll hsz h hB (fun _ => 358) (fun k => if k = 0 then startShA else shape358) 1
    (one_piece_of_whole (run_whole border shape353 shape354 shape358 front links head finish back))
    rfl rfl T hbs Said fall h4 hV

/-- A toy at letters: four links at numerals, laid by a match on the link's number, as a caller
lays the twenty-four: Lean takes `RunsAll 43 14 …` where `14 * 3 + 1` stands. -/
theorem toy_four_links (a b c d e : ShA) (link0 : RunsAll 1 14 a b) (link1 : RunsAll 15 14 b c)
    (link2 : RunsAll 29 14 c d) (link3 : RunsAll 43 14 d e) : RunsAll 1 56 a e :=
  links_chain (fun l => [a, b, c, d, e].getD l a) 4
    (fun l hl => match l, hl with
      | 0, _ => link0
      | 1, _ => link1
      | 2, _ => link2
      | 3, _ => link3)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.runsAll_zero
#print axioms Johnson.AtFull.Shape.links_chain
#print axioms Johnson.AtFull.Shape.run_to_test
#print axioms Johnson.AtFull.Shape.run_whole
#print axioms Johnson.AtFull.Shape.one_piece_of_whole
#print axioms Johnson.AtFull.Shape.table_yes_of_links
#print axioms Johnson.AtFull.Shape.debts_of_links
#print axioms Johnson.AtFull.Shape.debts_halved_of_links
#print axioms Johnson.AtFull.Shape.toy_four_links
