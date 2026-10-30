-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoAt.lean: CONDITIONAL: the hypothesis `K4WoTable`
(Law/Wo.lean) at the library's own parameters of the first chain's thread (`lettersAt`,
Honest/Thread/FirstAt.lean). One statement with its proof, by unfolding.

Not shown here. THAT THE HYPOTHESIS h ON THE PUBLIC FILES HOLDS OF ANY FILES: the library has such
an h under four hypotheses on the public files (`P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean: they are in scope; they are read; one test on the head's data;
one structure of conditions that is still owed); that the four hold together is not shown. THE
FULL SIZE ALONE, AND THE OLDER HASH (secondHashFunction) ALONE, as that file has it. The statements that spend
this table at the library's own reader are Law/WoHead.lean and Law/WoTop.lean; those of
Law/WoOf.lean, Law/WoTies.lean, Law/WoAtStand.lean and Law/WoShare.lean cannot be called at it
(their heads say why). IT IS A LAW, NOT A PART: no file that defines a part may import it. Nothing
on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk of the imports that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, Both…
and PassH…: 46 modules whose names hold RecCompile; it stopped at 16 under Johnson/Goal/ and 2
under ThirdParty/, and what these import is not counted; none under Johnson/D/, none of the three
names.

  `k4WoTable_at`: at these parameters the thread's sentence at the item `Item.wo m` is the library's
    `woAt` at the data's public numbers and the data's reader of the pile of pending rows.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Wo
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open ProofFile.Honest.FirstThread (Script WtF lettersAt)
open VerifiableInference.Desc (Strs Chain)
open VerifiableInference.Desc.First (Item)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **`K4WoTable` at the library's own parameters.** CONDITIONAL: on h. -/
theorem k4WoTable_at (m : Nat) :
    K4WoTable (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (Item.wo m) h.𝔇.d1 h.𝔇.rw13 m :=
  ⟨fun _ _ _ _ hw => hw⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4WoTable_at
