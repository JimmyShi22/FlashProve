-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/HB/LLHARD/HeadFacts.lean: closed facts under the structure of conditions `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean), under which the counted statements at the full size stand, and under the
structure `P5J.AtMg` (Johnson/P5J/AtMg.lean) that it extends. Theorems with their proofs.

Why. A statement "under every `AtMgA o Z D r Zp Np cF x`" names, beside the three public files Z and
the letter o for the second hash function, six more letters. Here: (a) these six are fixed by o and
Z, so that "under every such structure" speaks of at most one; (b) the structure's data D are the
full size's written data, because one of the structure's own conditions compares the declared rounds
with the written lists; so the numbers of trees that these data give the first and the shared chain
are the written lists' numbers, 83 and 11.

Main names:
  `AtMg.unique`: two structures `AtMg` at one o and one Z have the same five other letters: the
    public part (the field pub of `LaidAt`, Johnson/P5J/LaidOpens.lean), the places (places), the
    first chain (`LaidAt.chain`, Johnson/P5J/TestsAtRun.lean), the data (data) and the run (run).
  `head_unique`: (a): two structures `AtMgA` at one o, Z, D, r have the same Zp, Np, cF and x. x is
    the place of the output head's lookup (the field headAt). ("head" in this theorem's name means
    the structure of conditions; in headAt it means the output head.)
  `head_unique_all`: (a) in one call: two structures `AtMgA` at one o and one Z have the same six
    other letters.
  `AtMg.data_written`, `data_written_at`: D is `Johnson.G.writtenPFull`: `laidPOf_written`
    (Johnson/Desc/Laid/ProofFullScope.lean) at `laidPOf_of` (ProofFullLaw.lean).
  `AtMg.trees`, `t1_t2_at`: (b): D.t₁ = 83 and D.t₂ = 11: by `t1_written` and `t2_written`
    (TreesWritten.lean). t₁ counts over the field ds₁, the first chain's rounds without its last,
    the seal; t₂ over ds₂, the chain that the written lists name "shared".
  `AtMg.data_at_depth`, `data_at_depth`, `AtMg.trees_at`, `trees_at_depth`: the same two facts at
    `D.at frS.P.T.a`: the data with their one field a, the stored table's depth, overwritten by the
    depth of the tables' code at the full size's sizes, which is 32: by `writtenPFull_at`
    (Johnson/Flat/Dec/DataAtWritten.lean). t₁ and t₂ do not read that field: the two on the trees
    give a form in which others' statements stand, and no new fact.
All eleven stand at every o.

Limits. A member of `AtMgA` and of `AtMg` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/): where there is none, both (a) and (b) speak of nothing; (a) says "at most
one", never "one". What has been evaluated, by the page of the
structure's authors: at o := `OnBytes.secondHashFunction` alone, by a program's run and not in Lean: most of the
conditions; not the seven of the field opts under their names; of the tests of the field asks the
eight that the list then had, of thirteen now; at another o nothing. That evaluation is not called
here. (The list of these tests, `LPFD.lawsAsk`, has fourteen entries in this library.)
(b) OPENS ONE OF THE STRUCTURE's OWN CONDITIONS: D = `writtenPFull` holds because the field
asks of `LaidAt` holds a test, `seatPinnedProof`, that compares the rounds declared for these public
files with the written lists. It says nothing on what the IOP as written in Lean makes of the files:
83 and 11 are numbers of the written lists, and that these lists are what the maker returns at the
shipped files is held by no test of the library at the full size (Johnson/G/DryProofTestsFull.lean
says so of itself). D is the structure's own letter: where another statement has data of its own (a
letter DP, or DP.at a depth), that they are this D is not said here. Two structures at different o
are not compared. Of the fields of `AtMg` two are spent: scope ((b)) and laid; of `AtMgA`'s own:
headAt ((a)). No negative test: neither statement has a test with code in it. The full size alone.
Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.TestsAtRun
import Johnson.Desc.Laid.ProofFullScope
import Johnson.HB.LLHARD.TreesWritten
import Johnson.Flat.Dec.DataAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D D' : WholeD} {r r' : LPFD.Full.RunPF}
  {Zp Zp' : ProofFile.Pub} {Np Np' : H2U.Places4} {cF cF' : Chain TS ProofFile.Cl}
  {x x' : VerifiableInference.Desc.First.Look.Place}

/-! ## (a) One structure -/

/-- **Two structures `AtMg` at one letter for the second hash function and one set of public files
have the same five other letters.** -/
theorem AtMg.unique (h : AtMg o Z D r Zp Np cF) (h' : AtMg o Z D' r' Zp' Np' cF') :
    Zp = Zp' ∧ Np = Np' ∧ cF = cF' ∧ D = D' ∧ r = r' := by
  obtain rfl : Zp = Zp' := Except.ok.inj (h.laid.pub.symm.trans h'.laid.pub)
  obtain rfl : Np = Np' := Except.ok.inj (h.laid.places.symm.trans h'.laid.places)
  obtain rfl : cF = cF' := Except.ok.inj (h.laid.chain.symm.trans h'.laid.chain)
  exact ⟨rfl, rfl, rfl, Except.ok.inj (h.laid.data.symm.trans h'.laid.data),
    h.laid.run.trans h'.laid.run.symm⟩

/-- **(a) Two structures `AtMgA` at one o, Z, D and r have the same four other letters.** -/
theorem head_unique (h : AtMgA o Z D r Zp Np cF x) (h' : AtMgA o Z D r Zp' Np' cF' x') :
    Zp = Zp' ∧ Np = Np' ∧ cF = cF' ∧ x = x' := by
  obtain ⟨rfl, rfl, rfl, -, -⟩ := h.toAtMg.unique h'.toAtMg
  exact ⟨rfl, rfl, rfl, Option.some.inj (h.headAt.symm.trans h'.headAt)⟩

/-- **(a) in one call: two structures `AtMgA` at one o and one Z have the same six other letters.**
-/
theorem head_unique_all (h : AtMgA o Z D r Zp Np cF x) (h' : AtMgA o Z D' r' Zp' Np' cF' x') :
    D = D' ∧ r = r' ∧ Zp = Zp' ∧ Np = Np' ∧ cF = cF' ∧ x = x' := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h.toAtMg.unique h'.toAtMg
  exact ⟨rfl, rfl, rfl, rfl, rfl, Option.some.inj (h.headAt.symm.trans h'.headAt)⟩

/-! ## (b) The data are the written data -/

/-- The structure's data are the full size's written data: because its own field asks holds a test
that compares the declared rounds with the written lists. Nothing is said on what the IOP as written
in Lean makes of the files. -/
theorem AtMg.data_written (h : AtMg o Z D r Zp Np cF) : D = Johnson.G.writtenPFull :=
  LPFD.Full.laidPOf_written h.scope
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- The same under the wider structure. -/
theorem data_written_at (h : AtMgA o Z D r Zp Np cF x) : D = Johnson.G.writtenPFull :=
  h.toAtMg.data_written

/-- By the data the first chain sends 83 trees and the shared chain 11. -/
theorem AtMg.trees (h : AtMg o Z D r Zp Np cF) : D.t₁ = 83 ∧ D.t₂ = 11 := by
  rw [h.data_written]
  exact ⟨Johnson.G.t1_written, Johnson.G.t2_written⟩

/-- **(b) The same under the wider structure.** -/
theorem t1_t2_at (h : AtMgA o Z D r Zp Np cF x) : D.t₁ = 83 ∧ D.t₂ = 11 := h.toAtMg.trees

/-! ### The same where the data's field for the stored table's depth is overwritten -/

/-- With their field a, the stored table's depth, overwritten by the depth of the tables' code at
the full size's sizes (32), the data are the written data still. -/
theorem AtMg.data_at_depth (h : AtMg o Z D r Zp Np cF) :
    D.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenPFull := by
  rw [h.data_written]
  exact VerifiableInference.OnPublicFiles.writtenPFull_at

/-- The same under the wider structure. -/
theorem data_at_depth (h : AtMgA o Z D r Zp Np cF x) :
    D.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenPFull := h.toAtMg.data_at_depth

/-- So the two numbers of trees are 83 and 11 there too. (They do not read that field: a form, no
new fact.) -/
theorem AtMg.trees_at (h : AtMg o Z D r Zp Np cF) :
    (D.at OnBytes.Slice.frS.P.T.a).t₁ = 83 ∧ (D.at OnBytes.Slice.frS.P.T.a).t₂ = 11 := by
  rw [h.data_at_depth]
  exact ⟨Johnson.G.t1_written, Johnson.G.t2_written⟩

/-- The same under the wider structure. -/
theorem trees_at_depth (h : AtMgA o Z D r Zp Np cF x) :
    (D.at OnBytes.Slice.frS.P.T.a).t₁ = 83 ∧ (D.at OnBytes.Slice.frS.P.T.a).t₂ = 11 :=
  h.toAtMg.trees_at

end P5J

#print axioms P5J.AtMg.unique
#print axioms P5J.head_unique
#print axioms P5J.head_unique_all
#print axioms P5J.AtMg.data_written
#print axioms P5J.data_written_at
#print axioms P5J.AtMg.trees
#print axioms P5J.t1_t2_at
#print axioms P5J.AtMg.data_at_depth
#print axioms P5J.data_at_depth
#print axioms P5J.AtMg.trees_at
#print axioms P5J.trees_at_depth
