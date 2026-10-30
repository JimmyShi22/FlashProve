-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmBySortB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmBySort.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 2 OF
ITS DECLARATIONS: linkNo_of_promise_b · armCellIn_bySort_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmBySort
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf Stand standOf
  standAt)
open VerifiableInference.Desc.First.FillSent (link_of_sentIs)
open VerifiableInference.Desc.K9 (segAt? Readers)
open VerifiableInference.Desc.Sound (Frame linksFull MsgT MsgQ MgData CellsQ mgAll d13 rowQ insQ
  outsQ relAt meansQ strsOf seatTab UFn uBySort uBySort_lay uBySort_att uBySort_head linkNo
  ArmCellIn)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

section
variable {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W}

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → P × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
theorem linkNo_of_promise_b (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : P × S) (y : Strs)
    (hIn : InAt Dm.N (honest (mgAll Dm Mg₀) ans test) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A : K9.Part) (hA : segAt? x.2 = some A) : linkNo x.2 = l := by
  have hin : Pub.more (some l) "frame.sentIs" ∈
      (First.pubSets (honest (mgAll Dm Mg₀) ans test).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] := by
    rw [honest_more_closed Dm Mg₀ ans test hM]
    exact inSet_of (List.all_eq_true.1 sentIn_mg l (List.mem_range.2 hl))
  have h0 := inAt_pub hIn _ (List.mem_append_left _ hin)
  rw [honest_pub_all, First.pubAll_more_sentIs] at h0
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some hA
  unfold linkNo
  rw [hLa]
  exact link_of_sentIs hLa h0

/-- **THE JOIN**, at one run. -/
theorem armCellIn_bySort_b (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : P × S) (y : Strs)
    (hIn : InAt Dm.N (honest (mgAll Dm Mg₀) ans test) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A B : K9.Part) (hA : segAt? x.2 = some A) (Rd : Readers)
    (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (rd : ℕ × ℕ → MsgQ)
    (h : ArmCellIn Rd own own' piece run x.2 A B rd
      (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l)) :
    ArmCellIn Rd own own' piece run x.2 A B rd (uBySort Dm.uL Dm.uA Dm.uH) := by
  refine armCellIn_congr Rd own own' piece run x.2 A B rd ?_ h
  rw [uBySort_at Dm.uL Dm.uA Dm.uH x.2 _ (stand_of_promise l hl x y hIn),
    linkNo_of_promise_b Dm dk Mg₀ hM l hl x y hIn A hA]

end

section
variable {Xi Tok Cl : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public} {F : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.linkNo_of_promise_b
#print axioms VerifiableInference.Desc.K1.armCellIn_bySort_b
