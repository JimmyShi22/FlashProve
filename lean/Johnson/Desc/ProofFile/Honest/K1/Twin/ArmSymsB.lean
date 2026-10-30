-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmSymsB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmSyms.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF ITS
DECLARATIONS: symsIn_at_reads_b. THE PROOFS ARE COPIES.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no statement here names it; it is kept so that a copied call has the source's number of
arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmSyms
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttEntryB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ linkNo)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **Inside the fence, at the written list, layout and shape.** -/
theorem symsIn_at_reads_b {J : S → Prop} (hM : Mg₀.more = {}) {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ}
    {R₁ R₂ R₃ : Rounds} {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String}
    {A B : K9.Part} (Fc : ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    {shp : ReqShape} {lay₀ : ReqLayout} (hJl : ∀ s, J s → LiveIs shp lay₀ s) {tl : HTailF2}
    (hB : symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l tl = true)
    (hF : FirstSeated (Dm.N.sent l 0) A l) : SymsIn (Dm.N.sent l 0) A tl := by
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have hlive : x.2.live = A.L.check := by
    unfold S.live
    rw [hLa]
  obtain ⟨eS, eL⟩ := hJl _ Fc.inv
  rw [hlive] at eS eL
  refine symsIn_of_B ?_ hF
  rw [arrays_at_reads_b Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front, eS, eL]
  exact hB

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.symsIn_at_reads_b
