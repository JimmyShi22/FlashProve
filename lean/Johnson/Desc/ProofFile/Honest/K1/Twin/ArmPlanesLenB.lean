-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmPlanesLenB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmPlanesLen.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 3
OF ITS DECLARATIONS: shape_at342_b · hlen_at342_b · planesLeft4_of_b. THE PROOFS ARE COPIES.

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
dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmPlanesLen
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadBareB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- What the lookup on the calls heard has the shape of the plan's place. -/
theorem shape_at342_b {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∃ p h, First.Look.placeAt XV 24 false = some p ∧ p.shape = some h ∧
      ∀ gk, x.2.lookHeard? = some gk → gk.shape = h := by
  obtain ⟨p, hp, ⟨h, hsh, F, F', G, g, rs, _, _, hK, hh, _⟩, _⟩ := leftOn_at342_b Dm dk hIn
  refine ⟨p, h, hp, hsh, fun gk hg => ?_⟩
  obtain rfl : g = gk := Option.some.inj (hh.symm.trans hg)
  exact hK.shape

/-- **The clause hlen**, from a sentence on the public parameters. -/
theorem hlen_at342_b
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH) := by
  obtain ⟨p, h, hp, hsh, hg⟩ := shape_at342_b Dm dk hIn
  intro gk hk
  rw [hg gk hk]
  exact hLen p h hp hsh

end

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
/-- **PlanesLeft4 at a state inside the promise in front of the reads' place.** -/
theorem planesLeft4_of_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) {own own' : List (ℕ × ℕ)} {a b : K9.Part}
    {rdW : ℕ × ℕ → Sound.MsgQ} (L : PlanesLeft5 XV own own' x.2 a b rdW) :
    PlanesLeft4 XV own own' x.2 a b rdW :=
  ⟨hlen_at342_b Dm dk hLen hIn, L.hHostC⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.shape_at342_b
#print axioms VerifiableInference.Desc.K1.hlen_at342_b
#print axioms VerifiableInference.Desc.K1.planesLeft4_of_b
