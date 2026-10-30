-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmHeadBareB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmHeadBare.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 5 OF
ITS DECLARATIONS: leftOn_at342_b · bareEnd_at342_b · bareLeaves_at342_b · hK6_of3_b · hPl_of3_b. THE
PROOFS ARE COPIES.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the original's block
binds dk (no twin's statement names it; it is kept so that a copied call has the original's number
of arguments). Kept as in the original: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmHeadBare
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadPaid2B
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
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab dataQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- The lookups' sentence at the state in front of the output head's reads' place. -/
theorem leftOn_at342_b {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) : k3LeftOnItemAt XV 24 x.2 := by
  have hin : Pub.leftOn 24 ∈ (First.pubSets (honest (mgAll Dm mgBase) ans test).more linksFull
      (flatPlacesOf linksFull true))[noL 24 false]?.getD [] := by
    have e : (honest (mgAll Dm mgBase) ans test).more = mgMore :=
      honest_more_closed Dm mgBase ans test rfl
    rw [e]
    exact List.contains_iff_mem.1 leftOpen342_mg
  have h0 := inAt_pubP hIn _ hin
  rw [honest_pubP_all Dm mgBase ans test] at h0
  exact h0

/-- **The form left for the join names no entry.** -/
theorem bareEnd_at342_b {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk → gk.cEnd.ents = #[] := by
  intro gk hg
  obtain ⟨p, _, ⟨h, _, F, F', G, g, rs, _, _, hK, hh, _⟩, _⟩ := leftOn_at342_b Dm dk hIn
  obtain rfl : g = gk := Option.some.inj (hh.symm.trans hg)
  exact hK.cEndEnts

/-- **The start form of the sumcheck over the leaves names no entry.** -/
theorem bareLeaves_at342_b {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk → gk.leaves.start.ents = #[] := by
  obtain ⟨p, _, _, hb⟩ := leftOn_at342_b Dm dk hIn
  exact hb

end

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM FOUR CLAUSES.** -/
theorem hK6_of3_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft4 XV (Dm.N.sent 24 0) x.2 A B Dm.cs Dm.arr Dm.ms Dm.N 24 w) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of2_b Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hK6' X arrs x x' y y' w p A B Fc hn
      ⟨L.hT, bareEnd_at342_b Dm dk Fc.inAt, L.hRun, L.hlab, L.hride⟩

/-- **THE PREMISE hPl OF arm_at_reads_three, FROM TWO CLAUSES.** -/
theorem hPl_of3_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (hPl' : ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w)) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU :=
  hPl_of2_b Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hPl' X arrs x x' y y' w p A B Fc hn
      ⟨L.hlen, bareLeaves_at342_b Dm dk Fc.inAt, L.hHostC⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.leftOn_at342_b
#print axioms VerifiableInference.Desc.K1.bareEnd_at342_b
#print axioms VerifiableInference.Desc.K1.bareLeaves_at342_b
#print axioms VerifiableInference.Desc.K1.hK6_of3_b
#print axioms VerifiableInference.Desc.K1.hPl_of3_b
