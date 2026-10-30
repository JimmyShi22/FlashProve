-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmElsePaidB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmElsePaid.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: hElse_of_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the source has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm
Mg₀), or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no twin's statement names it; it is kept so that a copied call has the source's number of
arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmElsePaid
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadB
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
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs named)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf standOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase rowQ Mem
  seatTab dataQ ArmCellIn)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf LinkHoles statesOfLink readersOfLink
  holesAt phAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent K6Name p8K6)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
/-- **THE PREMISE hElse OF arm_at_reads_three, FROM J ALONE.** -/
theorem hElse_of_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJb : ∀ s, J s → RowsBareH s) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 →
      p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24) := by
  intro X arrs x x' y y' w p A B Fc h6 hp
  obtain ⟨lk, _, _, _, eL, -⟩ := IM.k6_of hS hR O
  have hX : headLink XV = 24 := hWX ▸ headLink_open hS hR O
  obtain ⟨hp1, hp8⟩ : p.1 = 2 ∧ (p.2 == "K8.equations") = false := by
    refine else_of_run ?_ h6 hp
    obtain ⟨j, n, h1, h2⟩ := Fc.run
    refine ⟨j, n, h1, ?_⟩
    have h2' : p ∈ runsAt Dm.links 24 j n := h2
    rw [hDlk] at h2'
    exact h2'
  obtain ⟨o, ho⟩ := here_head_of_stand (stand_of_promise 24 (by decide) x y Fc.inAt)
  have hb : RowsBare x.2 := hJb _ Fc.inv o ho
  have hr := states2_bare hS hR O lk eL p.2 hp
  intro R hR' f hf e he
  exfalso
  rw [rd24 Dm hX lk ((hlk 24 (by decide)).trans eL), hp1] at hR'
  have h1 : (if (p.2 == "K8.equations") = true then (holesAt XV 24 24 lk).small x.2
    else
      match readerOf (statesOfLink lk) 2 p.2 x.2 with
      | some R => some R
      | Option.none => (holesAt XV 24 24 lk).silent 2 p.2 x.2) = some R := hR'
  rw [hp8, silent24] at h1
  have hbare : ∀ f ∈ R.forms, f.ents = #[] := by
    cases hq : readerOf (statesOfLink lk) 2 p.2 x.2 with
    | some R₁ =>
      rw [hq] at h1
      obtain rfl : R₁ = R := Option.some.inj h1
      exact reader_bare _ 2 p.2 hr hb hq
    | none =>
      rw [hq] at h1
      have h2 : (withTables (p8K6 XV 24) x.2).bind (readerOf (statesOfLink lk) 2 p.2) = some R := h1
      obtain ⟨e', he', h3⟩ := Option.bind_eq_some_iff.1 h2
      exact reader_bare _ 2 p.2 hr (rowsBare_tables _ he' hb) h3
  rw [hbare f hf] at he
  cases he

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hElse_of_b
