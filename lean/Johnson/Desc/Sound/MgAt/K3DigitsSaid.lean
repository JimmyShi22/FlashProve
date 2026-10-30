-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3DigitsSaid.lean: the lookup on the digits of a segment's approximate range
proof: THE FIELD othersP OF THE KIND's LEDGER's DigOwedR (Johnson/Desc/Sound/MgAt/K3Owed.lean: «the
sentences at the public items that are open behind, but left and leftOn, hold behind»), IN ITS OWN
TEXT, AT ITS OWN LETTERS, AT THE COMPOSED MEANING mgAll Dm Mg. After the like at the calls
(MgAt/K3CallsSaid.lean), whose kind-free lemma pubP_of_said is called. NO SOUNDNESS IS CLAIMED.

Main names.
  digSaid_mgMore: by the kernel, at all 25: every item that is open behind the digits' place at the
    closed list mgMore is left m, leftOn m, or one at which the written table means no sentence
    (saysNone, Johnson/Desc/First/AllSaid.lean). digSaid_strict: A NEGATIVE TEST, foretold by
    reading, untried: with no item let off the test says false (leftOn l stands behind).
    (Where this and lean/THEOREM.md differ, the page
    holds.)
  othersP_dig_mgAll: THE FIELD.
WHAT IS LEFT. hM (the meaning beneath has no extra public test) · hPb (the meaning beneath says its
sentence wherever the table means none: met at the closed base by its own text).
NO FACT ALONG THE FOLD AND NONE OF THE FIELD's PREMISES IS SPENT.
OBJECT. Functions with code of the table of joints at closed lists; the composed meaning's field
pubP.
Used by K3DigitsOwedSeven.lean (Johnson/Desc/Sound/MgAt/) and K03OthersPAt.lean (Johnson/P5J/).
LETTERS. Dm, Mg, Rch; l, q, b'.
IS IT EMPTY? The evaluations have no premise.


Compiled with the whole library.


The ledger's two texts othersPub, othersP at the digits bear two premises behind the promise in
front: «reached» (Rch k ((z, u.1), u.2)) and «no mark» (u.1.failed = none).

Limits. The closed list mgMore of the build apart; the full size's lists.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsSaid
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub More Meaning pubSets pubStep pubRowM saysNone)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The test at one segment. ok: which items need no "no sentence is meant". -/
def digSaidRowB (M : More) (ok : Pub → Bool) (l : ℕ) : Bool :=
  (pubStep ((pubSets M linksFull PS)[k3K l true]?.getD [])
    (pubRowM M linksFull (IM.k3Place l true))).all fun q => ok q || (saysNone q).isSome

/-- left m, leftOn m. -/
def isLeftB : Pub → Bool
  | .left _ => true
  | .leftOn _ => true
  | _ => false

set_option maxRecDepth 1000000 in
theorem digSaid_mgMore : (List.range 25).all (digSaidRowB mgMore isLeftB) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test.** -/
theorem digSaid_strict : (List.range 25).all (digSaidRowB mgMore fun _ => false) = false := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **THE FIELD othersP.** -/
theorem othersP_dig_mgAll (hM : Mg.more = {})
    (hPb : ∀ r c, (saysNone r).isSome = true → Mg.pubP r c) {l : ℕ} (hl : l < 25)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) :
    ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1) := by
  intro B' _ z u τ v _ _ _ _ _ _ r hr h1 h2
  rw [mgAll_more_closed Dm Mg hM] at hr
  have h := List.all_eq_true.1 digSaid_mgMore l (List.mem_range.2 hl)
  unfold digSaidRowB at h
  have h0 := List.all_eq_true.1 h r hr
  rw [Bool.or_eq_true] at h0
  rcases h0 with h0 | h0
  · cases r with
    | left m => exact absurd rfl (h1 m)
    | leftOn m => exact absurd rfl (h2 m)
    | _ => cases h0
  · exact pubP_of_said Dm Mg hPb r h0 (z, v.1)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digSaid_mgMore
#print axioms VerifiableInference.OnPublicFiles.digSaid_strict
#print axioms VerifiableInference.OnPublicFiles.othersP_dig_mgAll
