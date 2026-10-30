-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
led_mgAll: no state inside the promise is shown here.
Johnson/Desc/Sound/MgAt/K3RidesLed.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll: THE
PREMISE hLed OF ridesAtR_digits_mgAll | ridesAtR_digits_ledger
(Johnson/Desc/Sound/MgAt/K3RidesDig.lean, K3RidesDigLedger.lean), IN ITS OWN TEXT, AT THE DIGITS'
BORDER k3K l true: inside the promise in front an unmarked state holds a ledger whose three arrays
have one entry a slot. From: the public test "ledger l" stands in front of the digits' place
(digits_sorted, Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean: by the kernel) · the promise holds
every public test that is open or tied there (onQ_front,
Johnson/Desc/Sound/MgAt/K3CallsOthers.lean) · at the composed meaning that test is ledgerB. AND
TWO CHECKS THAT WERE OWED: an example in which Lean lays ridesAtR_calls_ledger into the field
rides of the head's own structure HeadRestR (Johnson/Desc/Sound/MgAt/K3Mean.lean) · a kernel
evaluation: every place of the kind K3 in the driver's list has piece 3 or below, or 7 or above,
and there are fifty. Statements and proofs. No error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints' promise at a border; First.ledgerB.
Used by K3RidesDigFwd.lean, K3RidesDigFwd2.lean and K3RidesDigFwd3.lean
  (Johnson/Desc/Sound/MgAt/) and others.
LETTERS: Dm, Mg, Rch, l, sub.
IMPORTS: Johnson/Desc/Sound/MgAt/K3DigitsSorted.lean,
  K3CallsOthers.lean,
  K3RidesLedger.lean,
  K3Mean.lean;
  Johnson/Desc/First/Look/K3KeeperRides.lean.
  Compiled with the whole library.
Main names: `led_mgAll`; `k3SplitB`, `k3Split_full`.

WHAT IS LEFT: hM: the meaning beneath has no extra public test (the ledger's own hM).
Limits. One list of segments.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsSorted
import Johnson.Desc.Sound.MgAt.K3CallsOthers
import Johnson.Desc.Sound.MgAt.K3RidesLedger
import Johnson.Desc.Sound.MgAt.K3Mean
import Johnson.Desc.First.Look.K3KeeperRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- Every place of the kind K3 has piece 3 or below, or 7 or above; there are fifty. -/
def k3SplitB : Bool :=
  ((PS).filter fun a => decide (a.kind = .K3)).all (fun a => decide (a.piece ≤ 3 ∨ 7 ≤ a.piece)) &&
    ((PS).filter fun a => decide (a.kind = .K3)).length == 50

set_option maxRecDepth 100000 in
theorem k3Split_full : k3SplitB = true := by decide +kernel

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

/-- **hLed, AT THE DIGITS' BORDER.** -/
theorem led_mgAll (hM : Mg.more = {}) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hs : linksFull[l]? = some sub) :
    ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      ∃ F, u.1.fork? = some F ∧ OnBytes.PscRun.Sized F := by
  intro z u hu _ hm
  have hu0 : u.1.failed = none := Classical.not_not.1 hm
  have hq : Pub.ledger l ∈ frontDig mgMore l :=
    (digits_sorted hl hs).2 _ (by cases sub <;> simp [keptDigits])
  have hf := onQ_front hu hu0
  rw [mgAll_more_closed Dm Mg hM] at hf
  have h1 := hf _ hq
  rw [mgAll_pub, Desc.First.pubAll_ledger, ledgerB_is] at h1
  cases hF : u.1.fork? with
  | none =>
    rw [hF] at h1
    cases h1
  | some F =>
    rw [hF] at h1
    exact ⟨F, rfl, sized_of_sizedB h1⟩

/-- **Lean holds ridesAtR_calls_ledger against the field rides of the head's own structure.** (The
example proves nothing new: its end is its premise T's.) -/
example (claim : Aff → Cl) (sts : List (ℕ × ℕ)) (s₀ : Desc.First.S) (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (arrs : Array (Nat × String)) (pl pl' : Desc.Place)
    (told : List (List Desc.Oracle))
    (T : HeadRestR Dm Mg Rch claim sts s₀ x q b' arrs pl pl' told) (a : Desc.Place)
    (seats : List (ℕ × ℕ)) (es : Dm.smp = smpNamed Dm.cs seats)
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (ha : PS[k3K 24 false]? = some a) (hK : a.kind = .K3) (hp : a.piece ≤ 3) (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl
          (Desc.Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ = some v → SameBut u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i)) :
    HeadRestR Dm Mg Rch claim sts s₀ x q b' arrs pl pl' told :=
  { T with
    rides := ridesAtR_calls_ledger Dm Mg seats es hD hd Rch (k3K 24 false) q b' ha hK hp hback
      hRel hj hReq hHead }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3Split_full
#print axioms VerifiableInference.OnPublicFiles.led_mgAll
