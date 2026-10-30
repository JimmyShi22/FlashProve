-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsSaid.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: THE FIELD othersP OF AttRestR, LayRestR AND CallsLeftR
(Johnson/Desc/Sound/MgAt/K3CallsRestR.lean, K3CallsLeftR.lean): "what each public item that is open
behind says beside its test, but for left l". At mgAll the sentences beside the tests are the
lookups' at left and leftOn, "true" at the items of the pending claim on the weights, and the
meaning beneath's at every other item (mgAll_pubP). By a test on the table (by the kernel) every
item that is open behind the lookup on the calls, but left l, is one at which the written table
says "no sentence is meant" (saysNone, Johnson/Desc/First/AllSaid.lean). So the field falls to ONE
premise on the meaning beneath: hPb. It reads no state. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: Meaning.pubP at the composed meaning; the table of joints.
Used by K3DigitsSaid.lean (Johnson/Desc/Sound/MgAt/) · K03OthersPAt.lean (Johnson/P5J/).
LETTERS: Dm, Mg: mgAll's parameters; l: a segment below 25; a: the place at the border kOfCalls l.

WHAT IS LEFT, BOOKED: term: hPb (where no sentence is meant the meaning beneath says nothing false:
  at the closed meaning beneath, mgBase (MgBase.lean), it is that meaning's own text) · hmore.

Main names: `pubP_of_said` (kind-free: at every item with saysNone) · `callsSaidB_mgMore` (by the
  kernel) · `callsSaidB_strict` (A NEGATIVE TEST: without the leave for left l the test says false)
  ·
  `othersP_mgAll`.

Limits. The full size's list and mgMore alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsTable
import Johnson.Desc.Sound.MgAt.K3CallsMean
import Johnson.Desc.First.AllSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc.First (More saysNone)
open VerifiableInference.Desc.First.FillP1 (p1Item)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **Where the table `saysNone` means no sentence, the composed meaning says what the meaning
beneath says, or nothing.** -/
theorem pubP_of_said (hPb : ∀ q a, (saysNone q).isSome = true → Mg.pubP q a) (p : Pub)
    (h : (saysNone p).isSome = true) (a : P × Desc.First.S) : (mgAll Dm Mg).pubP p a := by
  rw [mgAll_pubP]
  have key : ∀ r : Pub, (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) →
      (Desc.First.Look.fillK3 X Dm.sent
        (Desc.First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg)).pubP r a =
      (Desc.First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg).pubP r a := by
    intro r h1 h2
    cases r <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _)
  rw [key p (fun m e => by subst e; cases h) (fun m e => by subst e; cases h)]
  by_cases hp : p1Item p = true
  · exact Desc.First.FillP1.fillP1_pubP_own Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg p hp a
  · rw [Desc.First.FillP1.fillP1_pubP_else Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg p (by simpa using hp) a]
    exact hPb p a h

end

/-- The test at one segment. ok: which items need no "no sentence is meant". -/
def callsSaidRowB (M : More) (ok : ℕ → Pub → Bool) (l : ℕ) : Bool :=
  ((Desc.First.flatPlacesOf linksFull true)[kOfCalls l]?).any fun a =>
    (pubStep ((pubSets M linksFull (Desc.First.flatPlacesOf linksFull true))[kOfCalls l]?.getD [])
      (pubRowM M linksFull a)).all fun q => ok l q || (saysNone q).isSome

set_option maxRecDepth 1000000 in
theorem callsSaidB_mgMore :
    (List.range 25).all (callsSaidRowB mgMore fun l q => q == .left l) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the test can fail. -/
theorem callsSaidB_strict :
    (List.range 25).all (callsSaidRowB mgMore fun _ _ => false) = false := by decide +kernel

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  {l : ℕ} {a : Desc.Place} (b' : Desc.Block Desc.First.S Cl)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **othersP**, at every sort of segment. -/
theorem othersP_mgAll (hPb : ∀ r c, (saysNone r).isSome = true → Mg.pubP r c)
    (hmore : Mg.more = {}) (hl : l < 25) (here : PS[kOfCalls l]? = some a) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (kOfCalls l) u →
      Rch (kOfCalls l) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[kOfCalls l]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull a),
        p ≠ .left l → (mgAll Dm Mg).pubP p (z, v.1) := by
  intro B' _ z u v _ _ _ _ _ p hp hne
  rw [mgAll_more_closed Dm Mg hmore] at hp
  have h := List.all_eq_true.1 callsSaidB_mgMore l (List.mem_range.2 hl)
  unfold callsSaidRowB at h
  rw [here, Option.any_some] at h
  have h1 := List.all_eq_true.1 h p hp
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact absurd (beq_iff_eq.1 h1) hne
  · exact pubP_of_said Dm Mg hPb p h1 (z, v.1)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.pubP_of_said
#print axioms VerifiableInference.OnPublicFiles.callsSaidB_mgMore
#print axioms VerifiableInference.OnPublicFiles.callsSaidB_strict
#print axioms VerifiableInference.OnPublicFiles.othersP_mgAll
