-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsPlanesFound.lean: the lookup on the digits of a segment's
approximate range proof: A PAYER, HELD BY LEAN AGAINST THE PREMISES' OWN TEXTS, FOR THREE PREMISES
OF hPlanesIt_dig (MgAt/K3DigitsPlanesIt.lean): hrawP («what the link states under "planes" at the
calls' piece is the lookup's own run at the calling kind's readers»: k03_planes_raw,
Johnson/Desc/First/Look/K03StatesRaw.lean: in the goals' scope, at the description
as it is opened) and hrdA, hrdH (these readers are the attention kind's, the output head's kind's:
the two arms of K3Lot.readersAt, Johnson/Desc/ProofFile/Lot/K3.lean). WHAT IT IS FOR: to show that
the three are meetable together under what is left below (hrd and hrHead among it). A joining. NO
RESULT ON THE PROTOCOL.

Main names.
  isHead_of_piece: the digits' piece 8 says «the output head's segment». readersAt_is_att,
    readersAt_is_head: which arm answers.
  hPlanesIt_dig_found: hPlanesIt_dig at lk := the opened description's own link l, with the three
    struck.
WHAT IS LEFT. THE GOALS' SCOPE AND THE OPENING (hSc, hR, O) · hlkc (Dm.lk l = c.links[l]?) · hrd
(the calling kind has readers at l: K3Lot.readersAt … l = some rd) · hlinks, hM · the place's and
the piece's · AT THE OUTPUT HEAD's SEGMENT: hrHead.
OBJECT. K9.statesOfLink at the description's own links; the composed public test at formsIn.
isHead_of_piece is used by K3DigitsPlanesHead.lean (Johnson/Desc/Sound/MgAt/); the other three
names are called by no other file.
LETTERS. Those of K03StatesRaw.lean and of hPlanesIt_dig; X := Bs.G₀.W.


Compiled with the whole library.


Limits. No segment is shown at which what is left holds.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesIt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift)
open VerifiableInference.Desc.K9 (readerOf statesOfLink)
open VerifiableInference.Desc.First.Att.P (readersOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The output head's segment. -/
theorem isHead_of_piece {X : Verify.Public} {l : ℕ} (h : Desc.K3.pieceAt X l true = 8) :
    Desc.K3.isHead X l = true := by
  unfold Desc.K3.pieceAt at h
  cases hh : Desc.K3.isHead X l with
  | true => rfl
  | false =>
    rw [hh] at h
    cases h

/-- Off the output head's segment the readers are the attention kind's. -/
theorem readersAt_is_att {X : Verify.Public} {l : ℕ} {rd : Desc.K3.Readers Desc.First.S}
    (hh : Desc.K3.isHead X l = false) (h : K3Lot.readersAt X l = some rd) :
    ∃ A, rd = readersOfO A := by
  unfold K3Lot.readersAt at h
  simp only [hh, Bool.false_eq_true, if_false] at h
  split at h <;> split at h <;>
    first
      | cases h
      | (obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
         exact ⟨A, rfl⟩)

/-- At the output head's segment they are that kind's. -/
theorem readersAt_is_head {X : Verify.Public} {l : ℕ} {rd : Desc.K3.Readers Desc.First.S}
    (hh : Desc.K3.isHead X l = true) (h : K3Lot.readersAt X l = some rd) :
    ∃ iU3, rd = callerReaders (planesAt iU3) := by
  unfold K3Lot.readersAt at h
  simp only [hh, if_true] at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨iU3, rfl⟩

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F₀ : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
  {A₀ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
  {Xi P Tok : Type} {rows cols nR : ℕ} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR Bs.G₀.W)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **THE PAYER SPENT.** -/
theorem hPlanesIt_dig_found (hSc : VerifierAndGoals.InScope Pf = true)
    (hR₀ : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F₀ Z Bs base c A₀ B₂)
    (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt Bs.G₀.W l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const Bs.G₀.W codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (hlinks : Dm.links = linksFull)
    (hlkc : Dm.lk l = c.links[l]?) (rd : Desc.K3.Readers Desc.First.S)
    (hrd : K3Lot.readersAt Bs.G₀.W l = some rd)
    (hrHead : ∀ lk : Desc.Link Desc.First.S Desc.Claim, c.links[l]? = some lk →
      sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
        SameBut u.1 v.1 → DigLeft u.1 v.1 →
        onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
        Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
          (readerOf (statesOfLink lk) (1 + shift sub) "planes" u.1).isSome = true) :
        sub ≠ .layers → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, v.1) = true := by
  obtain ⟨lk, pc, hlk, -, hP⟩ := k03_planes_raw hSc hR₀ O l hl rd hrd
  obtain ⟨hpc, -⟩ :=
    K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  rw [k3Ix_calls_shift hl hsub] at hP
  exact hPlanesIt_dig Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk
    (hlkc.trans hlk) pc.lm rd hP
    (fun e => by
      subst e
      exact readersAt_is_att (notHead_of_piece (hpc.symm.trans hpcT)) hrd)
    (fun e => by
      subst e
      exact readersAt_is_head (isHead_of_piece (hpc.symm.trans hpcT)) hrd)
    (hrHead lk hlk)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.isHead_of_piece
#print axioms VerifiableInference.OnPublicFiles.readersAt_is_att
#print axioms VerifiableInference.OnPublicFiles.readersAt_is_head
#print axioms VerifiableInference.OnPublicFiles.hPlanesIt_dig_found
