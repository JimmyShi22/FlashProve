-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkKeyD.lean: THE THREE
SEATS OF A LOOKUP'S LINK (SeatsKeyD.lean) AT THE TYPED LOOKUP WITHOUT A LETTER (datK,
KeyLaw/Closed.lean): the typed lookup is made of the plan's lookup, the matrix's size and the table
of homes; its entries are read off the witness's words and matrix. So the four borders speak of the
record, the words and the matrix alone.

Main names:
  AK, slk, msgk, PK: the typed lookup, where a mask entry stands, the reading, the places of its
    masks, at the letters.
  callerK_tie, k3K_relLaw, layerK_tie: THE THREE SEATS.
  row0_rel: what the border in front of the caller claims, in words of the matrix: beside the riding
    joint, every key of every part that the matrix holds is the number of a row of the range table.

Limits. Those of SeatsKeyD.lean and KeyLaw/SeatK3.lean, but for FaceIs, Tied and KeysAre, which hold
here. Left as premises: Adm; l.d ≤ 64; Hands; Fits; Rides; ReadsLow and Pins of the riding joint;
MadeOf of the written rounds; the public tests.

-/
import Johnson.RunOne.Law.SeatsKeyD
import Johnson.Desc.First.Look.KeyLaw.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.LinkKeyD
open Iop OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params OnBytes.Maker KObj
open VerifiableInference.Desc (Block claimsIn)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound (JointRow RelLaw QuietTie seatPiece)
open VerifiableInference.Desc.Key (FirstState Claim LookupRecord lookupSeat caller layer layerOrder
  lookupPlace)
open Johnson.RunOne.Law.SeatsKeyD
open Lk6 (Dat pubOf)

variable {Fr : VerifiableInference.Desc.Sound.Frame} (one : OneTime) (set : Setting) (i : ℕ)
  (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (oL kL : List ℕ) (idxN : ℕ) (T : Type)
  (stOf : FirstState → T) {Kc M Wp : Type} (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)

/-- The typed lookup at the letters. -/
abbrev AK : Dat GE := datK T id m l (homeT one id m l oL kL idxN).toList

/-- Where a mask entry stands. -/
abbrev slk : Slot → (AK one id m l oL kL idxN T).J := slK T id m l (homeT one id m l oL kL
    idxN).toList

/-- The typed entries, read off a witness's words and matrix. -/
abbrev msgk (u : M) : (AK one id m l oL kL idxN T).J → GE :=
  msgK T id m l (homeT one id m l oL kL idxN).toList one.ranges one.codes i (wd u) (mx u)

/-- The standard places of the typed lookup's masks at the letters' entries. -/
abbrev PK : Lk6.Pl (AK one id m l oL kL idxN T) :=
  placesAt (AK one id m l oL kL idxN T) (slk one id m l oL kL idxN T)
    (fun n => (oL.map fun j => (⟨one.ranges.messageId, j⟩ : Slot)).getD n default)
    (fun n => (kL.map fun j => (⟨idxN, j⟩ : Slot)).getD n default)

variable (R0 : IOR.Rels Kc T Fr.E (M × Wp))
variable {one set i id m l oL kL idxN T stOf wd mx}

/-- **The caller's seat.** -/
theorem callerK_tie (hst : Rides stOf i) :
    QuietTie (caller one i (Wf.lookupOf id m l))
      (row0 one i id m l oL kL idxN (AK one id m l oL kL idxN T) stOf R0
        (msgk one i id m l oL kL idxN T wd mx))
      (rowIn lookupSeat (AK one id m l oL kL idxN T) stOf (Inv one i id m l oL kL idxN) R0
        (msgk one i id m l oL kL idxN T wd mx)) :=
  callerD_tie hst

set_option maxHeartbeats 1600000 in
/-- **The seat of the kind's own block.** -/
theorem k3K_relLaw (before : List (ℕ × ℕ)) (bits : ℕ) (base : ℕ) (ds : List RDT)
    (hst : Rides stOf i)
    (hnd : (Fr.all.map (·.no)).Nodup) (hadm : (pubOf (Wf.lookupOf id m l)).Adm Cb.Gl.p)
    (hd : l.d ≤ 64)
    (hB : ReadsLow (AK one id m l oL kL idxN T) R0 base)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf id m l)))) (st0 : T) :
    RelLaw (lookupKind lookupSeat before bits [] (lookupPlace set i (Wf.lookupOf id m l))) base ds []
      (bkLam (AK one id m l oL kL idxN T) (PK one id m l oL kL idxN T) Fr.E R0
        (msgk one i id m l oL kL idxN T wd mx))
      (mapsOf (Lk6.lamS_runs (AK one id m l oL kL idxN T) (PK one id m l oL kL idxN T) Fr.E).rd ds
        (meets_typed (AK one id m l oL kL idxN T) st0 (PK one id m l oL kL idxN T) Fr.E
          (faceOfLkp (Wf.lookupOf id m l))
          (faceIsK T id m l (homeT one id m l oL kL idxN).toList st0 hadm hd) hadm ds
          hds).1.length_eq)
      (fun a => (stOf a.1, a.2))
      (rowIn lookupSeat (AK one id m l oL kL idxN T) stOf (Inv one i id m l oL kL idxN) R0
        (msgk one i id m l oL kL idxN T wd mx))
      (rowOut lookupSeat (lookupPlace set i (Wf.lookupOf id m l)) (AK one id m l oL kL idxN T)
        (slk one id m l oL kL idxN T) (fun n => (homeT one id m l oL kL idxN).getD n default) stOf
        (Inv one i id m l oL kL idxN) R0 (msgk one i id m l oL kL idxN T wd mx)) :=
  k3D_relLaw (A := AK one id m l oL kL idxN T) (sl := slk one id m l oL kL idxN T) before bits base
    ds hst hnd (fun st => faceIsK T id m l _ st hadm hd) hadm hB hds st0

/-- **The layer's seat: the exchange.** The matrix is cut at its size. -/
theorem layerK_tie {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ}
    (hst : Rides stOf i)
    (hadm : (pubOf (Wf.lookupOf id m l)).Adm Cb.Gl.p)
    (hlo : Wf.lookupOk Wf.fBits l = true) (hfm : Wf.fitsMatrix m l = true)
    (hi : one.ranges.lookups[i]? = some l)
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true) :
    QuietTie (layer one set i (Wf.lookupOf id m l)
        (claimsIn [b0, lookupKind lookupSeat before bits [] (lookupPlace set i (Wf.lookupOf id m l))]
          [(1, "objects"), (1, "planes"), (1, "guests")]))
      (rowOut lookupSeat (lookupPlace set i (Wf.lookupOf id m l)) (AK one id m l oL kL idxN T)
        (slk one id m l oL kL idxN T) (fun n => (homeT one id m l oL kL idxN).getD n default) stOf
        (Inv one i id m l oL kL idxN) R0 (msgk one i id m l oL kL idxN T wd mx))
      (row3 one i id m l oL kL idxN (AK one id m l oL kL idxN T) stOf R0 wd fun u => cutM m (mx u))
          :=
  layerD_tie hst rfl hadm hlo hfm hi hla (fun u => tiedK T id m l _ _ _ i (wd u) (mx u))
    fun st u => by
      have h := keysAreK T id m l (homeT one id m l oL kL idxN).toList st
        (msgk one i id m l oL kL idxN T wd mx u)
      rw [matOf_cut] at h
      exact h

/-- **What the border in front of the caller claims.** -/
theorem row0_rel (a : FirstState × Fr.E.Str) :
    (row0 one i id m l oL kL idxN (AK one id m l oL kL idxN T) stOf R0
      (msgk one i id m l oL kL idxN T wd mx)).rel a ↔
      ∃ w : M × Wp, R0.relR (stOf a.1, a.2) w ∧ KeysIn id m l (cutM m (mx w.1)) := by
  constructor
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, h1, (in_iff_at T id m l _ _ _ _ i _ _).1 h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, h1, (in_iff_at T id m l _ _ _ _ i _ _).2 h2⟩

end Johnson.RunOne.Law.LinkKeyD

#print axioms Johnson.RunOne.Law.LinkKeyD.callerK_tie
#print axioms Johnson.RunOne.Law.LinkKeyD.k3K_relLaw
#print axioms Johnson.RunOne.Law.LinkKeyD.layerK_tie
#print axioms Johnson.RunOne.Law.LinkKeyD.row0_rel
