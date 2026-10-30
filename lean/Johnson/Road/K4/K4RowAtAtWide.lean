-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowAtAtWide.lean: THE STRUCTURE `K4RowAt` (K04LawOf.lean: what the assembly of
K4's law leaves for the lines in front, the riders and what an accepting run keeps: eleven letters
and six fields) HAS A MEMBER AT THE WIDER MEANING OVER THE CLOSED BASE, `mgWide Dm E mgBase`, AND
ITS DATA `k4DataWide Dm E mgBase`, under the premises of `k4Row_wide` (K4RowAtWide.lean) but hbase.
One statement with its proof: calls.

  **`rowAt_wide`**: hH · `AtK4` · `K4OnX` (9) · `K4OnD` (8) · `K4NamedW` (9) · hhead · Dm.lk m =
  some l · the five ties on l's sub-protocols ⟹ `Nonempty (K4RowAt x linksFull … k m pl q
  (k4DataWide Dm E mgBase) (mgWide Dm E mgBase) told z)`. THE LETTERS: rest := restNames · Hh := the
  composed meaning's own holes at l · the others the premises' own.

Limits. THE WIDER MEANING IS A BRIDGE's SIDE, NOT THE MEANING THAT COUNTS. EVERY PREMISE NAMED
STANDS; THEY ARE SHOWN TOGETHER AT NO Dm. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K04LawOf
import Johnson.Road.K4.K4RowAtWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.Riders (door_of_fit k4_door_full restNames k4Kept_of_means door_funs)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.statesOfLink)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (Frame Piece strsOf MsgT mgWide MgData WideData mgBase
  linksFull mgAll_pubP_said)

variable {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub) {z : ProofFile.InstPub}
  {k m : ℕ} {pl : Place} {x : Bool × Par}
  {q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK rows cols) Tok MsgT)}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
  {runO runG : ℕ → S → Except String (List Claim × S)}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := ProofFile.InstPub) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **UNDER hH, H, Sx, Sd, Sn, hhead, hlk AND THE FIVE TIES (ALL PREMISES): the assembly's structure
for K4's row has a member at the wider meaning over the closed base.** -/
theorem rowAt_wide (hH : isLay Dm.links (headLink X) = false)
    (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl)
    (Sx : K4OnX X pol KL layout m (parOf x)) (Sd : K4OnD Dm m (parOf x) n)
    (Sn : K4NamedW Dm E k m (parOf x) told n)
    (hhead : ∀ s s' (a b : Fr.E.Str), LayRest s s' → SameStr Fr q.base a b → ∀ p i w,
      Dm.headPart p i (z, s') (strsOf Fr b) w → Dm.headPart p i (z, s) (strsOf Fr a) w)
    (hlk : Dm.lk m = some l)
    (st : ∀ s, StatesAt (K9.statesOfLink l) 2 (parOf x) "front" s ∧
      StatesAt (K9.statesOfLink l) 2 (parOf x) "back" s)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) :
    Nonempty (K4RowAt x linksFull (flatPlacesOf linksFull true) k m pl q (k4DataWide Dm E Bm)
      (mgWide Dm E Bm) told z) := by
  obtain ⟨seats, hsmp⟩ := Sd.smp
  obtain ⟨R, hreq⟩ := Sd.req
  have Em := k4Means_mgWide Dm E Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have Ep := k4Pile_mgWide Dm E Bm
  have hmk : ((mgWide Dm E Bm).more.rows linksFull pl).makes = [(some m, "K8.funsThird")] :=
    (door_of_fit H k4_door_full).1
  exact ⟨
    { pol := pol
      KL := KL
      layout := layout
      n := n
      rest := restNames
      Hh := VerifiableInference.Desc.K9.holesAt X (headLink X) m l
      l := l
      nO := nO
      nG := nG
      runO := runO
      runG := runG
      reads := k4Reads_at z Fr q.base (arr := Dm.arr) (mat := Dm.mat13) (R := R) (seats := seats)
        rfl Sd.dec hreq hsmp rfl (fun _ _ _ _ => rfl) hhead
      plan := k4RowPlan_wide Dm E H Sx Sd Sn
      kept := k4Kept_of_means Em Ep
      seats :=
        ⟨VerifiableInference.Desc.K9.readersAt_some Dm.lk X _ m l hlk, st, fO, oRun, fG, gRun⟩
      door := fun _ _ => door_funs Ep hmk
      doorP := fun nm hnm a => by
        rw [hmk, List.mem_singleton] at hnm
        subst hnm
        exact mgAll_pubP_said Dm (.more (some m) "K8.funsThird") a rfl }⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rowAt_wide
