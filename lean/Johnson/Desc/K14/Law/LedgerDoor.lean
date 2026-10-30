-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerDoor.lean: WHAT THE LAST CHAIN's DOOR ASKS OF THE SHARED CHAIN's END,
LAID BESIDE THE FILLING OF RECORD AND PAID AT THE LAST BLOCK. The row
SH₃ wants the shared chain's promise to hold, at its last border, the door's own text doorSharedB p
(Johnson/Desc/Last/DoorTexts.lean: five tests on the record: the statement is in order · the book
fits · Omega is part 0 of its tree · Omega is there with the plan's shape · it has one sample row).
HERE: a LAYER over XK (Johnson/Desc/K14/Law/LedgerNineTen.lean), whose own statements do not turn.

  XD, XW          XD p k s := fitsX k s && doorX p 12 k s (two tests); XW := XK &&
                  XD: **XK with the door**: to be laid in pmK's slot X in XK's place.
  door_of_record  **the door's text at the chain's last record, from XK 12 and fitsX 12**: by
                  doorSharedB_of_parts: in order from tidY · the book's two from
                  door_two_three · Omega's two from omY, with d.loc.oOmega = the
                  plan's number (sharedX_twelve).
  XK_last, XW_last   **the last step's price, paid**: from border 11 to border 12, at one record.
  XW_first, XW_front, XW_point, handsAt_XW   the walk of XW, as XK's: the first record by make · the
                  front · "LIN point" at the piece · HandsAt, as share_filled | share_seamed ask it.
  pmW_is, nine_at_W, ten_at_W   our promise at XW is our promise at XK with XD beside, as terms; the
                  clauses at blocks 9 and 10 at XW FROM the clauses at XK (nine_at_K | ten_at_K), by
                  clause_beside and fitsX_onGu | fitsX_onGomega.
WHAT STAYS. hpS (the door's plan's shape for Omega is the sending's first message's: with
shape_omega an equation p.S.omega = Q.par.S.omega between two plans' letters) · h1a (that shape has
one answer: one_answer from K1's condition) · hO (the sending has a message) · what handsAt_XK asks.
That 12 IS the table's last border 1 + T.l₂.length: a length of the seated row.
What is not claimed. NO MEMBER IS SHOWN. It closes no row. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.LedgerNineTen
import Johnson.Desc.Sound.BookFitsCarried
import Johnson.Desc.Last.ShapeDoorParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit Grows)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Third (P₁₄)
open VerifiableInference.Desc.Last (doorSharedB doorX doorSharedB_of_parts)
open Desc.K14.Law.Fence

/-- **What is laid over the filling of record for the last chain's door**: the book fits
(fitsX), and at the chain's last border, 12, the door's own text on the shared chain's end
(doorX). -/
def XD (p : P₁₄) : ℕ → St → Bool := fun k s => fitsX k s && doorX p 12 k s

theorem XD_iff (p : P₁₄) (k : ℕ) (s : St) : XD p k s = true ↔
    fitsX k s = true ∧ (k ≠ 12 ∨ doorSharedB p s = true) := by
  unfold XD doorX
  rw [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]

/-- Away from the last border XD is fitsX. -/
theorem XD_off (p : P₁₄) (k : ℕ) (hk : k ≠ 12) (s : St) (h : fitsX k s = true) :
    XD p k s = true := (XD_iff p k s).2 ⟨h, Or.inl hk⟩

variable (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool)) (nO : ℕ) (p : P₁₄)

/-- **XK with the door.** -/
def XW : ℕ → St → Bool := fun k s => XK Q sentU layU layO sO nO k s && XD p k s

theorem XW_iff (k : ℕ) (s : St) : XW Q sentU layU layO sO nO p k s = true ↔
    XK Q sentU layU layO sO nO k s = true ∧ XD p k s = true := by
  unfold XW
  rw [Bool.and_eq_true]

/-- **THE DOOR's TEXT AT THE CHAIN's LAST RECORD, FROM WHAT THE PROMISE HOLDS THERE.** -/
theorem door_of_record (hpS : p.S.omega = sO.2.1) (h1a : sO.2.1.answers = 1)
    (hnO : nO = sentU.size) (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
    (hO : 0 < (withOmega Q.S).size) (d : St) (hX : XK Q sentU layU layO sO nO 12 d = true)
    (hF : fitsX 12 d = true) : doorSharedB p d = true := by
  obtain ⟨g1, _, g3, g4, _, _, _⟩ := (XK_iff Q nO sO sentU layU layO 12 d).1 hX
  obtain ⟨_, e, _, _⟩ := sharedX_twelve Q sentU layU layO d hO g1
  obtain ⟨y, hy, hs, _, hr⟩ := ((omY_iff sO.2.1 nO 12 d).1 g3).resolve_left (by omega)
  refine doorSharedB_of_parts (OnBytes.Means.inOrderB_of (tidY_order 12 d g4))
    (fun ψ => door_two_three Q sentU layU layO Q.codes hlO hO d g1 hF ψ) ⟨y, ?_, ?_, ?_⟩
  · rw [e, ← hnO]
    exact hy
  · rw [hs, hpS]
  · rw [hr, h1a]

/-- XK from border 11 to border 12, at one record. -/
theorem XK_last (hY : ∀ s, sO.2.2.2 11 s = true → sO.2.2.2 12 s = true) (s : St)
    (h : XK Q sentU layU layO sO nO 11 s = true) :
    XK Q sentU layU layO sO nO 12 s = true := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := (XK_iff Q nO sO sentU layU layO 11 s).1 h
  exact (XK_iff Q nO sO sentU layU layO 12 s).2 ⟨sharedX_end Q sentU layU layO s g1, g2,
    (omY_iff _ _ 12 s).2 (Or.inr (((omY_iff _ _ 11 s).1 g3).resolve_left (by omega))), g4,
    (msgY_iff _ _ _ 12 s).2 (Or.inr (((msgY_iff _ _ _ 11 s).1 g5).resolve_left (by omega))),
    (msgY_iff _ _ _ 12 s).2 (Or.inr (((msgY_iff _ _ _ 11 s).1 g6).resolve_left (by omega))),
    hY s g7⟩

/-- **The last step's price, paid**: XW from border 11 to border 12, at one record. -/
theorem XW_last (hpS : p.S.omega = sO.2.1) (h1a : sO.2.1.answers = 1) (hnO : nO = sentU.size)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (hO : 0 < (withOmega Q.S).size)
    (hY : ∀ s, sO.2.2.2 11 s = true → sO.2.2.2 12 s = true) (s : St)
    (h : XW Q sentU layU layO sO nO p 11 s = true) : XW Q sentU layU layO sO nO p 12 s = true := by
  obtain ⟨h1, h2⟩ := (XW_iff Q sentU layU layO sO nO p 11 s).1 h
  have hK := XK_last Q sentU layU layO sO nO hY s h1
  have hF : fitsX 12 s = true := ((XD_iff p 11 s).1 h2).1
  exact (XW_iff Q sentU layU layO sO nO p 12 s).2 ⟨hK, (XD_iff p 12 s).2 ⟨hF,
    Or.inr (door_of_record Q sentU layU layO sO nO p hpS h1a hnO hlO hO s hK hF)⟩⟩

/-- At the chain's first record; over the front. -/
theorem XW_first (key : TableKey) (hY : sO.2.2.2 0 (first Q.codes key) = true) :
    XW Q sentU layU layO sO nO p 0 (first Q.codes key) = true :=
  (XW_iff Q sentU layU layO sO nO p 0 _).2 ⟨XK_first Q nO sO sentU layU layO key hY,
    XD_off p 0 (by omega) _ (fitsX_first Q.codes key)⟩

theorem XW_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hY : ∀ s, sO.2.2.2 0 s = true → sO.2.2.2 1 s = true)
    (hx : XW Q sentU layU layO sO nO p 0 d = true) : XW Q sentU layU layO sO nO p 1 d' = true := by
  obtain ⟨h1, h2⟩ := (XW_iff Q sentU layU layO sO nO p 0 d).1 hx
  exact (XW_iff Q sentU layU layO sO nO p 1 d').2 ⟨XK_front Q nO sO sentU layU layO c d d' rs gs h
      hY h1,
    XD_off p 1 (by omega) _ (fitsX_front c d d' rs gs h ((XD_iff p 0 d).1 h2).1)⟩

variable {Cells : Type} (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pm₁ : PromMeaning St) (n nU : ℕ)
  (cs : Codes) {Xi P₁ Cl Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr (P₁ ×
      St) Cl (Wit Cells Tok MsgT)))
  (e₀ : ℕ → ActV St Fr → Wit Cells Tok MsgT → Wit Cells Tok MsgT)

/-- **Our promise at XW is our promise at XK with XD laid beside**: as terms. -/
theorem pmW_is : (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XW Q sentU
    layU layO sO nO p)) = besideP (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU
    nO Q (XK Q sentU layU layO sO nO)) (XD p) := by
  have e : (fun (k : ℕ) (s : St) => (pmI decT₂ Pm₁ Q.par n nU nO).shape k s &&
        (layX Q k s && (XK Q sentU layU layO sO nO k s && XD p k s))) =
      fun k s => ((pmI decT₂ Pm₁ Q.par n nU nO).shape k s &&
        (layX Q k s && XK Q sentU layU layO sO nO k s)) && XD p k s := by
    funext k s
    cases (pmI decT₂ Pm₁ Q.par n nU nO).shape k s <;> cases layX Q k s <;>
      cases XK Q sentU layU layO sO nO k s <;> cases XD p k s <;> rfl
  show PromMeaning.mk _ _ _ _ _ _ = PromMeaning.mk _ _ _ _ _ _
  exact congrArg (fun sh => PromMeaning.mk _ _ _ _ sh _) e

/-- Inside the promise at XW: XD. -/
theorem door_of_on (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XK
        Q sentU layU layO sO nO)) (XD p)) Oc true f l k a) : XD p k a.1.2 = true :=
  ((promQ_beside N _ true f l (XD p) k _).1 ha.1).2

/-- **The clause at block 9 at XW**, from the clause at XK. -/
theorem nine_at_W (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (ε : Err (uLT (ckP .two) x.ds))
    (h : ClauseAt N Mg (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XK Q
        sentU layU layO sO nO)) Oc true f l e₀ 9 x ε) :
    ClauseAt N Mg (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XW Q sentU
        layU layO sO nO p)) Oc true f l e₀ 9 x ε := by
  rw [pmW_is]
  refine clause_beside N Mg _ Oc true f l e₀ (XD p) 9 x ε (fun a τ b ha hout => ?_) h
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  exact XD_off p 10 (by omega) _ (fitsX_onGu π he ha1 9 10 _ _ rs gs hd ((XD_iff p 9 _).1
    (door_of_on Q sentU layU layO sO nO p decT₂ Pm₁ n nU cs G ms N Oc oNo f l 9 a ha)).1)

/-- **The clause at block 10 at XW**, from the clause at XK. -/
theorem ten_at_W (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (ε : Err (uLT (ckP .two) x.ds))
    (h : ClauseAt N Mg (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XK Q
        sentU layU layO sO nO)) Oc true f l e₀ 10 x ε) :
    ClauseAt N Mg (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XW Q sentU
        layU layO sO nO p)) Oc true f l e₀ 10 x ε := by
  rw [pmW_is]
  refine clause_beside N Mg _ Oc true f l e₀ (XD p) 10 x ε (fun a τ b ha hout => ?_) h
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  exact XD_off p 11 (by omega) _ (fitsX_onGomega π he ha1 10 11 _ _ rs gs hd ((XD_iff p 10 _).1
    (door_of_on Q sentU layU layO sO nO p decT₂ Pm₁ n nU cs G ms N Oc oNo f l 10 a ha)).1)

section walk
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hUw : withU Q.S = some sentU)
  (hlU : layTrees Q.codes sentU = some layU) (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
  (hS : Q.S.sharedSplitNeeded = true) (hm : Q.par.S.masksAhead = true)
  (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)

include hbl hUw hlU hlO hS hm hp

/-- **"LIN point"**, at the piece. -/
theorem XW_point (c1 : Block St Cl) (hc : DecidesAs c1 b1) (hr : c1.rounds = b1.rounds)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c1) (a : (P₁ × St)
        × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (hY : sO.2.2.2 2 y.1.2 = true)
    (h : XW Q sentU layU layO sO nO p 1 a.1.2 = true) :
    XW Q sentU layU layO sO nO p 2 y.1.2 = true := by
  obtain ⟨h1, h2⟩ := (XW_iff Q sentU layU layO sO nO p 1 _).1 h
  obtain ⟨rs, gs, hd⟩ := held_yes x c1 hx a τ y hout
  rw [hc] at hd
  exact (XW_iff Q sentU layU layO sO nO p 2 _).2
    ⟨XK_point Q nO sO sentU layU layO b1 b2 b3 b4 b5 b6 b7 b8 hbl hUw hlU hlO hS hm hp c1 hc hr x hx
        a τ
        y hout hY h1,
      XD_off p 2 (by omega) _ (fitsX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b1 (by simp) 1 2 _ _ rs gs hd
        ((XD_iff p 1 _).1 h2).1)⟩

/-- **The kind's other seven and the end: HandsAt for XW.** -/
theorem handsAt_XW (on : ℕ → (P₁ × St) × Fr.E.Str → Prop)
    (hU0 : 0 < (shapesOf (parU Q sentU)).length) (hkU : sampledAt (parU Q sentU) ⟨0, hU0⟩)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩)
    (h1 : 1 < (shapesOf (parO Q)).length) (hkS : sampledAt (parO Q) ⟨1, h1⟩)
    (hpS : p.S.omega = shapeAt (parO Q) ⟨0, h0⟩) (h1a : (shapeAt (parO Q) ⟨0, h0⟩).answers = 1)
    (hO : 0 < (withOmega Q.S).size) (Y : ℕ → St → Bool)
    (hY : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8] Y)
    (hon : ∀ k a, on k a → XW Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, hU0⟩,
      shapeAt (parO Q) ⟨0, h0⟩, shapeAt (parO Q) ⟨1, h1⟩, Y) sentU.size p k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      (XW Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, hU0⟩, shapeAt (parO Q) ⟨0, h0⟩,
        shapeAt (parO Q) ⟨1, h1⟩, Y) sentU.size p) := by
  have hK := handsAt_XK (Cl := Cl) (Cells := Cells) (Tok := Tok) Q sentU layU layO b1 b2 b3 b4 b5 b6
    b7 b8 hbl hUw hlU hlO hS hm hp on hU0 hkU h0 hk h1 hkS Y hY
    fun k a ha => ((XW_iff Q sentU layU layO _ _ p k _).1 (hon k a ha)).1
  refine ⟨fun i b hi hb c hc hr x hx a τ y ha hout => ?_, fun s z h => ?_, fun s h =>
    XW_last Q sentU layU layO _ _ p hpS h1a rfl hlO hO hY.last s h⟩
  · obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
    rw [hc] at hd
    have hi8 : i < 8 := by
      have := (List.getElem?_eq_some_iff.1 hb).1
      simpa using this
    exact (XW_iff Q sentU layU layO _ _ p (i + 2) _).2 ⟨hK.step i b hi hb c hc hr x hx a τ y ha
        hout,
      XD_off p (i + 2) (by omega) _ (fitsX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b
        (List.mem_of_getElem? hb) (i + 1) (i + 2) _ _ rs gs hd
        ((XD_iff p (i + 1) _).1 ((XW_iff Q sentU layU layO _ _ p (i + 1) _).1 (hon _ a ha)).2).1)⟩
  · obtain ⟨g1, g2⟩ := (XW_iff Q sentU layU layO _ _ p 7 s).1 h
    exact (XW_iff Q sentU layU layO _ _ p 8 _).2 ⟨hK.zeta s z g1,
      XD_off p 8 (by omega) _ ((XD_iff p 7 s).1 g2).1⟩

end walk

end Desc.K14.Law

#print axioms Desc.K14.Law.pmW_is
#print axioms Desc.K14.Law.nine_at_W
#print axioms Desc.K14.Law.ten_at_W
#print axioms Desc.K14.Law.XW_point
#print axioms Desc.K14.Law.handsAt_XW
#print axioms Desc.K14.Law.door_of_record
#print axioms Desc.K14.Law.XW_last
#print axioms Desc.K14.Law.XW_first
#print axioms Desc.K14.Law.XW_front
