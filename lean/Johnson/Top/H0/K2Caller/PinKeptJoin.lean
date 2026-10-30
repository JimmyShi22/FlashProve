-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PinKeptJoin.lean: the code switch: THE JOIN: FROM THE
LIBRARY's RELATION IN FRONT OF THE SWITCH TO THE TABLE OF JOINTS' PIN AT EVERY KEPT SEAT, at what
the table's extractor lays at a switch, at the named reader of OOD samples.
  KeptFacts    WHAT THE JOIN ASKS AT A HELD MEMBER, beside the library's relation: sixteen fields,
               on public numbers, the verifier's state and the oracles: the frame's entry kk for the
               member (there; its rows, row bits and pad are the typed shape's) · SeatWord.lean's
               KeptSeat · one answer · the rows are long enough for the pad · the new copy (there;
               the old one's main rows and row length; its pad stands where the old one's stood;
               arr GIVES THE TWO COPIES ONE NUMBER) · the state's statement has the front's
               statement's oracle messages (this file once: «is the front's»: FALSE at a place that
               stands at a link, where the front pushes a group) · the seat is one of the plan's
               list, AND ITS NUMBER THERE IS kk's OWN · the statement has the message, with a
               stored sample row, whose form reads as its coefficients · some typed seed fits it ·
               every leaf is shown
  pin_kept_join  a member x of the table's list, alike to the typed kept member, whose pad alone the
               row lays, is pinned at extAt … [] minePad false none a y w. Out of KeptDec.lean's
               pin_kept, HeldIsNamed.lean's held_is_named, smpNamed_bySeat, KeptOff.lean's
               hoff_kept and hnew_made
  pinJT_kept   THE TABLE's OWN «pin» (Johnson/Desc/Sound/MeaningSig.lean's pinJT) at a seat q at
               which a member of the table's list sits, where each member that sits there is one
               whose pad the row lays and is alike to a typed kept member with KeptFacts
WHAT IS ASKED OF THE LAW: two things on its typed witness's pair c: h (the library's clause on every
held slot: a conjunct of its relation in front) and hu (c's message is the witness's new messages
along the map of names: at the letters as this folder's files make them, by definition).
LIMITS. A JOIN OVER PREMISES: KeptFacts · Fit · two mask rows · the front's frame · the front reads
something at some position · the seats whose pads the row lays are all different. NONE IS SHOWN AT A
REAL VALUE: SO pinKept IS NOT YET PAID AT ANY PLACE OF THE PROTOCOL.
(Where this and lean/THEOREM.md differ, the page
holds.) No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.HeldIsNamed
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription Wit padB)
open VerifiableInference.Desc.Sound (ShownAt Sending Mem Alike AgreeBy seatOf numOf MsgT PinAt extAt
  msgsOf smpNamed smpNamed_bySeat numAt SitsAt pinJT agreeSeat_of_seats)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK} {Xi P : Type} (G : FileDescription Xi)
  (seat : Fin r.lo.length → ℕ × ℕ) (seatN : Fin r.l.length → ℕ × ℕ) (p : K2.P2)
  (orc : Strs → ℕ → ℕ → List UInt64) (arr : ℕ → ℕ → ℕ) (seats : List (ℕ × ℕ))

/-- **What the join asks at a held member**, beside the library's relation: all on public numbers,
the verifier's state and the oracles. -/
structure KeptFacts (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (k : {a // (plainHd r H).cl a}) (kk : KeptPlace) (xo : OnBytes.Oracle) : Prop where
  at' : W₀.kept[r.kept.idxOf k.1.1.val]? = some kk
  rows : kk.rows = (r.lo.get k.1.1).1.mainRows
  bits : kk.rowBits = ceilLog2 (r.lo.get k.1.1).1.mainRows
  pad : kk.pad = padPlaces r.cs (r.lo.get k.1.1).1
  seatIs : KeptSeat G p t fx (orc y) y kk.old (r.lo.get k.1.1).1 (seat k.1.1)
    (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a)
  one : (r.lo.get k.1.1).1.answers = 1
  fit : eachZ (r.lo.get k.1.1).1 ≤ (r.cs.base.getD (r.lo.get k.1.1).1.code default).ell
  new : ∃ ho : 1 + r.kept.idxOf k.1.1.val < r.l.length,
    (r.l.get ⟨_, ho⟩).1.mainRows = (r.lo.get k.1.1).1.mainRows ∧
    (r.cs.base.getD (r.l.get ⟨_, ho⟩).1.code default).ell =
      (r.cs.base.getD (r.lo.get k.1.1).1.code default).ell ∧
    (∀ row place, padRaw r.cs (r.l.get ⟨_, ho⟩).1 row place ↔
      padRaw r.cs (r.lo.get k.1.1).1 row place) ∧
    arr (seatN ⟨_, ho⟩).1 (seatN ⟨_, ho⟩).2 = arr (seat k.1.1).1 (seat k.1.1).2
  st : a.2.st.oracles = fx.st.oracles
  listed : seat k.1.1 ∈ seats
  num : numAt seats ⟨⟨r.lo, seat⟩, k.1.1⟩ = kk.old
  msg : fx.st.oracles[kk.old]? = some xo
  stored : xo.sampleRows.size ≠ 0
  reads : ∀ i, formAt (formOn (rowK2 r H fx.st W₀ k)) i =
    coefAt (rowK2 r H fx.st W₀ k) kk.old .main i
  fits : ∃ sd, FitsK2 r H fx.st W₀ k sd
  shown : ShownAt G r.cs r.lo seat y k.1.1

variable {Cells Tok : Type}
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells)

/-- **THE JOIN: a kept member is pinned in front of the switch.** -/
theorem pin_kept_join (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ memK rowK (plK W₀))
    (w : Wit Cells Tok MsgT) (c : (vecD (plainD r H)).Cf.N.Wit)
    (hu : ∀ j, c.1 j = (sigOf r.cs r.l).ents (msgsOf r.cs r.l seatN arr w)
      (Johnson.Top.H.iJ (plainR r H).s W₀ memK rowK (plK W₀) r.cs r.l Ft.nameJ j))
    (k : {a // (plainHd r H).cl a})
    (h : ((vecD (plainD r H)).held.o k).decW
      ((vecD (plainD r H)).held.sW k (faAt r H p orc (smpK2 r H) (t, fx, W₀) y).2.1.1)
      ((faAt r H p orc (smpK2 r H) (t, fx, W₀) y).1.1.1.2 k) =
        some ((vecD (plainD r H)).held.msg c.1 k))
    (kk : KeptPlace) (xo : OnBytes.Oracle)
    (Fk : KeptFacts G seat seatN p orc arr seats a t fx W₀ y k kk xo)
    (x : Mem) (minePad : List Mem) (hx : x ∈ minePad) (hA : Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩)
    (hS : AgreeBy r.cs G (smpNamed r.cs seats) seatOf ([] ++ minePad) a y (seatOf x)) :
    PinAt G r.cs x.1.l x.1.seat (fun b => smpNamed r.cs seats b x.1) arr x.2 a y
      (extAt r.cs G arr (smpNamed r.cs seats) decT c₀ [] minePad false none a y w) := by
  have hkk : keptK2 r H W₀ k = kk := by
    unfold keptK2
    rw [List.getD_eq_getElem?_getD, Fk.at']
    rfl
  obtain ⟨z, z1, z2, z3⟩ := held_is_named seat seats a fx W₀ k Fk.st Fk.listed
    (by rw [hkk]; exact Fk.num) (by rw [hkk]; exact Fk.bits) xo (by rw [hkk]; exact Fk.msg)
    Fk.stored (by rw [hkk]; exact Fk.reads) Fk.fits
  obtain ⟨ho, e2, e4, same, hN⟩ := Fk.new
  have hz : HEq (smpNamed r.cs seats a x.1 x.2) (some z) := by
    rw [← z1]
    exact smpNamed_bySeat r.cs seats a x ⟨⟨r.lo, seat⟩, k.1.1⟩ hA
  have esh : (x.1.l.get x.2).1 = (r.lo.get k.1.1).1 := congrArg Prod.fst hA.1
  have enum : numOf arr x = arr (seat k.1.1).1 (seat k.1.1).2 := by
    unfold numOf
    rw [show x.1.seat x.2 = seat k.1.1 from hA.2]
  refine pin_kept G seat p orc (smpK2 r H) arr (smpNamed r.cs seats) decT c₀ t fx W₀ y hm hW k kk
    Fk.at' Fk.rows q₀ h0 Fk.seatIs c h a x minePad hx hA z hz z2 z3 Fk.shown hS w ?_
  intro mask row place hin hp
  rw [esh] at hin hp
  rw [enum, ← hN]
  exact hoff_kept W₀ Ft (msgsOf r.cs r.l seatN arr w) c.1 hu k kk Fk.at' Fk.bits Fk.pad Fk.one
    Fk.fit (w.msg (arr (seatN ⟨_, ho⟩).1 (seatN ⟨_, ho⟩).2))
    (fun row place h1 h2 h3 => hnew_made seatN arr w _ ho _ e2 e4 same row place h1 h2 h3)
    mask row place hin hp

/-- **The table's pin at a kept seat**, at what the table's extractor lays at a switch. -/
theorem pinJT_kept (a : P × VerifiableInference.Desc.First.S)
    (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W₀ : SwitchFrame) (y : Strs)
    (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ memK rowK (plK W₀))
    (w : Wit Cells Tok MsgT) (c : (vecD (plainD r H)).Cf.N.Wit)
    (hu : ∀ j, c.1 j = (sigOf r.cs r.l).ents (msgsOf r.cs r.l seatN arr w)
      (Johnson.Top.H.iJ (plainR r H).s W₀ memK rowK (plK W₀) r.cs r.l Ft.nameJ j))
    (h : ∀ k, ((vecD (plainD r H)).held.o k).decW
      ((vecD (plainD r H)).held.sW k (faAt r H p orc (smpK2 r H) (t, fx, W₀) y).2.1.1)
      ((faAt r H p orc (smpK2 r H) (t, fx, W₀) y).1.1.1.2 k) =
        some ((vecD (plainD r H)).held.msg c.1 k))
    (ms minePad : List Mem) (hN : (minePad.map seatOf).Nodup) (q : ℕ × ℕ)
    (hex : ∃ x ∈ ms, SitsAt x q.1 q.2)
    (hall : ∀ x ∈ ms, SitsAt x q.1 q.2 → x ∈ minePad ∧
      ∃ (k : {a // (plainHd r H).cl a}) (kk : KeptPlace) (xo : OnBytes.Oracle),
        Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩ ∧
          KeptFacts G seat seatN p orc arr seats a t fx W₀ y k kk xo) :
    pinJT r.cs G arr (smpNamed r.cs seats) ms q.1 q.2 a y
      (extAt r.cs G arr (smpNamed r.cs seats) decT c₀ [] minePad false none a y w) := by
  refine ⟨hex, fun x hx hs => ?_⟩
  obtain ⟨hp, k, kk, xo, hA, Fk⟩ := hall x hx hs
  exact pin_kept_join G seat seatN p orc arr seats decT c₀ a t fx W₀ y hm hW q₀ h0 Ft w c hu k (h k)
    kk xo Fk x minePad hp hA
    (agreeSeat_of_seats r.cs G (smpNamed r.cs seats) ([] ++ minePad) (by simpa using hN) a y _)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pinJT_kept

#print axioms VerifiableInference.Desc.First.K2Caller.pin_kept_join
