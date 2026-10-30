-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerPays.lean: PREMISES OF THE ONE TERM (share_row,
Johnson/Desc/K14/Law/LedgerRow.lean) PAID AT OTHER FILES' FILLINGS: smp₂ := smpSt cs oNo stSh
(K1's reading smpAt at the member's number in the chain's statement:
Johnson/Desc/Sound/SmpShared.lean) · X ⊇ bookX ft (the book in order, the first mask noted:
Johnson/Desc/Sound/BookX.lean). AND THE NEW MESSAGES' NUMBERS behind the two sendings.

  smpReads_smpSt  hsm: smpSt reads the record through its messages' shapes, marks and sample rows.
  x_of_on         inside the promise with XX laid beside the book-keeping, XX holds of the record.
  bookX_hands     hX2 … hX6, hX8, bookX's part: a piece that holds, in the wrap, a block which
                  decides as the i-th of the kind's eight hands bookX on from i + 1 to i + 2.
  bookX_zeta, bookX_last   hX7, hX11, bookX's part: over all records.
  num_at_sends    at a yes of a sending "the record's size behind, less the place's messages, and k"
                  (K1's law's term for the k-th new message's number) is the size in front and k.
  number_two, number_five   so, at the pieces, inside the promise: nU + k, nO + k: what
                  smp_of_number (SendSeam.lean) asks (hnum) at a reading by fixed numbers.
  keep5_paid      **hkeep5**, in five_core's own form, at smpSt, from one fact on the plan's letter
                  oNo: a member that sits at o_u's seat bears o_u's number.
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRow
import Johnson.Desc.Sound.BookX
import Johnson.Desc.Sound.SmpShared
import Johnson.Desc.Sound.HeldShift
import Johnson.Desc.Sound.FenceK14Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.K1 (sendPiece SameMsgs shapesOf)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence (bookX bookX_iff bookX_k14 bookX_end)

/-- hsm at smpSt. -/
theorem smpReads_smpSt (cs : OnBytes.Codes) (oNo : Mem → ℕ) : SmpReads (smpSt cs oNo stSh) := by
  intro s s' hm _
  funext S i
  exact smpAt_congr cs _ _ s.st s'.st _ (hm.2 _)

/-- bookX's part of hX7. -/
theorem bookX_zeta (ft : ℕ) (s : St) (z : List E) (h : bookX ft 7 s = true) :
    bookX ft 8 { s with loc := { s.loc with zFd := z } } = true := by
  rcases (bookX_iff ft 7 s).1 h with h | ⟨h1, h2⟩
  · omega
  · exact (bookX_iff ft 8 _).2 (Or.inr ⟨h1, Or.inr (h2.resolve_left (by omega))⟩)

/-- bookX's part of hX11. -/
theorem bookX_last (ft : ℕ) (s : St) (h : bookX ft 11 s = true) : bookX ft 12 s = true :=
  bookX_end ft s h

variable {P₁ Cl Xi Cells Tok : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (bkR : TreeBook → TreeBook) (N : NumbersS) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  (n nU nO : ℕ)
  (p : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (Q : P14) (XX : ℕ → St → Bool)

/-- Inside the promise with XX beside the book-keeping, XX holds of the record. -/
theorem x_of_on (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (pmI decT₂ Pm₀ Q.par n nU nO)) XX) Oc true p l k a) : XX k a.1.2 = true :=
  ((promQ_beside N _ true p l XX k _).1 ha.1).2

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
include hbl

/-- **bookX is handed on** by a piece that holds, in the wrap, a block which decides as the i-th of
the kind's eight. -/
theorem bookX_hands (hm : Q.par.S.masksAhead = true) (i : ℕ) (b : Block St Unit)
    (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (c : Block St Cl) (hc : DecidesAs c b)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y)
    (h : bookX Q.par.toGPar.firstTree (i + 1) a.1.2 = true) :
    bookX Q.par.toGPar.firstTree (i + 2) y.1.2 = true := by
  obtain ⟨rs, gs, hd⟩ := held_yes x c hx a τ y hout
  rw [hc] at hd
  exact bookX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hm i b hb _ _ rs gs hd h

/-- **The new messages' numbers**: at a yes of a sending the k-th of its messages bears the number
    "the
record's size behind, less the place's messages, and k" (K1's law's term): that is the size in front
and k. -/
theorem num_at_sends (sentU : Array OracleNotice) (hU : withU Q.S = some sentU) :
    (∀ d rs gs d', b2.decide d rs gs = .ok d' → ∀ k : ℕ,
      d'.st.oracles.size - (shapesOf (parU Q sentU)).length + k = d.st.oracles.size + k) ∧
    ∀ d rs gs d', b5.decide d rs gs = .ok d' → ∀ k : ℕ,
      d'.st.oracles.size - (shapesOf (parO Q)).length + k = d.st.oracles.size + k := by
  obtain ⟨u, hu, e2, e5⟩ := Fence.blocks_two Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl := Option.some.inj (hu.symm.trans hU)
  have len : ∀ K : VerifiableInference.Desc.K1.Par, (shapesOf K).length = K.sent.size := fun K => by
    simp [shapesOf]
  constructor
  · intro d rs gs d' h k
    rw [e2] at h
    obtain ⟨lay, _, _, hs, _⟩ := Fence.sendAt_received Q _ _ _ _ _ (Fence.behindU_book Q.par) d d'
        rs
      gs h
    have hs' : d'.st.oracles.size = d.st.oracles.size + (parU Q u).sent.size := hs
    rw [len, hs']
    omega
  · intro d rs gs d' h k
    rw [e5] at h
    obtain ⟨lay, _, _, hs, _⟩ := Fence.sendAt_received Q _ _ _ _ _ (Fence.behindOmega_book Q.par) d
        d'
      rs gs h
    have hs' : d'.st.oracles.size = d.st.oracles.size + (parO Q).sent.size := hs
    rw [len, hs']
    omega

/-- **At the pieces, inside the promise**: nU + k behind "send o_u", nO + k behind "send o_omega":
    what
smp_of_number (SendSeam.lean) asks (hnum) at a reading by fixed numbers (its smpByNumber;
smpSt: one term). -/
theorem number_two (sentU : Array OracleNotice) (hU : withU Q.S = some sentU) (c2 : Block St Cl)
    (h2c : DecidesAs c2 b2) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hx : x.b = heldW c2) (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (y : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (pmI decT₂ Pm₀ Q.par n nU nO)) XX) Oc true p l 2 a)
    (hout : x.ior.red.out a τ = some y) (k : ℕ) :
    y.1.2.st.oracles.size - (shapesOf (parU Q sentU)).length + k = nU + k := by
  obtain ⟨rs, gs, hd⟩ := held_yes x c2 hx a τ y hout
  rw [h2c] at hd
  have h2 : (pmI decT₂ Pm₀ Q.par n nU nO).shape 2 a.1.2 = true :=
    ((promQ_beside N _ true p l XX 2 _).1 ha.1).1 (.shape 2) (by simp [promsAt])
  rw [pmI_shape0 decT₂ Pm₀ Q.par n nU nO 2 (by decide)] at h2
  have hs := ((midB_iff nU a.1.2).1 ((shapeP_iff Q.par nU a.1.2).1 h2).2.2.2).1
  rw [(num_at_sends Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU).1 _ rs gs _ hd k, hs]

theorem number_five (sentU : Array OracleNotice) (hU : withU Q.S = some sentU) (c5 : Block St Cl)
    (h5c : DecidesAs c5 b5) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hx : x.b = heldW c5) (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (y : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP (promSigS cs G smp₂ ms (fun s : St => s.st) (fun s : St => bkR s.book)
      (pmI decT₂ Pm₀ Q.par n nU nO)) XX) Oc true p l 5 a)
    (hout : x.ior.red.out a τ = some y) (k : ℕ) :
    y.1.2.st.oracles.size - (shapesOf (parO Q)).length + k = nO + k := by
  obtain ⟨rs, gs, hd⟩ := held_yes x c5 hx a τ y hout
  rw [h5c] at hd
  have h5 : (pmI decT₂ Pm₀ Q.par n nU nO).shape 5 a.1.2 = true :=
    ((promQ_beside N _ true p l XX 5 _).1 ha.1).1 (.shape 5) (by simp [promsAt])
  rw [pmI_shape0 decT₂ Pm₀ Q.par n nU nO 5 (by decide)] at h5
  have hs := ((midB_iff nO a.1.2).1 ((shapeM_iff Q.par nU nO _ a.1.2).1 h5).2).1
  rw [(num_at_sends Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU).2 _ rs gs _ hd k, hs]

/-- **hkeep5, paid**: in five_core's own form, at smp₂ := smpSt. -/
theorem keep5_paid (oNo : Mem → ℕ)
    (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
    (c5 : Block St Cl) (h5c : DecidesAs c5 b5) (base : ℕ) (d₁ d₂ : RDT)
    (ext₀ : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT) (err₀ : Err (uLT (ckP .two) [d₁, d₂])) :
    ∀ a τ y, onQ₂ N (besideP (promSigS cs G (smpSt cs oNo stSh) ms (fun s : St => s.st)
        (fun s : St => bkR s.book) (pmI decT₂ Pm₀ Q.par n nU nO)) XX) Oc true p l 5 a →
      (pc2 c5 base d₁ d₂ ext₀ err₀).ior.red.out a τ = some y →
      ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
        smpSt cs oNo stSh y.1.2 z.1 z.2 = smpSt cs oNo stSh a.1.2 z.1 z.2 := by
  intro a τ y ha hout
  obtain ⟨rs, gs, hd⟩ := held_yes (pc2 c5 base d₁ d₂ ext₀ err₀) c5 rfl a τ y hout
  rw [h5c] at hd
  have ha0 := ((promQ_beside N _ true p l XX 5 _).1 ha.1).1
  have h5 : (pmI decT₂ Pm₀ Q.par n nU nO).shape 5 a.1.2 = true := ha0 (.shape 5) (by simp [promsAt])
  rw [pmI_shape0 decT₂ Pm₀ Q.par n nU nO 5 (by decide)] at h5
  obtain ⟨_, sA, eN, _⟩ :=
    (shapeU_iff Q.par nU _ a.1.2).1 ((shapeM_iff Q.par nU nO _ a.1.2).1 h5).1
  have hlt : nU < a.1.2.st.oracles.size := by
    rw [← eN]
    exact noted_of_seatedUB Q.par a.1.2 sA
  exact fun z hz hs => smpSt_k14 cs oNo Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b5 (by simp) _ _ rs gs hd z
    (by rw [hoU z hz hs]; exact hlt)

end Desc.K14.Law

#print axioms Desc.K14.Law.smpReads_smpSt
#print axioms Desc.K14.Law.bookX_zeta
#print axioms Desc.K14.Law.x_of_on
#print axioms Desc.K14.Law.bookX_hands
#print axioms Desc.K14.Law.num_at_sends
#print axioms Desc.K14.Law.number_two
#print axioms Desc.K14.Law.number_five
#print axioms Desc.K14.Law.keep5_paid
