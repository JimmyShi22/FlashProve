-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptOff.lean: the code switch: OFF THE PAD THE WITNESS BEHIND THE
SWITCH HAS, AT A KEPT MEMBER's NUMBER, THE MEMBER's PART OF THE OPEN WORD's MESSAGE: the premise
hoff of KeptDec.lean's pin_kept (pin_ext_pad), assembled out of lemmas that lie.
  hoff_kept    where the open word's message u is read off new messages n along the library's map of
               names iJ: at a row and a place of the kept member outside its pad, the member's part
               of u (as toMsgT lays it) is any table msg that the new copy's table is
               there. By heldPort_sJ (Johnson/Top/H/SwitchHeldPush.lean) and iJ_off and
               padRaw_iff_mem (Johnson/Top/H/SwitchFront.lean); padB_inl (Sound/MsgSig.lean)
  hnew_made    where the new messages are msgsOf of a witness w: the new copy's table is,
               off its pad, w.msg at the number that arr gives the new copy's seat. (Kin:
               msgs_forth, Sound/World.lean, on toMsgT)
LIMITS. AN ASSEMBLY. hoff_kept's PREMISES: Fit at the frame W₀ and the typed slots' three readings ·
hu (u is n along iJ) · W₀ lists kk at the member's place in r.kept · kk's bits of rows and pad are
the typed shape's · THE KEPT MEMBER HAS ONE ANSWER (no known test gives it) · its rows are
long enough for the pad · hnew. hnew_made's: the new copy's shape has the old one's main rows and
row length, and its pad stands where the old one's stood. THAT arr GIVES THE TWO COPIES ONE NUMBER
IS NOT SAID HERE: whoever joins the two lemmas owes it. None of the premises is shown at a real
value. pinKept IS NOT PAID. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptDec
import Johnson.Top.H.SwitchFront
import Johnson.Top.H.SwitchHeldPush

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (padB Wit)
open VerifiableInference.Desc.Sound (toMsgT InMsg MsgT padB_inl msgsOf)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK}

/-- **Off the pad the kept member's part of the open word's message is the new copy's table.** -/
theorem hoff_kept (W₀ : SwitchFrame)
    (Ft : Fit r.cs r.l (plainR r H).s W₀ memK rowK (plK W₀)) (n : (sigOf r.cs r.l).Msg)
    (u : (vecD (plainD r H)).Cf.J → GE)
    (hu : ∀ j, u j = (sigOf r.cs r.l).ents n
      (Johnson.Top.H.iJ (plainR r H).s W₀ memK rowK (plK W₀) r.cs r.l Ft.nameJ j))
    (k : {a // (plainHd r H).cl a}) (kk : KeptPlace)
    (hk : W₀.kept[r.kept.idxOf k.1.1.val]? = some kk)
    (hbits : kk.rowBits = ceilLog2 (r.lo.get k.1.1).1.mainRows)
    (hpad : kk.pad = padPlaces r.cs (r.lo.get k.1.1).1)
    (h1 : (r.lo.get k.1.1).1.answers = 1)
    (hfit : eachZ (r.lo.get k.1.1).1 ≤ (r.cs.base.getD (r.lo.get k.1.1).1.code default).ell)
    (msg : MsgT)
    (hnew : ∀ row place, row < (r.lo.get k.1.1).1.mainRows →
      place < (r.cs.base.getD (r.lo.get k.1.1).1.code default).ell →
      ¬ padRaw r.cs (r.lo.get k.1.1).1 row place →
      tabOf r.cs r.l n (1 + r.kept.idxOf k.1.1.val) false row place = msg false row place)
    (mask : Bool) (row place : ℕ) (hin : InMsg r.cs (r.lo.get k.1.1).1 mask row place)
    (hp : padB r.cs (r.lo.get k.1.1).1 mask row place = false) :
    msg mask row place =
      toMsgT r.cs r.lo k.1.1 ((vecD (plainD r H)).held.msg u k) mask row place := by
  have hz : (r.lo.get k.1.1).1.maskRows = 0 := H.h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
  cases mask with
  | true =>
    have h' : row < (r.lo.get k.1.1).1.maskRows ∧ _ := hin
    exact absurd h'.1 (by omega)
  | false =>
    have hin' : row < (r.lo.get k.1.1).1.mainRows ∧
        place < (pMain r.cs (r.lo.get k.1.1).1).ell := hin
    have hno : ¬ padRaw r.cs (r.lo.get k.1.1).1 row place := fun q => by
      have hb := (padB_inl r.cs (r.lo.get k.1.1).1 (⟨row, hin'.1⟩, ⟨place, hin'.2⟩)).2 q
      rw [show padB r.cs (r.lo.get k.1.1).1 false row place = true from hb] at hp
      cases hp
    have e := heldPort_sJ r.cs r.lo r.mem (stageOf r.g 0) r.rad (fun _ => 0) (fun _ => 0)
      (H.hM 0) (H.hZ 0) r.kp (fun a _ => a.2) H.h0 (kqOf r) k (⟨row, hin'.1⟩, ⟨place, hin'.2⟩)
    have hpl : plK W₀ (slotOf k ⟨row, hin'.1⟩) = kk := by
      unfold plK
      show W₀.kept.getD (r.kept.idxOf k.1.1.val) _ = kk
      rw [List.getD_eq_getElem?_getD, hk]
      rfl
    unfold toMsgT
    rw [if_neg (by decide), dif_pos hin']
    show msg false row place = u ((plainHd r H).sJ k (.inl (⟨row, hin'.1⟩, ⟨place, hin'.2⟩)))
    rw [show (plainHd r H).sJ k (.inl (⟨row, hin'.1⟩, ⟨place, hin'.2⟩)) = _ from e, hu]
    have hI := iJ_off Ft n (slotOf k ⟨row, hin'.1⟩)
      (Fin.cast (congrArg Fmt.M1.Code.l (H.hM 0 k.1.1 k.2.fst k.2.fst)) ⟨place, hin'.2⟩) (by
        rw [hpl, hbits, hpad]
        exact fun q => hno ((padRaw_iff_mem r.cs _ hz h1 hfit row place hin'.1 hin'.2).2 q))
    exact (hI.trans (hnew row place hin'.1 hin'.2 hno)).symm

/-- **The new copy's table is, off its pad, the witness's message at the copy's number.** -/
theorem hnew_made {Cells Tok : Type} (seatN : Fin r.l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (w : Wit Cells Tok MsgT) (o : ℕ) (ho : o < r.l.length) (so : OracleShape)
    (e2 : (r.l.get ⟨o, ho⟩).1.mainRows = so.mainRows)
    (e4 : (r.cs.base.getD (r.l.get ⟨o, ho⟩).1.code default).ell =
      (r.cs.base.getD so.code default).ell)
    (same : ∀ row place, padRaw r.cs (r.l.get ⟨o, ho⟩).1 row place ↔ padRaw r.cs so row place)
    (row place : ℕ) (hrow : row < so.mainRows)
    (hpl : place < (r.cs.base.getD so.code default).ell) (hno : ¬ padRaw r.cs so row place) :
    tabOf r.cs r.l (msgsOf r.cs r.l seatN arr w) o false row place =
      w.msg (arr (seatN ⟨o, ho⟩).1 (seatN ⟨o, ho⟩).2) false row place := by
  have h1 : row < (r.l.get ⟨o, ho⟩).1.mainRows := by rw [e2]; exact hrow
  have h2 : place < (pMain r.cs (r.l.get ⟨o, ho⟩).1).ell := by
    show place < (r.cs.base.getD (r.l.get ⟨o, ho⟩).1.code default).ell
    rw [e4]
    exact hpl
  have hb : padB r.cs (r.l.get ⟨o, ho⟩).1 false row place = false := by
    cases hq : padB r.cs (r.l.get ⟨o, ho⟩).1 false row place with
    | false => rfl
    | true =>
      exact absurd ((same row place).1
        ((padB_inl r.cs (r.l.get ⟨o, ho⟩).1 (⟨row, h1⟩, ⟨place, h2⟩)).1 hq)) hno
  unfold Johnson.Top.H.tabOf
  rw [dif_pos ho, if_neg (by decide), dif_pos ⟨h1, h2⟩]
  show w.tab r.cs (r.l.get ⟨o, ho⟩).1 (arr (seatN ⟨o, ho⟩).1 (seatN ⟨o, ho⟩).2) (seatN ⟨o, ho⟩).1
    (seatN ⟨o, ho⟩).2 false row place = _
  unfold Wit.tab
  rw [hb]
  rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hnew_made

#print axioms VerifiableInference.Desc.First.K2Caller.hoff_kept
