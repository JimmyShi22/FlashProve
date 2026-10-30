-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/HeldIsNamed.lean: the code switch: THE HELD OOD SAMPLE
IS THE TABLE OF JOINTS' OWN AT THE KEPT MEMBER's SEAT, UP TO THE SEED's VALUES: what the premises
hz, hv, ha of KeptDec.lean's pin_kept want, AT THE TYPED MEMBER, at SmpK2.lean's smpK2 and the
named reader smpNamed (Johnson/Desc/Sound/SmpNamed.lean).

Both readers choose a seed. The switch's chooses among the typed seeds that FIT the member's first
stored sample row (their rows, carried to the open word's entries, are the vector of the row's
form). The table's (Johnson/Desc/Sound/SmpNamed.lean over Johnson/Desc/K1/Law/GoodSendForms.lean's
smpAt) chooses among the seeds whose MATRIX is that row, read as a linear form on the message. The
decoder and the collision read a seed through its values alone (dec_congr, clash_congr).
  forms_of_fits  a typed seed that fits has the row's form as its matrix: K1.formsAt … = some (Z.mat
               sd). By push_held_at and heldPort_sJ (Johnson/Top/H/SwitchHeldPush.lean)
  held_named   where formsAt is a sample σ's matrix and ansAt its answers: smpNamed has a sample
               with σ's values and answers. By smpNamed_at and val_congr
  smpK2_fits   where some typed seed fits, smpK2's does
  held_is_named  THE STATEMENT
LIMITS. held_is_named's PREMISES: the state's statement HAS THE FRONT's STATEMENT's ORACLE MESSAGES
(that the two statements are one IS FALSE AT A PLACE THAT STANDS
AT A LINK: there the front pushes a group (by reading)) · the seat is one of the plan's
list · THE PLAN's NUMBER OF THE SEAT IS THE FRAME's ENTRY's OWN NUMBER OF THE MESSAGE · the
entry's row bits are the typed shape's · the statement has the message, with a stored sample row ·
the row's form reads as the row's coefficients on the main table (K2Hands/FormOnReads.lean's
stored_reads) · some typed seed fits (seedFits_of_goodS). AT THE TYPED MEMBER ⟨⟨r.lo, seat⟩,
i⟩: from there to a member of the table's own list goes smpNamed_bySeat along Alike. None
of the premises is shown at a real value. pinKept IS NOT PAID. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.KeptOff
import Johnson.Desc.Sound.SmpNamed
import Johnson.Top.H0.K2Caller.SmpK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.Sound (val_congr smpNamed smpNamed_at numAt Sending)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK}

/-- **A typed seed that fits a kept member's stored sample row has that row's form as its
matrix.** -/
theorem forms_of_fits (St : Statement) (k : {a // (plainHd r H).cl a}) (old : ℕ)
    (xo : OnBytes.Oracle) (row0 : OnBytes.Row) (hx : St.oracles[old]? = some xo)
    (hr : xo.sampleRows[0]? = some row0)
    (hreads : ∀ i, formAt (formOn row0) i = coefAt row0 old .main i)
    (sd : ((sigOf r.cs r.lo).om k.1.1).Z.D)
    (hF : ∀ u, pushTo ((plainHd r H).sJ k) (((sigOf r.cs r.lo).om k.1.1).Z.mat sd u) =
      slotVec (plainR r H).s (plainR r H).Kp memK rowK (r.kept.idxOf k.1.1.val)
        (k1 (r.lo.get k.1.1).1) (formOn row0)) :
    K1.formsAt r.cs (r.lo.get k.1.1).1 St old = some (((sigOf r.cs r.lo).om k.1.1).Z.mat sd) := by
  have hz : (r.lo.get k.1.1).1.maskRows = 0 := H.h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
  unfold K1.formsAt
  rw [hx, Option.bind_some, hr, Option.map_some]
  congr 1
  funext u j
  rcases j with x | x
  · have e1 := push_held_at r.cs r.lo r.mem (stageOf r.g 0) r.rad (fun _ => 0) (fun _ => 0)
      (H.hM 0) (H.hZ 0) r.kp (fun a _ => a.2) H.h0 (kqOf r) k
      (((sigOf r.cs r.lo).om k.1.1).Z.mat sd u) x
    have e2 := heldPort_sJ r.cs r.lo r.mem (stageOf r.g 0) r.rad (fun _ => 0) (fun _ => 0)
      (H.hM 0) (H.hZ 0) r.kp (fun a _ => a.2) H.h0 (kqOf r) k x
    have e3 := congrFun (hF u) ((plainHd r H).sJ k (.inl x))
    rw [show pushTo ((plainHd r H).sJ k) (((sigOf r.cs r.lo).om k.1.1).Z.mat sd u)
      ((plainHd r H).sJ k (.inl x)) = _ from e1] at e3
    rw [e3, show (plainHd r H).sJ k (.inl x) = _ from e2]
    show coefAt row0 old .main (x.1.val + 2 ^ k1 (r.lo.get k.1.1).1 * x.2.val) =
      if r.kept.idxOf k.1.1.val = r.kept.idxOf k.1.1.val then
        formAt (formOn row0) (x.1.val + 2 ^ k1 (r.lo.get k.1.1).1 * x.2.val) else 0
    rw [if_pos rfl, hreads]
  · exact absurd x.1.isLt (by omega)

/-- **The table's named reader of OOD samples has, at the typed kept member, a sample with the held
one's values and answers**, where the statement's first stored sample row of the member's message is
the held seed's matrix and its target the held answer. -/
theorem held_named {P : Type} (seat : Fin r.lo.length → ℕ × ℕ) (seats : List (ℕ × ℕ))
    (a : P × VerifiableInference.Desc.First.S) (i : Fin r.lo.length) (hq : seat i ∈ seats)
    (σ : ((sigOf r.cs r.lo).om i).Smp)
    (hF : K1.formsAt r.cs (r.lo.get i).1 a.2.st (numAt seats ⟨⟨r.lo, seat⟩, i⟩) =
      some (((sigOf r.cs r.lo).om i).Z.mat σ.1))
    (hA : K1.ansAt a.2.st (numAt seats ⟨⟨r.lo, seat⟩, i⟩) = some σ.2) :
    ∃ z, smpNamed r.cs seats a ⟨r.lo, seat⟩ i = some z ∧
      ((sigOf r.cs r.lo).om i).Z.val z.1 = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧ z.2 = σ.2 := by
  have g : ∃ ρ, K1.formsAt r.cs (r.lo.get i).1 a.2.st (numAt seats ⟨⟨r.lo, seat⟩, i⟩) =
      some ((portOmZ r.cs (r.lo.get i).1 (r.lo.get i).2).Z.mat ρ) := ⟨σ.1, hF⟩
  refine ⟨(g.choose, σ.2), ?_, ?_, rfl⟩
  · rw [smpNamed_at r.cs seats a ⟨r.lo, seat⟩ i hq]
    show K1.smpAt r.cs (r.lo.get i).1 (r.lo.get i).2 a.2.st _ = _
    unfold K1.smpAt
    rw [dif_pos g, hA]
    rfl
  · exact val_congr _ _ _ (Option.some.inj (g.choose_spec.symm.trans hF))

/-- Where some typed seed fits, smpK2's does. -/
theorem smpK2_fits (fx : _root_.Tw.K2.Front) (W : SwitchFrame) (k : (vecD (plainD r H)).held.K)
    (h : ∃ sd, FitsK2 r H fx.st W k sd) : FitsK2 r H fx.st W k (smpK2 r H fx W k).1 := by
  unfold smpK2
  simp only [dif_pos h]
  exact h.choose_spec

/-- **THE HELD OOD SAMPLE IS THE TABLE's**, up to the seed's values: at SmpK2.lean's smpK2 and part
5's smpNamed. -/
theorem held_is_named {P : Type} (seat : Fin r.lo.length → ℕ × ℕ) (seats : List (ℕ × ℕ))
    (a : P × VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front) (W : SwitchFrame)
    (k : {a // (plainHd r H).cl a}) (hst : a.2.st.oracles = fx.st.oracles)
    (hq : seat k.1.1 ∈ seats)
    (hnum : numAt seats ⟨⟨r.lo, seat⟩, k.1.1⟩ = (keptK2 r H W k).old)
    (hb : (keptK2 r H W k).rowBits = k1 (r.lo.get k.1.1).1)
    (xo : OnBytes.Oracle) (hx : fx.st.oracles[(keptK2 r H W k).old]? = some xo)
    (hn : xo.sampleRows.size ≠ 0)
    (hreads : ∀ i, formAt (formOn (rowK2 r H fx.st W k)) i =
      coefAt (rowK2 r H fx.st W k) (keptK2 r H W k).old .main i)
    (hfit : ∃ sd, FitsK2 r H fx.st W k sd) :
    ∃ z, smpNamed r.cs seats a ⟨r.lo, seat⟩ k.1.1 = some z ∧
      ((sigOf r.cs r.lo).om k.1.1).Z.val z.1 =
        ((sigOf r.cs r.lo).om k.1.1).Z.val (smpK2 r H fx W k).1 ∧
      z.2 = (smpK2 r H fx W k).2 := by
  have h0 : 0 < xo.sampleRows.size := Nat.pos_of_ne_zero hn
  have hrow : xo.sampleRows[0]? = some (rowK2 r H fx.st W k) := by
    unfold rowK2 samplesOf
    rw [Array.getD_eq_getD_getElem?, hx, Option.getD_some, List.getD_eq_getElem?_getD,
      Array.getElem?_toList, Array.getElem?_eq_getElem h0]
    rfl
  have hF := smpK2_fits fx W k hfit
  unfold FitsK2 at hF
  rw [hb] at hF
  refine held_named seat seats a k.1.1 hq (smpK2 r H fx W k) ?_ ?_
  · rw [hnum]
    have e := forms_of_fits fx.st k _ xo _ hx hrow hreads _ hF
    unfold K1.formsAt at e ⊢
    rw [hst]
    exact e
  · rw [hnum]
    unfold K1.ansAt
    rw [hst, hx, Option.bind_some, hrow]
    rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.held_is_named

#print axioms VerifiableInference.Desc.First.K2Caller.held_named

#print axioms VerifiableInference.Desc.First.K2Caller.forms_of_fits
