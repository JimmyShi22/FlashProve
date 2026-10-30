-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptDec.lean: the code switch: FROM THE LIBRARY's CLAUSE ON A HELD
SLOT TO THE TABLE OF JOINTS' PIN AT THE KEPT MEMBER's SEAT, at what the table's extractor lays at a
switch.
  kept_dec     the library's clause «the held slot of the open word decodes, with its held OOD
               sample, to its part of the open word's message», at CarryK2.lean's made open word,
               IS: the kept member's own committed word, as the table's reader makes it, decodes
               with that sample to that part. By SlotWord.lean's slot_word and the library's
               dec_eq_decW
  pin_kept     THE STATEMENT: a member x of the table's list that is alike to the typed kept member
               (one shape with radius, one seat) and whose pad alone the row lays is PINNED at extAt
               … [] minePad … w. By dec_congr (Sound/Seed.lean: the decoder reads a seed
               through the sample map's values alone), dec_of_alike (Sound/PinMove.lean) and
               pin_ext_pad (Sound/World.lean)
  held_is_table  where the table's reader of OOD samples is smpOf forms ans
               (Sound/Seed.lean): AT THE TYPED KEPT MEMBER ⟨⟨r.lo, seat⟩, i⟩ it has a sample z with
               hv and ha, from TWO EQUATIONS: «forms» there is the held sample's matrix, «ans» its
               answers. (pin_kept's hz speaks of the TABLE's member x: from here to there goes part
               5's SmpBySeat along Alike: not in this file)
LIMITS. pin_kept's PREMISES, beside slot_word's six and the library's clause h: x is one of the
members whose pads the row lays · Alike · THE TABLE's OOD SAMPLE AT x IS THE HELD ONE UP TO THE
SEED's VALUES (hz, hv, ha) · every leaf is shown (hSh) · the members at one seat decode alike (hS) ·
hoff: OFF THE PAD THE WITNESS BEHIND HAS, AT THE MEMBER's NUMBER, THE PART OF THE OPEN WORD's
MESSAGE: that is where the law's relation must tie its typed witness to the chain's: NOT SHOWN HERE.
None of the premises is shown at a real value. pinKept IS NOT PAID. No soundness is claimed.

-/
import Johnson.Top.H0.K2Caller.SlotWord
import Johnson.Desc.Sound.PinMove
import Johnson.Desc.Sound.Seed
import Cb.Req1.LdSegProofsFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc (Wit padB)
open VerifiableInference.Desc.Sound (wordAt wordsOf ShownAt decAt toMsgT Sending Mem Alike AgreeBy
  seatOf numOf InMsg MsgT PinAt extAt pin_ext_pad dec_of_alike dec_congr smpOf smpOf_of seedIs_val)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK} {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (p : K2.P2) (orc : Strs → ℕ → ℕ → List UInt64)
  (smp : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r H)).held.Smp)

/-- **The kept member's own committed word decodes.** -/
theorem kept_dec (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (W₀ : SwitchFrame) (y : Strs) (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (k : {a // (plainHd r H).cl a}) (kk : KeptPlace)
    (hk : W₀.kept[r.kept.idxOf k.1.1.val]? = some kk)
    (hr : kk.rows = (r.lo.get k.1.1).1.mainRows)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (K : KeptSeat G p t fx (orc y) y kk.old (r.lo.get k.1.1).1 (seat k.1.1)
      (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a))
    (c : (vecD (plainD r H)).Cf.N.Wit)
    (h : ((vecD (plainD r H)).held.o k).decW
      ((vecD (plainD r H)).held.sW k (faAt r H p orc smp (t, fx, W₀) y).2.1.1)
      ((faAt r H p orc smp (t, fx, W₀) y).1.1.1.2 k) = some ((vecD (plainD r H)).held.msg c.1 k)) :
    ((sigOf r.cs r.lo).om k.1.1).dec (wordsOf G r.cs r.lo seat y k.1.1) (smp fx W₀ k) =
      some ((vecD (plainD r H)).held.msg c.1 k) := by
  rw [OMsg.dec_eq_decW]
  show ((sigOf r.cs r.lo).om k.1.1).decW
    (((sigOf r.cs r.lo).om k.1.1).upW (wordAt G r.cs r.lo seat y k.1.1)) _ = _
  rw [← slot_word G seat p orc smp t fx W₀ y hm hW k kk hk hr q₀ h0 K]
  exact h

variable {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smpT : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells)

/-- **A kept member is pinned at what the table's extractor lays at a switch.** -/
theorem pin_kept (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (W₀ : SwitchFrame) (y : Strs) (hm : fx.f.rows.masks = 2) (hW : K2.frameAt fx = some W₀)
    (k : {a // (plainHd r H).cl a}) (kk : KeptPlace)
    (hk : W₀.kept[r.kept.idxOf k.1.1.val]? = some kk)
    (hr : kk.rows = (r.lo.get k.1.1).1.mainRows)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (K : KeptSeat G p t fx (orc y) y kk.old (r.lo.get k.1.1).1 (seat k.1.1)
      (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a))
    (c : (vecD (plainD r H)).Cf.N.Wit)
    (h : ((vecD (plainD r H)).held.o k).decW
      ((vecD (plainD r H)).held.sW k (faAt r H p orc smp (t, fx, W₀) y).2.1.1)
      ((faAt r H p orc smp (t, fx, W₀) y).1.1.1.2 k) = some ((vecD (plainD r H)).held.msg c.1 k))
    (a : A) (x : Mem) (minePad : List Mem) (hx : x ∈ minePad)
    (hA : Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩)
    (z : ((sigOf r.cs r.lo).om k.1.1).Smp) (hz : HEq (smpT a x.1 x.2) (some z))
    (hv : ((sigOf r.cs r.lo).om k.1.1).Z.val z.1 =
      ((sigOf r.cs r.lo).om k.1.1).Z.val (smp fx W₀ k).1) (ha : z.2 = (smp fx W₀ k).2)
    (hSh : ShownAt G r.cs r.lo seat y k.1.1)
    (hS : AgreeBy r.cs G smpT seatOf ([] ++ minePad) a y (seatOf x))
    (w : Wit Cells Tok MsgT)
    (hoff : ∀ mask row place, InMsg r.cs (x.1.l.get x.2).1 mask row place →
      padB r.cs (x.1.l.get x.2).1 mask row place = false →
        w.msg (numOf arr x) mask row place =
          toMsgT r.cs r.lo k.1.1 ((vecD (plainD r H)).held.msg c.1 k) mask row place) :
    PinAt G r.cs x.1.l x.1.seat (fun b => smpT b x.1) arr x.2 a y
      (extAt r.cs G arr smpT decT c₀ [] minePad false none a y w) :=
  pin_ext_pad r.cs G arr smpT decT c₀ [] minePad false none a y w x hx _
    (dec_of_alike r.cs G smpT x ⟨r.lo, seat⟩ k.1.1 hA a y z hz hSh _
      (by
        have e := kept_dec G seat p orc smp t fx W₀ y hm hW k kk hk hr q₀ h0 K c h
        obtain ⟨z1, z2⟩ := z
        obtain rfl : z2 = (smp fx W₀ k).2 := ha
        exact (dec_congr _ _ z1 (smp fx W₀ k).1 _ hv).trans e))
    hS (by simp) hoff

/-- **The held OOD sample is the table's, up to the seed's values**, where the table's reader of
samples is Sound.smpOf forms ans and the two letters have, at the typed kept member, the held
sample's matrix and answers. -/
theorem held_is_table {A : Type}
    (forms : A → (s : Sending) → (i : Fin s.l.length) →
      Option (((sigOf r.cs s.l).om i).Z.S → ((sigOf r.cs s.l).om i).C.J → GE))
    (ans : A → (s : Sending) → (i : Fin s.l.length) → Option (((sigOf r.cs s.l).om i).Z.S → GE))
    (a : A) (i : Fin r.lo.length) (σ : ((sigOf r.cs r.lo).om i).Smp)
    (hF : forms a ⟨r.lo, seat⟩ i = some (((sigOf r.cs r.lo).om i).Z.mat σ.1))
    (hA : ans a ⟨r.lo, seat⟩ i = some σ.2) :
    ∃ z, smpOf r.cs forms ans a ⟨r.lo, seat⟩ i = some z ∧
      ((sigOf r.cs r.lo).om i).Z.val z.1 = ((sigOf r.cs r.lo).om i).Z.val σ.1 ∧ z.2 = σ.2 := by
  obtain ⟨ρ', h1, h2⟩ := smpOf_of r.cs forms ans a ⟨r.lo, seat⟩ i σ.1 σ.2 hF hA
  exact ⟨(ρ', σ.2), h1, seedIs_val r.cs forms a ⟨r.lo, seat⟩ i ρ' σ.1 h2 hF, rfl⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.held_is_table

#print axioms VerifiableInference.Desc.First.K2Caller.pin_kept

#print axioms VerifiableInference.Desc.First.K2Caller.kept_dec
