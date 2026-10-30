-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/MsgsAtFa.lean (kind K10): AT WHAT THE TABLE's EXTRACTOR GIVES, THE
WITNESS's MESSAGE AT THE i-TH OF THE GROUP's LIST IS WHAT THE PROVED SUB-PROTOCOL's DECODER GIVES
THERE AT `faK10`. Statements and proofs: calls.

Why. The tie between the typed message and the words (`WordsAre`, CubeAt.lean, beside this file) is
brought down to one equation a member: the typed message at a = `msgsOf cs lo
seat arr w a` (Johnson/Desc/Sound/MsgSig.lean: the witness's messages, read at the group's own
list). PinsAtFa.lean, beside this file, has a pin at the table's own member, in ITS list.
  `fa_msgs_of_pin`: the i-th of the group's list is pinned at w (`PinAt G cs lo seat ..`), and the
    decoder at `faK10` gives u at i: THEN `msgsOf cs lo seat arr w i = u`: a pin names the decoder's
    one value.
  `fa_msgs_ext`: under `fa_pin_ext`'s premises: `msgsOf cs lo seat arr (extAt .. mine minePad .. w)
    i = u`. By `fa_pin_ext` and `pin_move` (Johnson/Desc/Sound/PinMove.lean).
Limits. CALLS. All of `fa_pin_ext`'s premises stand. Nothing on the rows. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PinsAtFa

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ)
variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))

local notation "S1" => VerifiableInference.Desc.First.S

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **A pin names the decoder's one value.** -/
theorem fa_msgs_of_pin {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (i : Fin lo.length) (z : Pz)
    (a : S1 × F.E.Str) (w : Wit Cells Tok MsgT)
    (hp : PinAt G cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1) (strsOf F a.2) w)
    (u : ((sigOf cs lo).om i).Msg)
    (hd : (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some u) :
    msgsOf cs lo seat arr w i = u := by
  obtain ⟨zz, hz, -, hm⟩ := hp
  have hz' : smpS (z, a.1) ⟨lo, seat⟩ i = some zz := hz
  rw [fa_decs, hz'] at hd
  exact Option.some.inj (hm.symm.trans hd)

/-- **At the table's extractor's value the witness's message is the decoded one.** -/
theorem fa_msgs_ext {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (x : Mem) (hx : x ∈ mine)
    (i : Fin lo.length) (h : Alike x ⟨⟨lo, seat⟩, i⟩) (hB : SmpBySeat cs smpS) (z : Pz)
    (a : S1 × F.E.Str) (zz : ((sigOf cs lo).om i).Smp)
    (hz : smpS (z, a.1) ⟨lo, seat⟩ i = some zz)
    (hs : ShownAt G cs lo seat (strsOf F a.2) i) (u : ((sigOf cs lo).om i).Msg)
    (hd : (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some u)
    (hA : Agree cs G arr smpS mine (z, a.1) (strsOf F a.2) (numOf arr x))
    (hS : AgreeBy cs G smpS seatOf (mine ++ minePad) (z, a.1) (strsOf F a.2) (seatOf x))
    (w : Wit Cells Tok MsgT) :
    msgsOf cs lo seat arr
      (extAt cs G arr smpS decT c₀ mine minePad cellsToo tokNew (z, a.1) (strsOf F a.2) w) i = u :=
  fa_msgs_of_pin G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW arr i z a _
    ((pin_move cs G arr smpS x ⟨⟨lo, seat⟩, i⟩ h (z, a.1) (hB (z, a.1) x ⟨⟨lo, seat⟩, i⟩ h)
      (strsOf F a.2) _).1
      (fa_pin_ext G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW arr decT c₀
        mine minePad cellsToo tokNew x hx i h hB z a zz hz hs u hd hA hS w)) u hd

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.fa_msgs_of_pin
#print axioms VerifiableInference.Desc.First.Close.fa_msgs_ext
