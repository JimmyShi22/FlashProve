-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PinsAtFa.lean (kind K10): FROM "THE PROVED SUB-PROTOCOL's DECODER GIVES
A MESSAGE AT WHAT faK10 LAYS" TO "THE TABLE's MEMBER IS PINNED AT WHAT THE TABLE's EXTRACTOR GIVES".
Statements and proofs: calls.

Why. K10's law's end (`K10EndS`, GoodOf.lean) says: every word of the group decodes, at what fa
lays. The table of joints' item "pin" says of a member of ONE prover's message's list that it is
pinned (`PinAt`) at the witness. The sentence hQ of `k10_law_full_lay` (KindK10LawLay.lean) wants
the second, at the value of the table's extractor, from the first. The group's list and a prover's
message's list are two lists: Johnson/Desc/Sound/PinMove.lean moves what is said of
a member to every member that is alike (one entry, one seat).
  `fa_dec_at`: x a member that is alike to the i-th of the group's list (`Alike x ⟨⟨lo, seat⟩, i⟩`);
    the reader of samples hangs on the entry and the seat alone (`SmpBySeat`); the state holds the
    i-th's sample; every leaf is shown; the decoder at `faK10` (its smp := the reader at the sending
    ⟨lo, seat⟩) gives u at i: THEN x decodes in the table's sense: `decAt .. x .. = some (toMsgT cs
    lo i u)`. By `dec_of_alike` and `fa_decs`.
  `fa_pin_ext`: so, where x is among the row's own members (mine) and the row's own agree (`Agree`,
    `AgreeBy`): x is pinned at `extAt .. mine minePad .. w`, whatever w. By `pin_ext`
    (Johnson/Desc/Sound/World.lean).
Limits. CALLS. `Alike`, `SmpBySeat`, the sample, `ShownAt`, `Agree`, `AgreeBy`, x ∈ mine are
premises. That every member at a seat of the link's three moments is alike to a member of the
group's list is said nowhere: there is no term for seat. Nothing on the rows. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.FaK10
import Johnson.Desc.Sound.PinMove

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

/-- **A member that is alike to one of the group's list decodes in the table's sense**, where the
proved sub-protocol's decoder gives a message at what is laid. -/
theorem fa_dec_at (x : Mem) (i : Fin lo.length) (h : Alike x ⟨⟨lo, seat⟩, i⟩)
    (hB : SmpBySeat cs smpS) (z : Pz) (a : S1 × F.E.Str) (zz : ((sigOf cs lo).om i).Smp)
    (hz : smpS (z, a.1) ⟨lo, seat⟩ i = some zz)
    (hs : ShownAt G cs lo seat (strsOf F a.2) i) (u : ((sigOf cs lo).om i).Msg)
    (hd : (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some u) :
    decAt cs G smpS x.1 x.2 (z, a.1) (strsOf F a.2) = some (toMsgT cs lo i u) := by
  have hh := hB (z, a.1) x ⟨⟨lo, seat⟩, i⟩ h
  rw [hz] at hh
  rw [fa_decs, hz] at hd
  exact dec_of_alike cs G smpS x ⟨lo, seat⟩ i h (z, a.1) (strsOf F a.2) zz hh hs u hd

/-- **So it is pinned at what the table's extractor gives.** -/
theorem fa_pin_ext {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
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
    PinAt G cs x.1.l x.1.seat (fun q => smpS q x.1) arr x.2 (z, a.1) (strsOf F a.2)
      (extAt cs G arr smpS decT c₀ mine minePad cellsToo tokNew (z, a.1) (strsOf F a.2) w) :=
  pin_ext cs G arr smpS decT c₀ mine minePad cellsToo tokNew (z, a.1) (strsOf F a.2) w x hx _
    (fa_dec_at G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW x i h hB z a
      zz hz hs u hd) hA hS

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.fa_dec_at
#print axioms VerifiableInference.Desc.First.Close.fa_pin_ext
