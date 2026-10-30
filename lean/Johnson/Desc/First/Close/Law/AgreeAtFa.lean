-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AgreeAtFa.lean (kind K10): THE EXTRACTOR's OWN MEMBERS AGREE, WHERE
EACH IS ALIKE TO ONE OF THE GROUP's LIST AND THE KEY PARTS THE LIST's SEATS. Statements and proofs.

Why. `fa_pin_ext` (PinsAtFa.lean) and `k10_pin_laid` (PinsAtTable.lean), beside this file, ask
`Agree` and `AgreeBy` (Johnson/Desc/Sound/World.lean): all of the extractor's own members with one
number (with one seat) that decode decode alike. Under "every word decodes at what faK10 lays" a
member that is alike to the i-th of the group's list decodes to the i-th decoded message
(`fa_dec_at`): so two members agree as soon as their key names one i.
  `fa_agreeBy` (general in the key): key x = kS (the seat of x); every member of the list msL is
    alike to one of the group's list; kS parts the group's list's seats (kS (seat i) = kS (seat i')
    → i = i'); `SmpBySeat`; `CfAt` at every member of the group's list; the decoder at `faK10` gives
    u i at every i: THEN `AgreeBy cs G smpS key msL (z, a.1) y k`, at every k.
  `fa_agree`: at key := `numOf arr`: `Agree`. `fa_agree_seat`: at key := `seatOf`.
Limits. That the numbers `arr` part the group's seats, and that seat is injective, are premises:
facts on the plan (the table's own test `laysNodup`, Johnson/Desc/First/Borders.lean, is their kin):
not called here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PinsAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers ModelPart laysSeats)

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

/-- **Members that are alike to the group's list's agree, where the key parts its seats.** -/
theorem fa_agreeBy {Ky : Type} [DecidableEq Ky] (key : Mem → Ky) (kS : ℕ × ℕ → Ky)
    (hkey : ∀ x, key x = kS (seatOf x)) (msL : List Mem)
    (hAl : ∀ x ∈ msL, ∃ i : Fin lo.length, Alike x ⟨⟨lo, seat⟩, i⟩)
    (hinj : ∀ i i' : Fin lo.length, kS (seat i) = kS (seat i') → i = i')
    (hB : SmpBySeat cs smpS) (z : Pz) (a : S1 × F.E.Str)
    (hCf : ∀ i, CfAt G cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (u : (sigOf cs lo).Msg)
    (hd : ∀ i, (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some (u i))
    (k : Ky) : AgreeBy cs G smpS key msL (z, a.1) (strsOf F a.2) k := by
  intro x hx x' hx' hk hk' m m' hm hm'
  obtain ⟨i, hi⟩ := hAl x hx
  obtain ⟨i', hi'⟩ := hAl x' hx'
  have e : i = i' := by
    apply hinj
    have s1 : seatOf x = seat i := hi.2
    have s2 : seatOf x' = seat i' := hi'.2
    rw [← s1, ← s2, ← hkey, ← hkey, hk, hk']
  subst e
  obtain ⟨zz, hz, hsh, -⟩ := hCf i
  have d1 := fa_dec_at G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW x i hi
    hB z a zz hz hsh (u i) (hd i)
  have d2 := fa_dec_at G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW x' i
    hi' hB z a zz hz hsh (u i) (hd i)
  exact (Option.some.inj (hm.symm.trans d1)).trans (Option.some.inj (hm'.symm.trans d2)).symm

/-- At the members' numbers in the witness. -/
theorem fa_agree (arr : ℕ → ℕ → ℕ) (msL : List Mem)
    (hAl : ∀ x ∈ msL, ∃ i : Fin lo.length, Alike x ⟨⟨lo, seat⟩, i⟩)
    (hinj : ∀ i i' : Fin lo.length,
      arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → i = i')
    (hB : SmpBySeat cs smpS) (z : Pz) (a : S1 × F.E.Str)
    (hCf : ∀ i, CfAt G cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (u : (sigOf cs lo).Msg)
    (hd : ∀ i, (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some (u i))
    (k : ℕ) : Agree cs G arr smpS msL (z, a.1) (strsOf F a.2) k :=
  fa_agreeBy G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW (numOf arr)
    (fun s => arr s.1 s.2) (fun _ => rfl) msL hAl hinj hB z a hCf u hd k

/-- At the members' seats. -/
theorem fa_agree_seat (msL : List Mem)
    (hAl : ∀ x ∈ msL, ∃ i : Fin lo.length, Alike x ⟨⟨lo, seat⟩, i⟩)
    (hinj : Function.Injective seat) (hB : SmpBySeat cs smpS) (z : Pz) (a : S1 × F.E.Str)
    (hCf : ∀ i, CfAt G cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (u : (sigOf cs lo).Msg)
    (hd : ∀ i, (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some (u i))
    (k : ℕ × ℕ) : AgreeBy cs G smpS seatOf msL (z, a.1) (strsOf F a.2) k :=
  fa_agreeBy G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW seatOf
    (fun s => s) (fun _ => rfl) msL hAl (fun _ _ h => hinj h) hB z a hCf u hd k

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.fa_agreeBy
#print axioms VerifiableInference.Desc.First.Close.fa_agree
#print axioms VerifiableInference.Desc.First.Close.fa_agree_seat
