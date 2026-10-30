-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PinsAtTable.lean (kind K10): THE TABLE OF JOINTS' OWN SENTENCE "pin" AT
A SEAT THAT K10's EXTRACTOR LAYS, AT THE TABLE's OWN EXTRACTOR's VALUE, FROM "EVERY WORD DECODES AT
WHAT faK10 LAYS". A statement and its proof.

Why. hPin of `k10_hQ_beside` (HQBeside.lean, beside this file) asks `Mg.pin s.1 s.2 ..` at every
tenant s of the link's three moments; at the composed meaning that is `pinJT`
(Johnson/Desc/Sound/MeaningSig.lean): a member of ms sits there, and every member of ms that sits
there is pinned. PinsAtFa.lean has the pin of one member among the extractor's own.
  `k10_pin_laid`: s is among the seats that the extractor at the place p lays (`laysSeats Nu links
    p`); a member of ms sits at s; every member of ms that sits at s is alike to one of the group's
    list; the reader of samples hangs on the entry and the seat alone; every member of the group's
    list has no collision in the table's sense (`CfAt`: it holds the sample and "every leaf is
    shown"); the decoder at `faK10` gives a message at every member; the extractor's own members
    agree (`Agree`, `AgreeBy`): THEN `pinJT cs G arr smpS ms s.1 s.2 (z, a.1) y (extQ .. p (z, a.1)
    y behind w)`, whatever w and behind.
Limits. ONLY AT THE SEATS THAT THE EXTRACTOR LAYS: AT A K10 PLACE THESE ARE THE GROUP's BUT THE KEPT
ONES (Johnson/Desc/First/Borders.lean, `laysSeats`): at a kept tenant the pin in front must come
from the item "pinKept" behind: not here. All the premises named stand. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.PinsAtFa
import Johnson.Desc.Sound.BordersFill

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

/-- **The table's "pin" at a seat that the extractor lays.** -/
theorem k10_pin_laid {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok) (Nu : Numbers) (links : List ModelPart) (p : Place) (s : ℕ × ℕ)
    (hs : s ∈ laysSeats Nu links p) (hSit : ∃ x ∈ ms, SitsAt x s.1 s.2)
    (hAl : ∀ x ∈ ms, SitsAt x s.1 s.2 → ∃ i : Fin lo.length, Alike x ⟨⟨lo, seat⟩, i⟩)
    (hB : SmpBySeat cs smpS) (z : Pz) (a : S1 × F.E.Str)
    (hCf : ∀ i, CfAt G cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (u : (sigOf cs lo).Msg)
    (hd : ∀ i, (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 i = some (u i))
    (hA : ∀ x ∈ mineAt ms Nu links p,
      Agree cs G arr smpS (mineAt ms Nu links p) (z, a.1) (strsOf F a.2) (numOf arr x))
    (hS : ∀ x ∈ mineAt ms Nu links p,
      AgreeBy cs G smpS seatOf (mineAt ms Nu links p ++ minePadAt ms Nu links p) (z, a.1)
        (strsOf F a.2) (seatOf x))
    (behind : Option (Pz × S1)) (w : Wit Cells Tok MsgT) :
    pinJT cs G arr smpS ms s.1 s.2 (z, a.1) (strsOf F a.2)
      (extQ cs G arr smpS ms decT c₀ tokOf Nu links p (z, a.1) (strsOf F a.2) behind w) := by
  refine ⟨hSit, fun x hx hx' => ?_⟩
  have hm : x ∈ mineAt ms Nu links p := by
    refine List.mem_filter.2 ⟨hx, ?_⟩
    have e : x.1.seat x.2 = s := hx'
    rw [e]
    exact List.contains_iff_mem.2 hs
  obtain ⟨i, hi⟩ := hAl x hx hx'
  obtain ⟨zz, hz, hsh, -⟩ := hCf i
  unfold extQ
  exact fa_pin_ext G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW arr decT
    c₀ _ _ false _ x hm i hi hB z a zz hz hsh (u i) (hd i) (hA x hm) (hS x hm) w

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_pin_laid
