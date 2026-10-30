-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/HRowDrawn.lean (kind K10): THE PREMISE hRow OF k10_hQ_beside
(HQBeside.lean, beside this file), IN ITS VERY FORM, AT THE fa THAT LAYS THE DRAWN SEEDS:
`faK10 .. smpD ..` WITH A LETTER smpD FOR THE READER OF SAMPLES THAT fa LAYS, where HRowAtFa.lean's
k10_hRow has the table's own reader. A statement and its proof.

Why. fa stands inside the law's condition (K10OnS) and its end (K10EndS).
By report
the condition's clause "tied" has a road where fa lays the seeds as they were drawn; whether it can
be paid at the table's own reader IS NOT DECIDED. So the law's hQ is wanted at that fa. The pins
(`PinAt`) speak at the table's own reader. The library
cannot tell the two readers apart where they have one value and one answer (`SameVal`,
FaTwoReaders.lean): the decoders at what the two fa lay are one (`fa_decs_same`), wherever the
table's reader gives a sample.

What is said. `k10_hRow_drawn`: k10_hRow's sentence with smpD inside fa. TWO PREMISES MORE: hV
(SameVal cs lo smpD ‹the table's reader at ⟨lo, seat⟩›) and hSm (under X the table's reader gives a
sample at EVERY message of the list, those without a main row among them). ALL OTHER PREMISES ARE
k10_hRow's, with smpD inside fa in hCar and hpin's conditions; `RowAsks` is HRowAtFa.lean's.

Limits. BOOK-KEEPING, AS k10_hRow IS: NO PREMISE IS DISCHARGED. hV and hSm are shown of no reader
and
no state here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HRowAtFa
import Johnson.Desc.First.Close.Law.FaTwoReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open OnBytes.Means (InOrder tableSize)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowsHeld membersHeld PlacesApart
  rowSays wordsAtFirst)

variable {Xi : Type} (Gd : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (s : Sg) (e' : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

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

/-- The typed stage's caller. -/
local notation "cK10" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **hRow OF k10_hQ_beside, IN ITS VERY FORM, AT THE fa THAT LAYS THE DRAWN SEEDS.** -/
theorem k10_hRow_drawn (hV : SameVal cs lo smpD fun q j => smpS q ⟨lo, seat⟩ j)
    (hR : R = groupLayK cs lo s e' kb hM hZ) (hg : R.Good) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (hPr : Pr.k = R.s.h + R.s.g) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (X : (Pz × S1) × F.E.Str → Prop) (O : List Item) (no : Fin lo.length → ℕ)
    (hrow : Mg.row = rowSays Nu (wordsAtFirst arr))
    (hO : ∀ c, insQ links ps k (Item.row m c) → Item.row m c ∈ O)
    (hP : ∀ t, Item.row m (.sample t) ∈ O → t < 3 ∧ Item.pin m t ∈ O)
    (hX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) → RowAsks cs lo seat kb R N Nu m O no a.1)
    (hSm : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      ∀ i, ∃ zz, smpS (z, a.1) ⟨lo, seat⟩ i = some zz)
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L
          (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z a) (rdBK a'.1).1.rows)
    (hpin : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ i, memMain lo i → PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1)
          (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)) :
    ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ c, insQ links ps k (Item.row m c) →
          Mg.row m c (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w) := by
  intro z a a' hx hon hend w hw c hc
  have A := hX z a hx
  rw [hrow]
  exact k10_rows_at_cube R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base _ _ _ a a' hend
    hPr A.inOrder hg (fun b => no b.1) A.ties A.names (hCar z a a' hx hon hend w hw) (fun _ => 0)
    Nu (wordsAtFirst arr) z (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)
    (fun μ hμ => wordsAre_of_pins Gd cs lo seat s e' kb hM hZ R N keep pull n num fx A₀ bC bZ w₀ w₁
      L smpS σ₀ st₀ e₀ mW hR arr z a no (fun _ => 0) _ A.codes A.seats A.shapes
      (hpin z a a' hx hon hend w hw) μ fun i => by
        obtain ⟨zz, hz⟩ := hSm z a hx i
        exact (fa_decs_same Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD
          (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW hV z a i zz hz).symm.trans (hμ i))
    m A.grp O A.rows A.members A.apart hP c (hO c hc)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_hRow_drawn
