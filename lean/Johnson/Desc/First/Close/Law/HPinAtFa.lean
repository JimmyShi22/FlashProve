-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/HPinAtFa.lean (kind K10): THE PREMISE hPin OF `k10_hQ_beside`
(HQBeside.lean, beside this file), IN ITS VERY FORM, AT THE CONCRETE fa (`faK10`) AND A MEANING
WHOSE LETTER "pin" IS THE LIBRARY's OWN NOTION, FROM THE SAME PREMISE hpin THAT THE ROWS' PART
SPENDS. A statement and its proof.

Why. `k10_hRow` (HRowAtFa.lean) has hRow from hpin: every member with a main row of
the group's list is pinned in front, at the extractor's value, AT THE GROUP's OWN LIST (`PinAt Gd cs
lo seat ..`). The table's item "pin m t" speaks of the members of ms, each in ITS OWN prover's
message's list (`pinJT`, Johnson/Desc/Sound/MeaningSig.lean). `pin_move`
(Johnson/Desc/Sound/PinMove.lean) carries a pin between members that are alike.
  `k10_hPin`: hMg (the meaning's letter "pin" is `pinJT cs Gd arr smpS ms`: at the composed meaning
    by definition) · hSit (at every tenant of a moment whose pin the place closes a member of ms
    sits) · hAl (every member of ms that sits there is alike to a member WITH A MAIN ROW of the
    group's list) · hB (`SmpBySeat`) · hpin: THEN hPin, in its very form.
Limits. BOOK-KEEPING. hpin IS THE WHOLE CONTENT: at a member that the extractor lays: `fa_pin_ext`
(PinsAtFa.lean) with `pin_move`; at a kept member: from the item "pinKept" behind, ridden back:
`pin_kept_behind` (PinKeptBack.lean), under its own premises; `k10_hpin` (HpinAtTable.lean) has
hpin of the two, with a letter smpD inside fa, under hV (`SameVal`), hCar (`CarriedAt`) and further
premises that are shown of no state (fed to k10_hPin_any, HQAtFa.lean; not called at this theorem).
hSit and hAl are facts on the plan. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HQBeside
import Johnson.Desc.First.Close.Law.PinsAtFa
import Johnson.Desc.Sound.MeaningSig
import Johnson.G.SwitchKeptLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart)

variable {Xi : Type} (Gd : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
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

/-- The typed stage's caller. -/
local notation "cK10" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **hPin OF k10_hQ_beside, IN ITS VERY FORM.** -/
theorem k10_hPin {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (X : (Pz × S1) × F.E.Str → Prop)
    (hMg : Mg.pin = pinJT cs Gd arr smpS ms)
    (hSit : ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t, ∃ y ∈ ms, SitsAt y s.1 s.2)
    (hAl : ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t, ∀ y ∈ ms, SitsAt y s.1 s.2 →
      ∃ i : Fin lo.length, memMain lo i ∧ Alike y ⟨⟨lo, seat⟩, i⟩)
    (hB : SmpBySeat cs smpS)
    (hpin : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ i, memMain lo i → PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1)
          (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)) :
    ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t,
          Mg.pin s.1 s.2 (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w) := by
  intro z a a' hx hon hend w hw t ht s hs
  rw [hMg]
  refine ⟨hSit t ht s hs, fun y hy hy' => ?_⟩
  obtain ⟨i, hmi, hal⟩ := hAl t ht s hs y hy hy'
  exact (pin_move cs Gd arr smpS y ⟨⟨lo, seat⟩, i⟩ hal (z, a.1) (hB (z, a.1) y ⟨⟨lo, seat⟩, i⟩ hal)
    (strsOf F a.2) _).2 (hpin z a a' hx hon hend w hw i hmi)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_hPin
