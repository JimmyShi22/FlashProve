-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/HpinAtTable.lean (kind K10): EVERY MEMBER WITH A MAIN ROW OF THE
GROUP's LIST IS PINNED IN FRONT, AT THE TABLE's OWN EXTRACTOR's VALUE: THE ONE PREMISE hpin ON WHICH
BOTH HALVES OF hQ HANG, ASSEMBLED OF ITS TWO HALVES, AT `faK10` WITH ANY READER smpD OF SAMPLES THAT
THE LIBRARY CANNOT TELL FROM THE TABLE's. A statement and its proof.

Why. `k10_hPin` (HPinAtFa.lean) and `k10_hRow` (HRowAtFa.lean) spend hpin. K10's
extractor lays its group's seats but the kept ones (`laysSeats`, Johnson/Desc/First/Borders.lean).
At a seat that is laid the pin comes from "every word decodes at what faK10 lays" (`fa_pin_ext`,
PinsAtFa.lean); at a kept seat from the item "pinKept" behind, ridden back
(`pin_kept_behind`, PinKeptBack.lean).
  `minePad_k10`: at a place of the kind K10 the extractor lays no pad alone.
  `k10_hpin`: FROM: hp, hK (the place) · hMg (the meaning's "pin" is `pinJT`) · hOut ("pinKept" of
    the place's link is among what the place opens) · hV (`SameVal smpD` the table's reader at the
    group's list) · hB (`SmpBySeat`) · hStay (the table's reader answers alike across K10's step) ·
    hHit, hAlM, hGrp, hi1, hi2 (facts on the plan: every member with a main row is hit by a member
    of ms; the extractor's own are alike to the list's; its seat is laid or kept; the numbers and
    the seats part the list) · T1, T2 (PinKeptBack.lean's two tests) · hCfX (X gives the table's "no
    collision" at every member of the list) · hCar (X, the law's condition, its end and the relation
    behind give `CarriedAt`): THEN, under X, `K10OnS`, `K10EndS` and the relation behind, at every i
    with a main row: `PinAt Gd cs lo seat (the table's reader) arr i (z, a.1) y (extQAt .. k ((z,
    a.1), a.2) ((z, a'.1), a'.2) w)`.
Limits. AN ASSEMBLY: every premise named stands. hCar IS SPENT HERE TOO: the law's end gives "every
word decodes" only under `CarriedAt`. Nothing is shown of any state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HPinAtFa
import Johnson.Desc.First.Close.Law.AgreeAtFa
import Johnson.Desc.First.Close.Law.FaTwoReaders
import Johnson.Desc.First.Close.Law.PinKeptBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart laysSeats laysPads)

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
  (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- At a place of the kind K10 the extractor lays no pad alone. -/
theorem minePad_k10 (ms : List Mem) (Nu : Numbers) (links : List ModelPart) (p : Place)
    (hK : p.kind = .K10) : minePadAt ms Nu links p = [] := by
  have e : laysPads Nu links p = [] := by
    unfold laysPads
    split
    · rfl
    · rw [hK]
  unfold minePadAt
  rw [e]
  exact List.filter_eq_nil_iff.2 fun _ _ => by simp

/-- **hpin, OF ITS TWO HALVES.** -/
theorem k10_hpin {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hK : p.kind = .K10)
    (X : (Pz × S1) × F.E.Str → Prop) (hMg : Mg.pin = pinJT cs Gd arr smpS ms)
    (hOut : outsQ links ps k (Item.pinKept (p.link.getD 0)))
    (hV : SameVal cs lo smpD fun q j => smpS q ⟨lo, seat⟩ j) (hB : SmpBySeat cs smpS)
    (hStay : ∀ z s s', K10Step s s' → ∀ (y : Sending) (i : Fin y.l.length),
      smpS (z, s') y i = smpS (z, s) y i)
    (hHit : ∀ i, memMain lo i → ∃ y ∈ ms, Alike y ⟨⟨lo, seat⟩, i⟩)
    (hAlM : ∀ y ∈ mineAt ms Nu links p, ∃ i : Fin lo.length, Alike y ⟨⟨lo, seat⟩, i⟩)
    (hGrp : ∀ i, memMain lo i →
      seat i ∈ laysSeats Nu links p ∨ seat i ∈ Nu.keptOf (p.link.getD 0))
    (hi1 : ∀ i i' : Fin lo.length,
      arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → i = i')
    (hi2 : Function.Injective seat)
    (T1 : keptApartB arr Nu links p = true) (T2 : keptLowB Nu (p.link.getD 0) base = true)
    (hCfX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      ∀ i, CfAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L
          (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z a)
          (rdBK a'.1).1.rows) :
    ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ i, memMain lo i → PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1)
          (strsOf F a.2) (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k
            ((z, a.1), a.2) ((z, a'.1), a'.2) w) := by
  intro z a a' hx hon hend w hw i hmi
  have hcar := hCar z a a' hx hon hend w hw
  obtain ⟨⟨τ, himp, -, hcf⟩, hwr, -, -, hlast⟩ := hend
  obtain ⟨⟨u, hu⟩, -⟩ := hlast hcar
  have hCf := hCfX z a hx
  have huT : ∀ j, (sigOf cs lo).decs (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).1.2
      (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L
        (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW z a).2.1.2 j = some (u j) := fun j => by
    obtain ⟨zz, hz, -, -⟩ := hCf j
    rw [← fa_decs_same Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD
      (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW hV z a j zz hz]
    exact hu j
  obtain ⟨y, hy, hal⟩ := hHit i hmi
  have hseat : y.1.seat y.2 = seat i := hal.2
  have eE : extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k
      ((z, a.1), a.2) ((z, a'.1), a'.2) w =
      extAt cs Gd arr smpS decT c₀ (mineAt ms Nu links p) (minePadAt ms Nu links p) false
        (if VerifiableInference.Desc.First.laysTok links p then
          (some (z, a'.1)).map tokOf else none) (z, a.1) (strsOf F a.2) w := by
    unfold extQAt
    rw [hp]
    rfl
  rw [eE]
  refine (pin_move cs Gd arr smpS y ⟨⟨lo, seat⟩, i⟩ hal (z, a.1) (hB (z, a.1) y ⟨⟨lo, seat⟩, i⟩ hal)
    (strsOf F a.2) _).1 ?_
  rcases hGrp i hmi with hl | hk
  · have hm : y ∈ mineAt ms Nu links p := by
      refine List.mem_filter.2 ⟨hy, ?_⟩
      rw [hseat]
      exact List.contains_iff_mem.2 hl
    obtain ⟨zz, hz, hsh, -⟩ := hCf i
    refine fa_pin_ext Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW arr
      decT c₀ _ _ false _ y hm i hal hB z a zz hz hsh (u i) (huT i) ?_ ?_ w
    · exact fa_agree Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW arr _
        hAlM hi1 hB z a hCf u huT _
    · rw [minePad_k10 ms Nu links p hK, List.append_nil]
      exact fa_agree_seat Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS σ₀ st₀ e₀ mW _
        hAlM hi2 hB z a hCf u huT _
  · have hstep : K10Step a.1 a'.1 := ⟨_, _, _, hcf, hwr⟩
    have hbeh : Behind F base (strsOf F a.2) (strsOf F a'.2) :=
      ⟨_, a.2, τ, rfl, by rw [himp]; rfl⟩
    have hkp := hw (Item.pinKept (p.link.getD 0)) hOut
    have hkp' : Mg.pin (seat i).1 (seat i).2 (z, a'.1) (strsOf F a'.2) w := hkp (seat i) hk
    rw [hMg] at hkp'
    have hpb := hkp'.2 y hy hseat
    exact pin_kept_behind cs Gd arr smpS decT c₀ ms Nu links p hK false _ y
      (by show y.1.seat y.2 ∈ _; rw [hseat]; exact hk) base T1 T2 (z, a.1) (z, a'.1) _ _
      (hStay z a.1 a'.1 hstep y.1 y.2) hbeh w hpb

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.minePad_k10
#print axioms VerifiableInference.Desc.First.Close.k10_hpin
