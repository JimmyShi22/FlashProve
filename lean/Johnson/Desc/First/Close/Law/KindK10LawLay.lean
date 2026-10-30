-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10LawLay.lean (kind K10): `k10_law_full` (KindK10LawFull.lean,
beside this file) AT THE GROUP AT THE PROGRAM's OWN LAYOUT, THE MEMBERS WITH THE FLAG KEPT
(`groupFullLayK`, CornersKept.lean): ITS PREMISE "the group's data are in order" FALLS AGAINST ONE
EQUATION ON NUMBERS. A statement and its proof: one call.

  `k10_law_full_lay`: hk : gs.k = kLay lo kb (the group in front has the number of row variables
    that the layout's formula gives for these flags): THEN `k10_law_full`'s end at `groupFullLayK lo
    hlo gs hgs kb`, from its other premises. By `groupFullLayK_good` (CornersKept.lean).
hk at each of the 25 links, at the written list and the written request's flags: `real_full`
(ReqKept.lean), by the kernel: there is such a gs in `frontFull`: not called here.
Limits. Those of KindK10LawFull.lean: hQ IS SHOWN NOWHERE; fa is a letter; that the seated term's
piece is this piece at these letters is not shown. That a verifier's state's group has these members
and flags at a closing is not shown. No soundness statement.

-/
import Johnson.Desc.First.Close.Law.KindK10LawFull
import Johnson.Desc.First.Close.Law.CornersKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)

variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupFullLayK lo hlo gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupFullLayK lo hlo gs hgs kb).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFullLayK lo hlo gs hgs kb).sizeB keep
    (SbV (groupFullLayK lo hlo gs hgs kb) B)
    (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
    (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFullLayK lo hlo gs hgs kb).G ((groupFullLayK lo hlo gs hgs kb).sizeB keep
    (SbV (groupFullLayK lo hlo gs hgs kb) B)
    (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
    (ZV (groupFullLayK lo hlo gs hgs kb) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the real group. -/
local notation "CK" => (groupFullLayK lo hlo gs hgs kb).foldCaller keep
  (SbV (groupFullLayK lo hlo gs hgs kb) B)
  (slV (groupFullLayK lo hlo gs hgs kb) (pullOf (groupFullLayK lo hlo gs hgs kb)))
  (ZV (groupFullLayK lo hlo gs hgs kb) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁

/-- **THE FIELD law AT THE PROGRAM's OWN LAYOUT: THE GROUP's DATA ARE IN ORDER TOO.** -/
theorem k10_law_full_lay (hk : gs.k = kLay lo kb) (N : SlotNames RF)
    {Pz : Type} (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd (CK) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd (CK) dB dE dR (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1 Cl)
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ) (x : Rest (ckP .two) F (Pz × S1) W (dB :: dE :: List.replicate (Yc (CK)).k dR))
    (hcap : x.err = Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR)))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → W → W)
    (fa : Pz → S1 × F.E.Str → ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str)
    {na nb : String} (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n))
    (Rin Rout : (Pz × S1) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base dB dE dR (Yc (CK)).k
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc (CK)).k dR)))).ior.red.out a τ = some a' →
      K10EndS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR))) (fa z) a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) [] x).withMap e).ext
          ((z, a.1), a.2) τ w)) :
    ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) [] x).withMap e).GoodIn
      (fun a => K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  k10_law_full lo hlo gs hgs _ _ _ keep n num A₀ w₀ w₁ (groupFullLayK_good lo hlo gs hgs kb hk) N L
    dB dE dR ρ hρ pS Pr b H base x hcap e fa iE iR hn57 iB Rin Rout hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_law_full_lay
