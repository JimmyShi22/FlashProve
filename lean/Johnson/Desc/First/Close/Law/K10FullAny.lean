-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/K10FullAny.lean: THE LAW OF K10 AT ANY BLOCK WHOSE YES IS
`closeFrame`'s, AT THE REAL GROUP OF THE FULL SIZE, LAID BY THE PROGRAM's OWN LAYOUT. Statements and
proofs.

`k10_full_block` and `k10_full_block_lay` (K10FullBlock.lean, K10FullLay.lean, beside this file)
speak of the piece of `K9.closing Pr`. A description seats that block under wrappers. Here the same
two are said of `pieceOn b ..` (AtAny.lean): b a letter with the one premise H: its yes is
`closeFrame`'s.
  `k10_full_any`: `k10_any_self` at `groupFull lo hlo gs hgs oM oZ kp` with the payers of
    `k10_full_block`.
  `k10_full_any_lay`: the same at `groupFullLayK lo hlo gs hgs kb`: hGood is gone; in its place hk :
    gs.k = kLay lo kb.
What is left of `k10_full_any`, by the binders' names: hGood · N · keep · B · n · num · Kc St₀ Wp ·
E₀ · A₀ · w₀ · w₁ · L · dB dE dR · ρ · hρ · pS · Cl W · F · Pr · b · H · base · ext · err · fa · na
nb · iE · iR · hn57 · iB.
Limits. Those of K10FullBlock.lean, K10FullLay.lean and AtAny.lean. Nothing on an honest prover or
on hiding.

-/
import Johnson.Desc.First.Close.Law.AtAny
import Johnson.Desc.First.Close.Law.AtFull
import Johnson.Desc.First.Close.Law.FxPays
import Johnson.Desc.First.Close.Law.BatFull
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

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

local notation "RF" => groupFull lo hlo gs hgs oM oZ kp
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))

theorem k10_full_any
    (hGood : (RF).Good)
    (N : SlotNames RF)
    (keep : (SF).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (RF).G.Row B ≃ Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((SF).sub ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n
      num)).kp).Msg × Wp))
    (w₀ : (SF).Wit × Wp)
    (w₁ : LdBrW (RF).G ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) dB dE dR (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV
      RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src ((RF).foldCaller keep
      (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
      w₀ w₁)).X × ((kBatFoldRide L).src ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF
      n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).E.Str)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf
      RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext
      err).ior.red.Leads (K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE
      dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV
      RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2 τ = true
      ∧ closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceOn
      (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF))
      (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2
      τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧
      ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK
      a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt RF N keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
        gs.k).bC (placeFull gs.k).bZ w₀ w₁ L (fa a) (rdBK a'.1).1.rows → (∃ m : (SF).Msg, ∀ i,
        (SF).decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m : (SF).Msg, (∀ i, (SF).decs (fa
        a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? =
        some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
        ∀ (r : (RF).G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j,
        rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList[i]
        j * ((RF).Sh.rho.up ((RF).G.msg m, r)).1 j = readE (runRows (rdK a.1).2.2
        G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller
          keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull
              gs.k).bZ w₀ w₁)).k ext err).ds)) :=
  k10_any_self RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L dB
    dE dR ρ hρ (caller_step RF keep _ _ _ A₀ _ _ w₀ w₁) (caller_pick RF keep _ _ _ A₀ _ _ w₀ w₁)
    (full_fits lo hlo gs hgs oM oZ kp) hGood (full_inJ lo hlo gs hgs oM oZ kp) (full_counts lo hlo
    gs hgs oM oZ kp) (full_radius lo hlo gs hgs oM oZ kp) (full_fix lo hlo gs hgs oM oZ kp)
    (full_pulls lo hlo gs hgs oM oZ kp) pS Pr b H base ext err fa (placeFull gs.k) (placeFull_paid
    gs hgs) (full_stage lo hlo gs hgs oM oZ kp) (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl
    le_rfl iE iR (batFull gs.k n) (batFull_paid gs.k n hn57) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl iB

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupFullLayK lo hlo gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))

theorem k10_full_any_lay
    (hk : gs.k = kLay lo kb)
    (N : SlotNames RF)
    (keep : (SF).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (RF).G.Row B ≃ Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((SF).sub ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n
      num)).kp).Msg × Wp))
    (w₀ : (SF).Wit × Wp)
    (w₁ : LdBrW (RF).G ((RF).sizeB keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) dB dE dR (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV
      RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src ((RF).foldCaller keep
      (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
      w₀ w₁)).X × ((kBatFoldRide L).src ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF
      n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).E.Str)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf
      RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext
      err).ior.red.Leads (K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE
      dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV
      RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2 τ = true
      ∧ closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceOn
      (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF))
      (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2
      τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧
      ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK
      a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt RF N keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull
        gs.k).bC (placeFull gs.k).bZ w₀ w₁ L (fa a) (rdBK a'.1).1.rows → (∃ m : (SF).Msg, ∀ i,
        (SF).decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m : (SF).Msg, (∀ i, (SF).decs (fa
        a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? =
        some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
        ∀ (r : (RF).G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j,
        rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList[i]
        j * ((RF).Sh.rho.up ((RF).G.msg m, r)).1 j = readE (runRows (rdK a.1).2.2
        G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc ((RF).foldCaller
          keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull
              gs.k).bZ w₀ w₁)).k ext err).ds)) :=
  k10_full_any lo hlo gs hgs _ _ _ (groupFullLayK_good lo hlo gs hgs kb hk) N keep n num A₀ w₀ w₁ L
    dB dE dR ρ hρ pS Pr b H base ext err fa iE iR hn57 iB

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_full_any
#print axioms VerifiableInference.Desc.First.Close.k10_full_any_lay
