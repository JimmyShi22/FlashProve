-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/K10SmallLay.lean: THE LAW OF K10 AT K10's OWN BLOCK, AT THE REAL GROUP
OF THE SMALL SIZE, LAID BY THE PROGRAM's OWN LAYOUT, WHICHEVER MEMBERS ARE KEPT. A statement and its
proof.

`k10_small_block` (K10SmallBlock.lean, beside this file) leaves one premise on numbers: the group's
data are in order. CornersKept.lean pays it at the layout that the program's `layBlocks` gives for
any choice kb of kept members.
  `k10_small_block_lay`: `k10_small_block` at `groupSmallLayK lo hlo gs hgs kb`: hGood is gone; in
    its place ONE equation of numbers: the group in front has the number of row variables that the
    program's formula gives for these flags (hk).
What is left, by the binders' names: hk · N · keep · B · n · num · Kc St₀ Wp · E₀ · A₀ · w₀ · w₁ · L
· dB dE dR · ρ · hρ · pS · Cl W · F · Pr · base · ext · err · fa · na nb · iE · iR · hn57 · iB.
Limits. Those of K10SmallBlock.lean and of CornersKept.lean, LayoutDrawn.lean: which flags are a
plan's is not said; that a running statement's group has these members, shapes and flags is not
shown. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.K10SmallBlock
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

variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (kb : Fin lo.length → Bool)

local notation "RF" => groupSmallLayK lo hlo gs hgs kb
local notation "SF" => sigOf codesSmall2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))

theorem k10_small_block_lay
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
    (ρ : Rd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall
      gs.k).bC (placeSmall gs.k).bZ w₀ w₁) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁) dB dE dR (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc ((RF).foldCaller keep (SbV RF B) (slV
      RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src ((RF).foldCaller keep
      (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ
      w₀ w₁)).X × ((kBatFoldRide L).src ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF
      n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).E.Str)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 56) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n)) :
    (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep
      (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ
      w₀ w₁)).k ext err).ior.red.Leads (K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeSmall
      gs.k).bC (placeSmall gs.k).bZ w₀ w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceAt (Cl := Cl)
      (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF
      (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k ext
      err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec
      base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧ closeFrame
      (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceAt (Cl := Cl) (W
      := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF
      (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k ext
      err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK
      a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk
      ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 =
          {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt RF N keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeSmall
        gs.k).bC (placeSmall gs.k).bZ w₀ w₁ L (fa a) (rdBK a'.1).1.rows → (∃ m : (SF).Msg, ∀ i,
        (SF).decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m : (SF).Msg, (∀ i, (SF).decs (fa
        a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? =
        some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
        ∀ (r : (RF).G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j,
        rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList[i]
        j * ((RF).Sh.rho.up ((RF).G.msg m, r)).1 j = readE (runRows (rdK a.1).2.2
        G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE
          dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
              (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁)).k ext err).ds)) :=
  k10_small_block lo hlo gs hgs _ _ _ (groupSmallLayK_good lo hlo gs hgs kb hk) N keep n num A₀ w₀
    w₁ L dB dE dR ρ hρ pS Pr base ext err fa iE iR hn57 iB

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_small_block_lay
