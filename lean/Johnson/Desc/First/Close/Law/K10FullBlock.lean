-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/K10FullBlock.lean: THE LAW OF K10 AT K10's OWN BLOCK, AT THE REAL GROUP
OF THE FULL SIZE. A statement and its proof.

It gathers what the files beside it have paid: `k10_block_self` (AtBlockSelf.lean: the law at the
piece of K10's own block, lifted to the first chain's record, the group, the mask and the plan read
off the record) at the group, the pull, the fixed coefficient and the two written places of
GroupFull.lean, AtFull.lean, FxPays.lean and BatFull.lean.
  `k10_full_block`: at `groupFull lo hlo gs hgs oM oZ kp`: the piece of K10's block leads, from
    every statement with `K10OnS`, at the cap of 128 bits a round, to: one written transcript at
    which the stage's tests passed, the oracles behind are those left, and `closeFrame` returned
    just the frame and the statement read off the record behind; and if what is carried holds of
    that frame's rows, every message's word decodes and every row of `runRows` at the frame's own
    group holds.
What is left, by the binders' names: hGood · N · keep · B · n · num · Kc St₀ Wp · E₀ · A₀ · w₀ · w₁
· L · dB dE dR · ρ · hρ · pS · Cl W · F · Pr · base · ext · err · fa · na nb · iE · iR · hn57 · iB.
In kinds: the group's data are in order (hGood: Corners.lean and CornersKept.lean pay it at the
program's own layout); the three written rounds are the format's own (dB, dE, dR, ρ, hρ, iB, iE,
iR); n is at most 2^57; and letters: the names of the slots, the numbering, pS, fa, the kept
messages' joint, the place Pr, base, ext, err.
Limits. Those of AtBlockSelf.lean, AtBlock.lean (that the chain holds this piece's block is not
shown; Pr.k against the caller's number of fold rounds), OnK10.lean (that the promise holds of any
statement is not shown), AtPieceRead.lean (fa is a letter whose oracle half no premise ties to the
piece's oracles) and GroupFull.lean. The law's end is an implication from `CarriedAt`, of which no
member is shown. It is a law in the form `Leads`, not `GoodIn`. Through FoldPriced.lean and
BatPriced.lean it rests on the files under ThirdParty/ (lean/LIMITS.md, L15). Nothing on an honest
prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtBlockSelf
import Johnson.Desc.First.Close.Law.AtFull
import Johnson.Desc.First.Close.Law.FxPays
import Johnson.Desc.First.Close.Law.BatFull

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
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

local notation "RF" => groupFull lo hlo gs hgs oM oZ kp
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))

theorem k10_full_block
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
    (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep
      (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
      w₀ w₁)).k ext err).ior.red.Leads (K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceAt (Cl := Cl)
      (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF
      (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext
      err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec
      base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧ closeFrame
      (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceAt (Cl := Cl) (W
      := W) (F := F) Pr recOf putRec base dB dE dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF
      (pullOf RF)) (ZV RF n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext
      err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK
      a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk
      ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 =
          {
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
      (Err.cap 128 (uLT (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE
          dR (Yc ((RF).foldCaller keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
              (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k ext err).ds)) :=
  k10_block_self RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
    dB dE dR ρ hρ (caller_step RF keep _ _ _ A₀ _ _ w₀ w₁) (caller_pick RF keep _ _ _ A₀ _ _ w₀ w₁)
    (full_fits lo hlo gs hgs oM oZ kp) hGood (full_inJ lo hlo gs hgs oM oZ kp) (full_counts lo hlo
    gs hgs oM oZ kp) (full_radius lo hlo gs hgs oM oZ kp) (full_fix lo hlo gs hgs oM oZ kp)
    (full_pulls lo hlo gs hgs oM oZ kp) pS Pr base ext err fa (placeFull gs.k) (placeFull_paid gs
    hgs) (full_stage lo hlo gs hgs oM oZ kp) (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl le_rfl
    iE iR (batFull gs.k n) (batFull_paid gs.k n hn57) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl iB

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_full_block
