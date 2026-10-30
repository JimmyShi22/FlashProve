-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10LawFull.lean (kind K10): THE FIELD law OF K10's NAMED CONDITION
(`K10CondAt`, KindK10.lean), IN THE FORM `GoodIn`, AT THE MAKER's PIECE OVER A SEATED SUB-PROTOCOL,
AT THE REAL GROUP OF THE FULL SIZE: THE PROVED SUB-PROTOCOL's PREMISES ON THE TYPED STAGE ARE ALL
PAID. A statement and its proof: one call.

Why. `k10_law_withMap` (KindK10Law.lean, beside this file) gives that `GoodIn` from the proved
batching and fold's own premises on the typed stage (twenty binders), the cap, and one sentence hQ.
`k10_full_block` (K10FullBlock.lean) pays these twenty at `groupFull lo hlo gs hgs oM oZ kp`, but
ends in the form `Leads`, at K10's own sub-protocol. Here the same payers are laid into
`k10_law_withMap`.
  `k10_law_full`: at `groupFull lo hlo gs hgs oM oZ kp`, its own pull, the fixed coefficient (1, 1)
    and the two written places: the piece `pieceOf (held b) base (dB :: dE :: k x dR) [] x` with any
    map e as extractor is `GoodIn` from `K10OnS` at the pair, to `True`, between Rin and Rout.
What is left, by the binders' names: hGood (the group's data are in order: Corners.lean and
CornersKept.lean pay it at the program's own layout) · the three written rounds (dB, dE, dR, ρ, hρ,
iB, iE, iR) · hn57 (n is at most 2^57) · H (b's yes is the frame's closing's: `seated_yes` pays it
at the seated sub-protocol) · hcap (`k10_cap_at`, Johnson/P5J/K10Low.lean, pays it at the seated
piece) · letters: N, keep, B, n, num, A₀, w₀, w₁, L, pS, Pr, base, x, e, fa · AND hQ: K10OnS, the
piece's out and the law's end give: a witness of Rout behind gives, by the piece's extractor, a
witness of Rin in front.
Limits. hQ IS SHOWN NOWHERE. fa is a letter. That the seated term's piece is this piece at these
letters (k against the caller's number of fold rounds; n against the written number of rows) is not
shown here. Through FoldPriced.lean and BatPriced.lean it rests on the files under ThirdParty/
(lean/LIMITS.md, L15). Nothing on an honest prover or on hiding. No soundness statement.

-/
import Johnson.Desc.First.Close.Law.KindK10Law
import Johnson.Desc.First.Close.Law.K10FullBlock

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
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupFull lo hlo gs hgs oM oZ kp).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupFull lo hlo gs hgs oM oZ kp).sizeB keep
    (SbV (groupFull lo hlo gs hgs oM oZ kp) B)
    (slV (groupFull lo hlo gs hgs oM oZ kp) (pullOf (groupFull lo hlo gs hgs oM oZ kp)))
    (ZV (groupFull lo hlo gs hgs oM oZ kp) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFull lo hlo gs hgs oM oZ kp).G ((groupFull lo hlo gs hgs oM oZ kp).sizeB keep
    (SbV (groupFull lo hlo gs hgs oM oZ kp) B)
    (slV (groupFull lo hlo gs hgs oM oZ kp) (pullOf (groupFull lo hlo gs hgs oM oZ kp)))
    (ZV (groupFull lo hlo gs hgs oM oZ kp) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the real group. -/
local notation "CK" => (groupFull lo hlo gs hgs oM oZ kp).foldCaller keep
  (SbV (groupFull lo hlo gs hgs oM oZ kp) B)
  (slV (groupFull lo hlo gs hgs oM oZ kp) (pullOf (groupFull lo hlo gs hgs oM oZ kp)))
  (ZV (groupFull lo hlo gs hgs oM oZ kp) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁

/-- **THE FIELD law AT THE REAL GROUP OF THE FULL SIZE: THE TYPED STAGE IS PAID.** -/
theorem k10_law_full (hGood : (RF).Good) (N : SlotNames RF)
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
  k10_law_withMap RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁
    L dB dE dR ρ hρ (caller_step RF keep _ _ _ A₀ _ _ w₀ w₁)
    (caller_pick RF keep _ _ _ A₀ _ _ w₀ w₁) (full_fits lo hlo gs hgs oM oZ kp) hGood
    (full_inJ lo hlo gs hgs oM oZ kp) (full_counts lo hlo gs hgs oM oZ kp)
    (full_radius lo hlo gs hgs oM oZ kp) (full_fix lo hlo gs hgs oM oZ kp)
    (full_pulls lo hlo gs hgs oM oZ kp) pS Pr b H base x hcap e fa (placeFull gs.k)
    (placeFull_paid gs hgs) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl le_rfl iE iR (batFull gs.k n)
    (batFull_paid gs.k n hn57) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp) le_rfl iB Rin Rout hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_law_full
