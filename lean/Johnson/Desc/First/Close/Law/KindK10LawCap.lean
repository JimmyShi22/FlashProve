-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/KindK10LawCap.lean (kind K10): `k10_law_full_lay` (KindK10LawLay.lean,
beside this file) AT THE DATA AND THE REST THAT THE MAKER's OWN PIECE BEARS: the three rounds' data
are the written ones (`dBat n`, `dEps`, `dTwo`, CutAtK10.lean), the rest is `restCap ex i` (an
extractor and the cap, Johnson/Desc/Sound/BoundsAtCap.lean); AND AT A ROW OF PIECES THAT HOLDS THAT
PIECE. Statements and their proofs: calls.

  `yc_k_full`: the proved fold's number of rounds at the real group is the group in front's k.
  `k10_law_at_cap`: `k10_law_full_lay`'s end at these letters: its premises hcap, iB, iE, iR FALL
(by
    definition; `dBat_is`, `dEps_is`, `dTwo_is`).
  `k10_law_at_row`: **where a row's piece number i IS `pieceOf (held b) base (dBat n :: dEps :: k'
times
    dTwo) [] (restCap ex i ..)` and k' = gs.k: that piece, with the map e laid on its extractor, has
    `GoodIn`** in `k10_law_full_lay`'s letters.
  `num_exists`: a numbering num of the rows, for a claim of n less the samples' rows: there is one
    wherever the group's samples' rows are at most n.
Limits. Those of KindK10LawLay.lean: hQ IS SHOWN NOWHERE; fa is a letter. How many samples' rows the
real group has at a link, and that they are at most the place's number of batched rows, is not
shown. No soundness statement.

-/
import Johnson.Desc.First.Close.Law.KindK10LawLay
import Johnson.Desc.First.Close.Law.CutAtK10
import Johnson.Desc.Sound.BoundsAtCap

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


/-- The proved fold's number of rounds is the group in front's k. -/
theorem yc_k_full : (Yc (CK)).k = gs.k := by
  have es := (frontFull_place gs hgs).2
  show (Johnson.Top.H.stageOf gs 219).h + (Johnson.Top.H.stageOf gs 219).g = gs.k
  rw [← es]
  show 0 + gs.k = gs.k
  omega

/-- **THE FIELD law AT THE WRITTEN DATA AND THE CAP.** -/
theorem k10_law_at_cap (hk : gs.k = kLay lo kb) (N : SlotNames RF)
    {Pz : Type} (L : List (BatFoldCaller GE))
    (ρ : Rd (CK) (wT (dBat n)) (wT dEps) (wT dTwo))
    (hρ : ρ = realRd (CK) (dBat n) dEps dTwo (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1 Cl)
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → W → W)
    (i : ℕ) (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → W → W)
    (fa : Pz → S1 × F.E.Str → ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str)
    (hn57 : n ≤ 2 ^ 57)
    (Rin Rout : (Pz × S1) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base (dBat n) dEps dTwo (Yc (CK)).k
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap ex i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)))).ior.red.out a τ = some a' →
      K10EndS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        (dBat n) dEps dTwo Pr b base
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap ex i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo))) (fa z)
    a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo) [] (restCap
    ex i _)).withMap e).ext
          ((z, a.1), a.2) τ w)) :
    ((pieceOf (held b) base (dBat n :: dEps :: List.replicate (Yc (CK)).k dTwo) []
      (restCap ex i _)).withMap e).GoodIn
      (fun a => K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  k10_law_full_lay lo hlo gs hgs kb keep n num A₀ w₀ w₁ hk N L (dBat n) dEps dTwo ρ hρ pS Pr b H
    base (restCap ex i _) rfl e fa dEps_is dTwo_is hn57 (dBat_is n) Rin Rout hQ

/-- **AT A ROW OF PIECES THAT HOLDS THE MAKER's PIECE.** -/
theorem k10_law_at_row (hk : gs.k = kLay lo kb) (N : SlotNames RF)
    {Pz : Type} (L : List (BatFoldCaller GE))
    (ρ : Rd (CK) (wT (dBat n)) (wT dEps) (wT dTwo))
    (hρ : ρ = realRd (CK) (dBat n) dEps dTwo (oneOf id) (oneOf id))
    (pS : ∀ as : (Σ a : (RF).G.A, ((SF).om a.1).Z.S), ((SF).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1 Cl)
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → W → W)
    (i : ℕ) (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → W → W)
    (fa : Pz → S1 × F.E.Str → ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str)
    (hn57 : n ≤ 2 ^ 57)
    (Rin Rout : (Pz × S1) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base (dBat n) dEps dTwo (Yc (CK)).k
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap ex i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)))).ior.red.out a τ = some a' →
      K10EndS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        (dBat n) dEps dTwo Pr b base
        (fun a τ w => ((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)
    []
          (restCap ex i _)).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo))) (fa z)
    a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo) [] (restCap
    ex i _)).withMap e).ext
          ((z, a.1), a.2) τ w))
    (row : List (Piece (ckP .two) F (Pz × S1) Cl W)) (k' : ℕ) (hk' : k' = gs.k)
    (hrow : row[i]? = some (pieceOf (held b) base (dBat n :: dEps :: List.replicate k' dTwo) []
      (restCap ex i _))) :
    ∃ q, row[i]? = some q ∧ (q.withMap e).GoodIn
      (fun a => K10OnS RF N keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout := by
  have hy : (Yc (CK)).k = k' :=
    (yc_k_full lo hlo gs hgs kb keep n num A₀ w₀ w₁).trans hk'.symm
  subst hy
  exact ⟨_, hrow, k10_law_at_cap lo hlo gs hgs kb keep n num A₀ w₀ w₁ hk N L ρ hρ pS Pr b H base ex
    i e fa hn57 Rin Rout hQ⟩

/-- **A numbering of the rows, for a claim of n less the samples' rows.** -/
theorem num_exists [Fintype (Σ a : (RF).G.A, ((SF).om a.1).Z.S)]
    (hc : Fintype.card (Σ a : (RF).G.A, ((SF).om a.1).Z.S) ≤ n) :
    Nonempty ((RF).G.Row (Fin (n - Fintype.card (Σ a : (RF).G.A, ((SF).om a.1).Z.S))) ≃ Fin n) := by
  refine ⟨Fintype.equivFinOfCardEq ?_⟩
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.num_exists
#print axioms VerifiableInference.Desc.First.Close.yc_k_full
#print axioms VerifiableInference.Desc.First.Close.k10_law_at_cap
#print axioms VerifiableInference.Desc.First.Close.k10_law_at_row
