-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarField.lean: THE TEXT OF THE FIELD hCar OF THE CLOSING's FILES'
STRUCTURE `K10Heavy` (Johnson/Desc/First/Close/Law/K10Heavy.lean) UNDER A NAME, at that structure's
  own
45 letters in their order: so that the field can be stated at the closed constant's letters by an
application, without its text being typed a third time. The text is cut out of K10Heavy.lean by
program. A definition and a theorem.

  `HCarField ..`: the field's text.
  `K10Heavy.hCar_field`: the structure's field gives it, by Lean's own unfolding: so the text is the
    field's type.
Limits. Book-keeping. Nothing on soundness.
-/
import Johnson.Desc.First.Close.Law.K10Heavy

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
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowSays wordsAtFirst laysSeats)

local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

/-- The field hCar's text. -/
def HCarField
    (cs : OnBytes.Codes)
    (lo : List (OracleShape × ℕ))
    (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = (stageOf gs
      219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = (stageOf gs
      219).Z)
    (keep : (sigOf cs lo).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf cs lo).Wit × Wp)
    (w₁ : LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
      (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp
      Wp)
    {Xi : Type}
    (Gd : FileDescription Xi)
    (seat : Fin lo.length → ℕ × ℕ)
    (Nm : SlotNames (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))
    (L : List (BatFoldCaller GE))
    {Pz : Type}
    (smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) → Option
      ((sigOf cs s.l).om i).Smp)
    (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
    (σ₀ : (sigOf cs lo).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    {F : Frame}
    (mW : S1 × F.E.Str → (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.par.Cw.nat.Str)
    {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells)
    (c₀ : Cells)
    (tokOf : Pz × S1 → Tok)
    (pS : ∀ as : (Σ a : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.A, ((sigOf cs lo).om
      a.1).Z.S), ((sigOf cs lo).om as.1.1).Z.D →
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block S1 Cl)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → Wit Cells
      Tok MsgT → Wit Cells Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM
    hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf
    gs 219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
    gs.k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo))
    (Nu : Numbers)
    (Mg : Meaning Pz (Wit Cells Tok MsgT))
    (links : List ModelPart)
    (ps : List Place)
    (k : ℕ)
    (p : Place)
    (X : (Pz × S1) × F.E.Str → Prop)
    (O : List Item)
    (no : Fin lo.length → ℕ)
    (row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT)))
    (k' : ℕ) : Prop :=
  ∀ z a a', X ((z, a.1), a.2) → K10OnS (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) Nm
    keep (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)) n num fx1 A₀ (placeFull
    gs.k).bC (placeFull gs.k).bZ w₀ w₁ L pS Pr (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat
    Nm L smpD σ₀ st₀ e₀ mW z) a → K10EndS (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) Nm
      keep (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)) n num fx1 A₀ (placeFull
    gs.k).bC
    (placeFull gs.k).bZ w₀ w₁ L (dBat n) dEps dTwo Pr b base (fun a τ w => ((pieceOf (held b) base
    ((dBat n) :: dEps :: List.replicate (Yc ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).foldCaller keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219)
    radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num) ((1 : Fin 3),
    (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dTwo) [] (restCap ex ix
    _)).withMap (extQAt cs
    Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext ((z, a.1), a.2) τ w) (Err.cap 128
    (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc ((groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
    (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
    219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num) ((1 :
    Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁)).k dTwo))) (faLay cs lo gs
    kb hM hZ
    keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a a' → ∀ w, relAt (meansQ (Fr := F) Nu Mg
    fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w → CarriedAt (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ) Nm keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)
    (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ) n num) fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L (faLay cs
    lo
    gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a) (rdBK a'.1).1.rows

theorem K10Heavy.hCar_field
    {cs : OnBytes.Codes}
    {lo : List (OracleShape × ℕ)}
    {gs : GroupSize}
    {kb : Fin lo.length → Bool}
    {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = (stageOf gs
      219).C}
    {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = (stageOf gs
      219).Z}
    {keep : (sigOf cs lo).O → Prop}
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    {n : ℕ}
    {num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n}
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    {A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp)}
    {w₀ : (sigOf cs lo).Wit × Wp}
    {w₁ : LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
      (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp
      Wp}
    {Xi : Type}
    {Gd : FileDescription Xi}
    {seat : Fin lo.length → ℕ × ℕ}
    {Nm : SlotNames (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)}
    {L : List (BatFoldCaller GE)}
    {Pz : Type}
    {smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) → Option
      ((sigOf cs s.l).om i).Smp}
    {smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp}
    {σ₀ : (sigOf cs lo).Smp}
    {st₀ : St₀}
    {e₀ : E₀.Str}
    {F : Frame}
    {mW : S1 × F.E.Str → (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.par.Cw.nat.Str}
    {Cells Tok : Type}
    {arr : ℕ → ℕ → ℕ}
    {ms : List Mem}
    {decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells}
    {c₀ : Cells}
    {tokOf : Pz × S1 → Tok}
    {pS : ∀ as : (Σ a : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.A, ((sigOf cs lo).om
      a.1).Z.S), ((sigOf cs lo).om as.1.1).Z.D →
      (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE}
    {Cl : Type}
    {Pr : Par}
    {b : Block S1 Cl}
    {base : ℕ}
    {ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → Wit Cells
      Tok MsgT → Wit Cells Tok MsgT}
    {ix : ℕ}
    {ρ : Rd ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM
    hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf
    gs 219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
    gs.k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo)}
    {Nu : Numbers}
    {Mg : Meaning Pz (Wit Cells Tok MsgT)}
    {links : List ModelPart}
    {ps : List Place}
    {k : ℕ}
    {p : Place}
    {X : (Pz × S1) × F.E.Str → Prop}
    {O : List Item}
    {no : Fin lo.length → ℕ}
    {row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT))}
    {k' : ℕ}
    (Hv : K10Heavy cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀ e₀ mW arr ms
      decT c₀ tokOf pS Pr b base ex ix ρ Nu Mg links ps k p X O no row k') :
    HCarField cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀ e₀ mW arr ms decT
      c₀ tokOf pS Pr b base ex ix ρ Nu Mg links ps k p X O no row k' := Hv.hCar

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.K10Heavy.hCar_field
