-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LawRowSub.lean (kind K10): `k10_law_at_sub` (LawAtSub.lean, beside this
file) AT THE DATA AND THE REST THAT THE MAKER's OWN PIECE BEARS, AND AT A ROW OF PIECES THAT HOLDS
THAT PIECE. Statements and their proofs: calls.

Why. KindK10LawCap.lean has this step for `k10_law_full_lay`, at a written list, with
hQ a premise. Here it is taken for the assembled law, at any list whose entries stand on written
lists: so that one theorem serves K10's 25 places, link 0's five-list among them.
  `yc_k_sub`: the proved fold's number of rounds at `groupSub` is the group in front's k: general in
    keep and in the kept messages' joint A₀.
  `k10_law_row_sub`: the three rounds' data are the written ones (`dBat n`, `dEps`, `dTwo`,
    CutAtK10.lean); the rest is `restCap ex ix` (an extractor and the cap,
    Johnson/Desc/Sound/BoundsAtCap.lean): `k10_law_at_sub`'s premises hcap, iB, iE, iR fall (by
    definition; `dBat_is`, `dEps_is`, `dTwo_is`). WHERE A ROW's PIECE NUMBER ix IS `pieceOf (held b)
    base (dBat n :: dEps :: k' times dTwo) [] (restCap ex ix ..)` AND k' = gs.k: THAT PIECE, with
    the table's extractor laid on its own, has `GoodIn (K10OnS .. ∧ X) (fun _ => True)` between the
    table's two relations.
The statement is LawAtSub.lean's, turned by program; every turn fails aloud where its anchor lacks.
Limits. AN ASSEMBLY: those of LawAtSub.lean. That a seated row holds that piece is a premise
(`k10_row_at` has it at the constant). Nothing is shown of any state. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.LawAtSub
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
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowSays wordsAtFirst laysSeats)

variable (lo : List (OracleShape × ℕ)) (hen : Written lo) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)

local notation "RF" => groupSub lo hen gs hgs kb
local notation "SF" => sigOf codesFull2 lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupSub lo hen gs hgs kb).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub ((groupSub lo hen gs hgs kb).sizeB keep
    (SbV (groupSub lo hen gs hgs kb) B)
    (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
    (ZV (groupSub lo hen gs hgs kb) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSub lo hen gs hgs kb).G ((groupSub lo hen gs hgs kb).sizeB keep
    (SbV (groupSub lo hen gs hgs kb) B)
    (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
    (ZV (groupSub lo hen gs hgs kb) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the group. -/
local notation "CK" => (groupSub lo hen gs hgs kb).foldCaller keep
  (SbV (groupSub lo hen gs hgs kb) B)
  (slV (groupSub lo hen gs hgs kb) (pullOf (groupSub lo hen gs hgs kb)))
  (ZV (groupSub lo hen gs hgs kb) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁

variable {Xi : Type} (Gd : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ)
  (Nm : SlotNames (groupSub lo hen gs hgs kb))
  (L : List (BatFoldCaller GE)) {Pz : Type}
  (smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
    Option ((sigOf codesFull2 s.l).om i).Smp)
  (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf codesFull2 lo).om i).Smp)
  (σ₀ : (sigOf codesFull2 lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → (groupSub lo hen gs hgs kb).Sh.par.Cw.nat.Str)

/-- The proved fold's number of rounds is the group in front's k. -/
theorem yc_k_sub : (Yc (CK)).k = gs.k := by
  have es := (frontFull_place gs hgs).2
  show (Johnson.Top.H.stageOf gs 219).h + (Johnson.Top.H.stageOf gs 219).g = gs.k
  rw [← es]
  show 0 + gs.k = gs.k
  omega

/-- **AT A ROW OF PIECES THAT HOLDS THE MAKER's PIECE.** -/
theorem k10_law_row_sub
    (hC : Corners lo gs.k (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
      kb)
    (hV : SameVal codesFull2 lo smpD fun q j => smpS q ⟨lo, seat⟩ j) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok)
    (pS : ∀ as : (Σ a : (RF).G.A, ((sigOf codesFull2 lo).om a.1).Z.S),
      ((sigOf codesFull2 lo).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (hPr : Pr.k = (RF).s.h + (RF).s.g) (b : Block S1 Cl) (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) →
      Wit Cells Tok MsgT → Wit Cells Tok MsgT) (ix : ℕ)
    (ρ : Rd (CK) (wT (dBat n)) (wT dEps) (wT dTwo))
    (hρ : ρ = realRd (CK) (dBat n) dEps dTwo (oneOf id) (oneOf id))
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (hn57 : n ≤ 2 ^ 57)
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hK : p.kind = .K10)
    (X : (Pz × S1) × F.E.Str → Prop) (O : List Item) (no : Fin lo.length → ℕ)
    (hrow : Mg.row = rowSays Nu (wordsAtFirst arr)) (hMg : Mg.pin = pinJT codesFull2 Gd arr smpS ms)
    (hins : ∀ i, insQ links ps k i → (∃ c, i = Item.row (p.link.getD 0) c) ∨
      (∃ t, i = Item.pin (p.link.getD 0) t) ∨ i = Item.unmarked)
    (hOut : outsQ links ps k (Item.pinKept (p.link.getD 0)))
    (hO : ∀ c, insQ links ps k (Item.row (p.link.getD 0) c) → Item.row (p.link.getD 0) c ∈ O)
    (hP : ∀ t, Item.row (p.link.getD 0) (.sample t) ∈ O →
      t < 3 ∧ Item.pin (p.link.getD 0) t ∈ O)
    (hSit : ∀ t, insQ links ps k (Item.pin (p.link.getD 0) t) →
      ∀ s ∈ Nu.sent (p.link.getD 0) t, ∃ y ∈ ms, SitsAt y s.1 s.2)
    (hAl : ∀ t, insQ links ps k (Item.pin (p.link.getD 0) t) →
      ∀ s ∈ Nu.sent (p.link.getD 0) t, ∀ y ∈ ms, SitsAt y s.1 s.2 →
        ∃ i : Fin lo.length, memMain lo i ∧ Alike y ⟨⟨lo, seat⟩, i⟩)
    (hB : SmpBySeat codesFull2 smpS)
    (hStay : ∀ z s s', K10Step s s' →
      ∀ (y : VerifiableInference.Desc.Sound.Sending) (i : Fin y.l.length),
      smpS (z, s') y i = smpS (z, s) y i)
    (hHit : ∀ i, memMain lo i → ∃ y ∈ ms, Alike y ⟨⟨lo, seat⟩, i⟩)
    (hAlM : ∀ y ∈ mineAt ms Nu links p, ∃ i : Fin lo.length, Alike y ⟨⟨lo, seat⟩, i⟩)
    (hGrp : ∀ i, memMain lo i →
      seat i ∈ laysSeats Nu links p ∨ seat i ∈ Nu.keptOf (p.link.getD 0))
    (hi1 : ∀ i i' : Fin lo.length,
      arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → i = i')
    (hi2 : Function.Injective seat)
    (T1 : keptApartB arr Nu links p = true) (T2 : keptLowB Nu (p.link.getD 0) base = true)
    (hU : ∀ a, X a → a.1.2.failed = none)
    (hX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      RowAsks codesFull2 lo seat kb RF Nm Nu (p.link.getD 0) O no a.1)
    (hCfX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      ∀ i, CfAt Gd codesFull2 lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        pS Pr
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a →
      K10EndS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        (dBat n) dEps dTwo Pr b base
        (fun a τ w => ((pieceOf (held b) base
          ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo) [] (restCap ex ix _)).withMap
          (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)))
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt RF Nm keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
          (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
          (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a)
          (rdBK a'.1).1.rows)
    (row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT))) (k' : ℕ) (hk' : k' = gs.k)
    (hrw : row[ix]? = some (pieceOf (held b) base ((dBat n) :: dEps :: List.replicate k' dTwo) []
      (restCap ex ix _))) :
    ∃ q, row[ix]? = some q ∧ (q.withMap
      (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).GoodIn
      (fun a => K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW a.1.1)
        (a.1.2, a.2) ∧ X a)
      (fun _ => True) (relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k))
      (relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k)) := by
  have hy : (Yc (CK)).k = k' := (yc_k_sub lo hen gs hgs kb keep n num A₀ w₀ w₁).trans hk'.symm
  subst hy
  exact ⟨_, hrw, k10_law_at_sub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀
    e₀ mW hC hV arr ms decT c₀ tokOf (dBat n) dEps dTwo pS Pr hPr b base (restCap ex ix _) ρ hρ H
    rfl dEps_is dTwo_is hn57 (dBat_is n) Nu Mg links ps k p hp hK X O no hrow hMg hins hOut hO hP
    hSit hAl hB hStay hHit hAlM hGrp hi1 hi2 T1 T2 hU hX hCfX hCar⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.yc_k_sub
#print axioms VerifiableInference.Desc.First.Close.k10_law_row_sub
