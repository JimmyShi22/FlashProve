-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LawAtSub.lean (kind K10): THE PIECE's LAW `GoodIn` AT THE MAKER's PIECE
OVER K10's SUB-PROTOCOL, WITH THE TABLE OF JOINTS' OWN EXTRACTOR LAID IN, BETWEEN THE TABLE's OWN
TWO RELATIONS, AT THE GROUP OF ANY LIST WHOSE ENTRIES STAND ON THE WRITTEN LISTS, AND THE CONCRETE
fa: `k10_law_at_fa`'s LIKE (LawAtFa.lean [not in this library]), GENERAL IN THE LIST. An assembly:
a definition, a statement and its proof.

Why. At a written list the law (`k10_law_at_fa`, LawAtFa.lean [not in this library]) is idle at link
0 (said here without a theorem): its premise hCar asks a witness for the word of the one message of
the written list that is no member of the group. At the list without that message (`loFive`,
LinkZeroFive.lean) every message is a member. `k10_law_sub` (GroupSub.lean) has the law there from
hQ; `k10_hQ_at_fa` (HQAtFa.lean) is general in the list.
  `faSub`: `faK10` at RF := `groupSub lo hen gs hgs kb`, under a name.
  `k10_law_at_sub`: `((pieceOf (held b) base (dB :: dE :: k x dR) [] x).withMap (extQAt ..
    k)).GoodIn (fun a => K10OnS .. (faSub .. a.1.1) (a.1.2, a.2) ∧ X a) (fun _ => True) (the table's
    relation at insQ) (the table's relation at outsQ)`. That RF is `groupLayK` at the full size's
    letters holds by definition. At a written list `hen` is `written_of_mem`'s (GroupSub.lean).
This file's text is made by program. In the `variable` lines the group is written out.
Limits. AN ASSEMBLY: all of `k10_hQ_at_fa`'s premises stand but hR and hg, and `k10_law_sub`'s own
(the corners' test; the three rounds' formats; n ≤ 2 ^ 57; H; hcap). hCar stays a premise. THE FIRST
TIE (the promise gives `K10OnS`) is not touched. Nothing is shown of any state. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.GroupSub
import Johnson.Desc.First.Close.Law.HQAtFa

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

/-- `faK10` at the group of a list of written entries: under a name. -/
noncomputable def faSub : Pz → S1 × F.E.Str →
    ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str :=
  fun z => faK10 Gd codesFull2 lo seat RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
    (placeFull gs.k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z

/-- **THE PIECE's LAW, AT THE TABLE's OWN TERMS.** -/
theorem k10_law_at_sub
    (hC : Corners lo gs.k (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
      kb)
    (hV : SameVal codesFull2 lo smpD fun q j => smpS q ⟨lo, seat⟩ j) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : (RF).G.A, ((sigOf codesFull2 lo).om a.1).Z.S),
      ((sigOf codesFull2 lo).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (hPr : Pr.k = (RF).s.h + (RF).s.g) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc (CK)).k dR))
    (ρ : Rd (CK) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd (CK) dB dE dR (oneOf id) (oneOf id))
    (H : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (hcap : x.err = Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR)))
    {na nb : String} (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hn57 : n ≤ 2 ^ 57) (iB : IsRd (toRD dB) (Fmt.M2.rBatN n))
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
        dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) []
          x).withMap
          (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (CK)).k dR)))
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt RF Nm keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
          (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
          (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a)
          (rdBK a'.1).1.rows) :
    ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc (CK)).k dR) [] x).withMap
      (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).GoodIn
      (fun a => K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ
        w₀ w₁ L pS Pr
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW a.1.1)
        (a.1.2, a.2) ∧ X a)
      (fun _ => True) (relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k))
      (relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k)) :=
  goodIn_beside _ _ _ X _ _
    (k10_law_sub lo hen gs hgs kb keep n num A₀ w₀ w₁ hC Nm L dB dE dR ρ hρ pS Pr b H base x
      hcap (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)
      (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW) iE iR hn57 iB
      (fun a w => X a → relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k) a w)
      (relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k))
      (k10_hQ_at_fa Gd codesFull2 lo seat (stageOf gs 219) radFull kb (hMSub lo hen gs hgs)
        (hZSub lo hen gs hgs) RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
        (placeFull gs.k).bZ w₀ w₁ L smpS smpD σ₀ st₀ e₀ mW hV rfl
        (sub_good_of_corners lo hen gs hgs _ _ kb hC) arr ms decT c₀ tokOf dB dE dR pS Pr hPr b
        base x Nu Mg links ps k p hp hK X O no hrow hMg hins hOut hO hP hSit hAl hB hStay hHit hAlM
        hGrp hi1 hi2 T1 T2 hU hX hCfX hCar))

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.faSub
#print axioms VerifiableInference.Desc.First.Close.k10_law_at_sub
