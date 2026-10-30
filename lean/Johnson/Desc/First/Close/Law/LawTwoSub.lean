-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LawTwoSub.lean (kind K10): BOTH CONJUNCTS OF K10's OWN DEBT law
(`AtMgA.K10Two`, Johnson/P5J/K10Two.lean: the piece's law at the pick, and the first tie, at one
condition in front), IN LETTERS, AT ANY LIST WHOSE ENTRIES STAND ON WRITTEN LISTS. An assembly:
statements and their proofs: calls.

  `k10_onS_sub`: K10's condition in front `K10OnS` at `faSub`, at one statement: by
    `k10OnS_of_order` (OnOfOrder.lean) with `fa_front_same` (FaTwoReaders.lean) in the place of the
    clause front. FROM: hV (`SameVal`) · hCf (the table's "no collision" at every message of the
    list) · hA (the joint's promise) · hk, hh (the plan's k and h are the stage's) · tied
    (`RowsTied`) · zl (the stage's mask length is at most the layout's) · hI (the statement is in
    order) · code (the statement's mask code has the stage's length).
  `k10_two_sub`: `k10_law_row_sub`'s premises (LawRowSub.lean), and hOn: X gives `K10OnS` at
    `faSub`: THEN there is the row's piece q and A CONDITION o with: `(q.withMap (extQAt ..
    k)).GoodIn o (fun _ => True)` between the table's two relations, AND every statement with X has
    o. At X := "the table's promise, reached, no mark" this is the field's text at one place.
Limits. AN ASSEMBLY: NO PREMISE IS DISCHARGED THAT THE PARTS ASK. hCar, `RowAsks`, tied and the
plan's facts stand. Nothing is shown of any state: o may be empty. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LawRowSub
import Johnson.Desc.First.Close.Law.OnOfOrder

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

/-- **K10's CONDITION IN FRONT AT faSub, AT ONE STATEMENT.** -/
theorem k10_onS_sub (hV : SameVal codesFull2 lo smpD fun q j => smpS q ⟨lo, seat⟩ j)
    (pS : ∀ as : (Σ a : (RF).G.A, ((sigOf codesFull2 lo).om a.1).Z.S),
      ((sigOf codesFull2 lo).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
    (Pr : Par) (z : Pz) (a : S1 × F.E.Str)
    (hCf : ∀ i, CfAt Gd codesFull2 lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hA : A₀.on (st₀, e₀))
    (hk : (planOf (entries Pr) (rdK a.1)).k = (RF).s.h + (RF).s.g)
    (hh : (planOf (entries Pr) (rdK a.1)).h = (RF).s.h)
    (tied : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G →
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
      RowsTied RF n num Nm pS
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a).1.1.1
        (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a).1.2
        (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList)
    (zl : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G →
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
      (RF).s.Z.l ≤ 2 ^ lay.logEllZk)
    (hI : InOrder (rdK a.1).2.2)
    (code : ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK a.1)).maskCode default).ell =
      (RF).s.Z.l) :
    K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L pS
      Pr (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a :=
  k10OnS_of_order RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁
    L pS Pr _ a hk hh
    (fa_front_same Gd codesFull2 lo seat RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
      (placeFull gs.k).bZ w₀ w₁ L smpD (fun q j => smpS q ⟨lo, seat⟩ j) σ₀ st₀ e₀ mW hV z a hCf hA)
    tied zl hI code

/-- **BOTH CONJUNCTS OF K10's OWN DEBT, AT ONE CONDITION IN FRONT.** -/
theorem k10_two_sub
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
      (restCap ex ix _)))
    (hOn : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        pS Pr (faSub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a) :
    ∃ q, row[ix]? = some q ∧ ∃ o : (Pz × S1) × F.E.Str → Prop, (q.withMap
      (extQAt codesFull2 Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).GoodIn o
      (fun _ => True) (relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k))
      (relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k)) ∧ ∀ s, X s → o s := by
  obtain ⟨q, hq, hG⟩ := k10_law_row_sub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD
    σ₀ st₀ e₀ mW hC hV arr ms decT c₀ tokOf pS Pr hPr b base ex ix ρ hρ H hn57 Nu Mg links ps k p
    hp hK X O no hrow hMg hins hOut hO hP hSit hAl hB hStay hHit hAlM hGrp hi1 hi2 T1 T2 hU hX hCfX
    hCar row k' hk' hrw
  exact ⟨q, hq, _, hG, fun s hs => ⟨hOn s.1.1 (s.1.2, s.2) hs, hs⟩⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_onS_sub
#print axioms VerifiableInference.Desc.First.Close.k10_two_sub
