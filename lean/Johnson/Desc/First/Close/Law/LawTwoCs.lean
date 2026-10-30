-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LawTwoCs.lean (kind K10): `k10_two_sub` (LawTwoSub.lean, beside this
file) AT A LETTER cs FOR THE CODES, WITH cs = `codesFull2` A PREMISE. A definition, a statement and
its proof.

Why. K10's typed group, its payers and `k10_two_sub` stand at the written codes `codesFull2`. The
closed constant's letters (its reader of samples, its members, its meaning, its extractor) are typed
at the codes of the public part's own parameters (`At.cs Zp`, Johnson/P5J/LettersAt.lean). That the
two are one is a sentence at the head; but the types name the codes: a statement that holds both
does not typecheck. Here the codes are a letter: at cs := `At.cs Zp` every letter has the constant's
own type.
  `faLay`: `faK10` at `groupLayK cs lo (stageOf gs 219) radFull kb hM hZ`, under a name.
  `k10_two_cs`: `k10_two_sub`'s statement with cs for `codesFull2` and that group for `groupSub`; hM
    and hZ (the members' codes are the stage's) are letters: any proofs. PROOF: cs is replaced by
    `codesFull2` (hcs); what is left is `k10_two_sub`, by definition.
The statement is LawTwoSub.lean's, turned by program. In the `variable` lines the group is written
out.
Limits. Those of LawTwoSub.lean: AN ASSEMBLY: o may be empty. hcs at the constant is a premise here.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LawTwoSub

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

variable (cs : OnBytes.Codes) (hcs : cs = codesFull2) (lo : List (OracleShape × ℕ))
  (hen : Written lo) (gs : GroupSize) (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = (stageOf gs 219).C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = (stageOf gs 219).Z)

local notation "RF" => groupLayK cs lo (stageOf gs 219) radFull kb hM hZ
local notation "SF" => sigOf cs lo
local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

variable (keep : (sigOf cs lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B] (n : ℕ)
  (num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n) {Kc St₀ Wp : Type} {E₀
      : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB keep
    (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
    (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
        219) radFull kb hM hZ)))
    (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp))
  (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ).sizeB keep
    (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
    (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
        219) radFull kb hM hZ)))
    (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp Wp)

set_option quotPrecheck false in
/-- The caller of the proved batching and fold at the group. -/
local notation "CK" => (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep
  (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
  (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219)
      radFull kb hM hZ)))
  (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull gs.k).bC
  (placeFull gs.k).bZ w₀ w₁

variable {Xi : Type} (Gd : FileDescription Xi) (seat : Fin lo.length → ℕ × ℕ)
  (Nm : SlotNames (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))
  (L : List (BatFoldCaller GE)) {Pz : Type}
  (smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.par.Cw.nat.Str)

/-- `faK10` at the group at a letter for the codes: under a name. -/
noncomputable def faLay : Pz → S1 × F.E.Str →
    ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str :=
  fun z => faK10 Gd cs lo seat RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC
    (placeFull gs.k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z

include hcs hen hgs in
/-- **BOTH CONJUNCTS OF K10's OWN DEBT, AT ONE CONDITION IN FRONT.** -/
theorem k10_two_cs
    (hC : Corners lo gs.k (fun i => layAt (sizesM lo kb) i.val) (fun i => layAt (sizesZ lo) i.val)
      kb)
    (hV : SameVal cs lo smpD fun q j => smpS q ⟨lo, seat⟩ j) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok)
    (pS : ∀ as : (Σ a : (RF).G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → (RF).Sh.Cin.J → GE)
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
    (hrow : Mg.row = rowSays Nu (wordsAtFirst arr)) (hMg : Mg.pin = pinJT cs Gd arr smpS ms)
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
    (hB : SmpBySeat cs smpS)
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
      RowAsks cs lo seat kb RF Nm Nu (p.link.getD 0) O no a.1)
    (hCfX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      ∀ i, CfAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        pS Pr
        (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a →
      K10EndS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        (dBat n) dEps dTwo Pr b base
        (fun a τ w => ((pieceOf (held b) base
          ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo) [] (restCap ex ix _)).withMap
          (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) ((dBat n) :: dEps :: List.replicate (Yc (CK)).k dTwo)))
        (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt RF Nm keep (SbV RF B) (slV RF (pullOf RF)) (ZV RF n num) fx1 A₀
          (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
          (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z a)
          (rdBK a'.1).1.rows)
    (row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT))) (k' : ℕ) (hk' : k' = gs.k)
    (hrw : row[ix]? = some (pieceOf (held b) base ((dBat n) :: dEps :: List.replicate k' dTwo) []
      (restCap ex ix _)))
    (hOn : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      K10OnS RF Nm keep (pullOf RF) n num fx1 A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁ L
        pS Pr (faLay cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpD σ₀ st₀ e₀ mW z) a) :
    ∃ q, row[ix]? = some q ∧ ∃ o : (Pz × S1) × F.E.Str → Prop, (q.withMap
      (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).GoodIn o
      (fun _ => True) (relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k))
      (relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k)) ∧ ∀ s, X s → o s := by
  subst hcs
  exact k10_two_sub lo hen gs hgs kb keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀ e₀ mW hC hV
    arr ms decT c₀ tokOf pS Pr hPr b base ex ix ρ hρ H hn57 Nu Mg links ps k p hp hK X O no hrow hMg
    hins hOut hO hP hSit hAl hB hStay hHit hAlM hGrp hi1 hi2 T1 T2 hU hX hCfX hCar row k' hk' hrw
    hOn

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.faLay
#print axioms VerifiableInference.Desc.First.Close.k10_two_cs
