-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/HQAtFa.lean (kind K10): THE SENTENCE hQ OF K10's LAW AT THE MAKER's
PIECE, IN ONE THEOREM: AT THE CONCRETE fa (`faK10`) THAT LAYS THE DRAWN SEEDS, THE TABLE OF JOINTS'
OWN EXTRACTOR AND ITS OWN TWO RELATIONS, WITH A FACT X ON THE STATEMENT IN FRONT BESIDE. An
assembly: a statement and its proof.

Why. hQ is the whole of what ties K10's law to the table (GoodOf.lean's Limits). Its parts have been
typed in several files: the skeleton (`k10_hQ_beside`, HQBeside.lean); the rows (`k10_hRow_drawn`,
HRowDrawn.lean); the pins (`k10_hpin`, HpinAtTable.lean, of `fa_pin_ext` and `pin_kept_behind`).
Whether their forms meet is a question for Lean.
  `k10_hPin_any`: hPin of `k10_hQ_beside`, general in fa, from hpin (`k10_hPin`, HPinAtFa.lean,
    stands at the table's own reader of samples; its proof reads nothing of fa).
  `k10_hQ_at_fa`: hQ, to the letter of `k10_law_withMap`, at fa := `faK10 .. smpD ..`, e := `extQAt
    .. k`, Rin := fun a w => X a → (the table's relation at insQ), Rout := the table's relation at
    outsQ.
WHAT IS LEFT, BY SORT. On letters: hR, hg, hPr (the typed group) · hrow, hMg (the meaning's "row"
and "pin": at the composed meaning by definition) · hV, hB, hStay (the readers of samples). On the
table's lists and the plan: hp, hK, hins, hOut, hO, hP, hSit, hAl, hHit, hAlM, hGrp, hi1, hi2, T1,
T2. On the statement in front, under X: hU (no mark) · hX (`RowAsks`: ten fields) · hCfX (the
table's "no collision" at every member of the list). ACROSS THE STEP: hCar (X, the law's condition,
its end and the relation behind give `CarriedAt`).
Limits. AN ASSEMBLY: NO PREMISE IS DISCHARGED HERE THAT THE PARTS ASK. hCar IS THE ONE DEEP DEBT:
shown nowhere. Nothing is shown of any state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HRowDrawn
import Johnson.Desc.First.Close.Law.HpinAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open Johnson.G (memMain)
open OnBytes.Means (InOrder tableSize)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowsHeld membersHeld PlacesApart
  rowSays wordsAtFirst laysSeats)

variable {Xi : Type} (Gd : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (s : Sg) (e' : ℕ) (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)

variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))

local notation "S1" => VerifiableInference.Desc.First.S

/-- The typed stage's caller. -/
local notation "cK10" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

variable {Pz : Type}
  (smpS : Pz × S1 → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **hPin OF k10_hQ_beside, GENERAL IN fa.** -/
theorem k10_hPin_any {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
    (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (fa : Pz → S1 × F.E.Str → ((kBatFoldRide L).src cK10).X × ((kBatFoldRide L).src cK10).E.Str)
    (Nu : Numbers) (Mg : Meaning Pz (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (k m : ℕ) (X : (Pz × S1) × F.E.Str → Prop)
    (hMg : Mg.pin = pinJT cs Gd arr smpS ms)
    (hSit : ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t, ∃ y ∈ ms, SitsAt y s.1 s.2)
    (hAl : ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t, ∀ y ∈ ms, SitsAt y s.1 s.2 →
      ∃ i : Fin lo.length, memMain lo i ∧ Alike y ⟨⟨lo, seat⟩, i⟩)
    (hB : SmpBySeat cs smpS)
    (hpin : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ i, memMain lo i → PinAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) arr i (z, a.1)
          (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)) :
    ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t,
          Mg.pin s.1 s.2 (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w) := by
  intro z a a' hx hon hend w hw t ht s hs
  rw [hMg]
  refine ⟨hSit t ht s hs, fun y hy hy' => ?_⟩
  obtain ⟨i, hmi, hal⟩ := hAl t ht s hs y hy hy'
  exact (pin_move cs Gd arr smpS y ⟨⟨lo, seat⟩, i⟩ hal (z, a.1) (hB (z, a.1) y ⟨⟨lo, seat⟩, i⟩ hal)
    (strsOf F a.2) _).2 (hpin z a a' hx hon hend w hw i hmi)

/-- **hQ, IN ONE THEOREM.** -/
theorem k10_hQ_at_fa (hV : SameVal cs lo smpD fun q j => smpS q ⟨lo, seat⟩ j)
    (hR : R = groupLayK cs lo s e' kb hM hZ) (hg : R.Good) {Cells Tok : Type}
    (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells) (c₀ : Cells)
    (tokOf : Pz × S1 → Tok) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((sigOf cs lo).om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl : Type} (Pr : Par) (hPr : Pr.k = R.s.h + R.s.g) (b : Block S1 Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1) (Wit Cells Tok MsgT)
      (dB :: dE :: List.replicate (Yc cK10).k dR))
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
    (hStay : ∀ z s s', K10Step s s' → ∀ (y : Sending) (i : Fin y.l.length),
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
      RowAsks cs lo seat kb R N Nu (p.link.getD 0) O no a.1)
    (hCfX : ∀ z (a : S1 × F.E.Str), X ((z, a.1), a.2) →
      ∀ i, CfAt Gd cs lo seat (fun q => smpS q ⟨lo, seat⟩) i (z, a.1) (strsOf F a.2))
    (hCar : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L
          (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z a)
          (rdBK a'.1).1.rows) :
    ∀ z a τ a', K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a →
      (pieceOn (W := Wit Cells Tok MsgT) (F := F) b base dB dE dR (Yc cK10).k
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc cK10).k dR)))).ior.red.out a τ = some a' →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
          ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
        (faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        (fun (a : (Pz × S1) × F.E.Str) (w : Wit Cells Tok MsgT) =>
          X a → relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k) a w) ((z, a.1), a.2)
          (((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).withMap
            (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)).ext
            ((z, a.1), a.2) τ w) := by
  have hpin := k10_hpin Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS smpD σ₀ st₀ e₀ mW
    arr ms decT c₀ tokOf dB dE dR pS Pr b base x Nu Mg links ps k p hp hK X hMg hOut hV hB hStay
    hHit hAlM hGrp hi1 hi2 T1 T2 hCfX hCar
  exact k10_hQ_beside R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR pS Pr b base x
    (extQAt cs Gd arr smpS ms decT c₀ tokOf Nu links ps (fun a => a) k)
    (fun z => faK10 Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z)
    Nu Mg links ps k (p.link.getD 0) X hins hU
    (k10_hRow_drawn Gd cs lo seat s e' kb hM hZ R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS smpD
      σ₀ st₀ e₀ mW hV hR hg arr dB dE dR pS Pr hPr b base x _ Nu Mg links ps k (p.link.getD 0) X O
      no hrow hO hP hX (fun z a hx i => by
        obtain ⟨zz, hz, -, -⟩ := hCfX z a hx i
        exact ⟨zz, hz⟩) hCar hpin)
    (k10_hPin_any Gd cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpS arr ms dB dE dR pS Pr
      b base x _ _ Nu Mg links ps k (p.link.getD 0) X hMg hSit hAl hB hpin)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_hPin_any
#print axioms VerifiableInference.Desc.First.Close.k10_hQ_at_fa
