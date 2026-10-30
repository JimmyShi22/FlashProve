-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/HQBeside.lean (kind K10): WHOEVER PAYS hQ MAY SPEND A FACT ON THE
STATEMENT IN FRONT THAT STANDS BESIDE K10's LAW's OWN CONDITION. Statements and proofs.

Why. hQ of `k10_law_withMap` (KindK10Law.lean, beside this file) has, of the statement in front,
`K10OnS` alone. Its parts want more of that statement: that the state holds each member's sample and
every leaf is shown (the pins); that the statement is in order and the table's own tests on the rows
hold (the rows); that there is no mark. All these stand in the table's promise in front. The
condition in front o of `K10CondAt` (KindK10.lean) is bound by "there is": it may be `K10OnS` AND
such a fact X.
  `goodIn_beside` (general in the piece): `GoodIn on on' (fun a w => X a → R a w) R'` gives `GoodIn
    (fun a => on a ∧ X a) on' R R'`. By `Doomed.mono`.
  `k10_hQ_beside`: `k10_hQ_of_parts` (HQOfParts.lean) with X: hQ, to the letter of
    `k10_law_withMap`, at Rin := fun a w => X a → (the table's relation at insQ): FROM hins; hU (X
    gives "no mark"); hRow and hPin, each with X at the statement in front in hand.
So: `k10_law_withMap` (or what stands over it) at that Rin, then `goodIn_beside`: `GoodIn (K10OnS ..
∧ X) True (the table's two relations)`: the field law of `K10CondAt` at o := `K10OnS` ∧ X; the field
front then asks `K10OnS` and X of the promise.
Limits. GLUE. hRow and hPin are hQ's whole content: shown nowhere here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.HQOfParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart)
open VerifiableInference.Desc (Place)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- The typed stage's caller. -/
local notation "cK10" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

/-- The first chain's state. -/
local notation "S1st" => VerifiableInference.Desc.First.S

/-- **A fact on the statement in front can stand beside the condition.** -/
theorem goodIn_beside {St Cl W : Type} {C : _root_.Run.PQ.CK} {F : Frame} (p : Piece C F St Cl W)
    (on on' X : St × F.E.Str → Prop) (Rf Rb : St × F.E.Str → W → Prop)
    (g : p.GoodIn on on' (fun a w => X a → Rf a w) Rb) :
    p.GoodIn (fun a => on a ∧ X a) on' Rf Rb := fun a ha =>
  Doomed.mono _ _ (fun _ hτ b hb => ⟨(hτ b hb).1, fun w hw => (hτ b hb).2 w hw ha.2⟩) (g a ha.1)

/-- **hQ WITH A FACT BESIDE, FROM ITS PARTS.** -/
theorem k10_hQ_beside {Pz : Type} (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1st Cl) (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1st) W (dB :: dE :: List.replicate (Yc cK10).k dR))
    (e : (Pz × S1st) × F.E.Str → (Pz × S1st) × F.E.Str → W → W)
    (fa : Pz → S1st × F.E.Str → ((kBatFoldRide L).src cK10).X × ((kBatFoldRide L).src cK10).E.Str)
    (Nu : Numbers) (Mg : Meaning Pz W) (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (X : (Pz × S1st) × F.E.Str → Prop)
    (hins : ∀ i, insQ links ps k i →
      (∃ c, i = Item.row m c) ∨ (∃ t, i = Item.pin m t) ∨ i = Item.unmarked)
    (hU : ∀ a, X a → a.1.2.failed = none)
    (hRow : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ c, insQ links ps k (Item.row m c) →
          Mg.row m c (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w))
    (hPin : ∀ z a a', X ((z, a.1), a.2) →
      K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        ∀ t, insQ links ps k (Item.pin m t) → ∀ s ∈ Nu.sent m t,
          Mg.pin s.1 s.2 (z, a.1) (strsOf F a.2) (e ((z, a.1), a.2) ((z, a'.1), a'.2) w)) :
    ∀ z a τ a', K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base dB dE dR (Yc cK10).k
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc cK10).k dR)))).ior.red.out a τ = some a' →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, relAt (meansQ (Fr := F) Nu Mg fun a => a) (outsQ links ps k) ((z, a'.1), a'.2) w →
        (fun (a : (Pz × S1st) × F.E.Str) (w : W) =>
          X a → relAt (meansQ (Fr := F) Nu Mg fun a => a) (insQ links ps k) a w) ((z, a.1), a.2)
          (((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).withMap e).ext
            ((z, a.1), a.2) τ w) := by
  intro z a τ a' hon hout hend w hw hX i hi
  rw [maker_ext_of_on b base dB dE dR (Yc cK10).k x _ _ e z a a' τ hout w]
  rcases hins i hi with ⟨c, rfl⟩ | ⟨t, rfl⟩ | rfl
  · exact hRow z a a' hX hon hend w hw c hi
  · exact hPin z a a' hX hon hend w hw t hi
  · exact hU _ hX

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.goodIn_beside
#print axioms VerifiableInference.Desc.First.Close.k10_hQ_beside
