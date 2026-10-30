-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KindK10Law.lean (kind K10): THE FIELD "law" OF `K10CondAt`
(KindK10.lean, beside this file) FROM K10's LAW, AT THE PICK, AT THE MAKER's PIECE: WHAT IS LEFT OF
IT IS ONE NAMED SENTENCE hQ, WHICH NAMES NO `GoodIn`. Statements and proofs.

Why. `K10CondAt.law` asks `GoodIn o (fun _ => True) Rin Rout` of the piece: a part of the join's own
conclusion. K10's law is home in that form (`k10_goodIn`, GoodOf.lean), general in the condition
behind and in the two relations, under one premise hQ; `goodIn_at_maker` (GoodAtMaker.lean) carries
it to the maker's piece with the maker's own extractor.
  `k10_law_at_pick`: K10's law's own premises on the typed stage (those of `k10_goodIn`, to the
    letter); x: what the maker's piece holds beside its sub-protocol, with the cap of 128 bits a
    round as its error; fa z: what is laid in front of the proved sub-protocol, at each public part
    z; Rin, Rout: two relations on the pair; hQ: at every z, a, transcript and a': `K10OnS` at a,
    the piece's out, the law's end `K10EndS`: every witness of Rout behind gives, by x.ext at this
    transcript, a witness of Rin in front. THEN `GoodIn (K10OnS .. read at the pair) (fun _ => True)
    Rin Rout` at `pieceOf (held b) ..`.
  `k10_law_withMap`: the same at that piece with any map e as its extractor (`Piece.withMap`): the
    form in which the join has the piece.
Limits. hQ IS SHOWN NOWHERE: it is the whole tie of K10's law to a witness: that what the table's
extractor lays at K10's number are the messages of which the law's end speaks. The premises on the
typed stage are premises here (ConditionReal.lean pays what it pays of them at the written numbers).
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.KindK10
import Johnson.Desc.First.Close.Law.GoodOf

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

/-- **K10's LAW AT THE PICK, AT THE MAKER's PIECE.** -/
theorem k10_law_at_pick {Pz : Type} (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd cK10 (wT dB) (wT dE) (wT dR)) (hρ : ρ = realRd cK10 dB dE dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc cK10).val (Yc cK10).n fx (rd2 cK10))
    (hfx : fx.2 * (HVar.plain GE (Yc cK10).n).mon fx.1 = 1) (hFi : R.G.Fits) (hg : R.Good)
    (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ) (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e) (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1st Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1st) W (dB :: dE :: List.replicate (Yc cK10).k dR))
    (hcap : x.err = Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
    (fa : Pz → S1st × F.E.Str → ((kBatFoldRide L).src cK10).X × ((kBatFoldRide L).src cK10).E.Str)
    (xp : Johnson.Bridge.FoldedPlace) (hx : xp.Paid) (hxs : xp.s = R.s) (hxe : xp.e = R.e)
    (hxC : bC ≤ xp.bC) (hxZ : bZ ≤ xp.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (Rin Rout : (Pz × S1st) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base dB dE dR (Yc cK10).k
        (fun a τ w => x.ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc cK10).k dR)))).ior.red.out a τ = some a' →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => x.ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2) (x.ext ((z, a.1), a.2) τ w)) :
    (pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).GoodIn
      (fun a => K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  goodIn_at_maker b base dB dE dR (Yc cK10).k x
    (fun z => K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z)) (fun _ _ => True)
    (fun z a w => Rin ((z, a.1), a.2) w) (fun z a w => Rout ((z, a.1), a.2) w) fun z => by
      rw [hcap]
      exact k10_goodIn R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc
        he hv hP pS Pr b H base _ (fa z) xp hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB
        (fun _ => True) _ _ fun a τ a' h1 h2 h3 => ⟨trivial, hQ z a τ a' h1 h2 h3⟩

/-- **The same with any map as the piece's extractor.** -/
theorem k10_law_withMap {Pz : Type} (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd cK10 (wT dB) (wT dE) (wT dR)) (hρ : ρ = realRd cK10 dB dE dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc cK10).val (Yc cK10).n fx (rd2 cK10))
    (hfx : fx.2 * (HVar.plain GE (Yc cK10).n).mon fx.1 = 1) (hFi : R.G.Fits) (hg : R.Good)
    (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ) (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e) (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl W : Type} {F : Frame} (Pr : Par) (b : Block S1st Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (x : Rest (ckP .two) F (Pz × S1st) W (dB :: dE :: List.replicate (Yc cK10).k dR))
    (hcap : x.err = Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR)))
    (e : (Pz × S1st) × F.E.Str → (Pz × S1st) × F.E.Str → W → W)
    (fa : Pz → S1st × F.E.Str → ((kBatFoldRide L).src cK10).X × ((kBatFoldRide L).src cK10).E.Str)
    (xp : Johnson.Bridge.FoldedPlace) (hx : xp.Paid) (hxs : xp.s = R.s) (hxe : xp.e = R.e)
    (hxC : bC ≤ xp.bC) (hxZ : bZ ≤ xp.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (Rin Rout : (Pz × S1st) × F.E.Str → W → Prop)
    (hQ : ∀ z a τ a', K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa z) a →
      (pieceOn (W := W) (F := F) b base dB dE dR (Yc cK10).k
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two)
          (dB :: dE :: List.replicate (Yc cK10).k dR)))).ior.red.out a τ = some a' →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base
        (fun a τ w => ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) []
          x).withMap e).ext ((z, a.1), a.2) τ w)
        (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc cK10).k dR))) (fa z) a a' →
      ∀ w, Rout ((z, a'.1), a'.2) w → Rin ((z, a.1), a.2)
        (((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).withMap e).ext
          ((z, a.1), a.2) τ w)) :
    ((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).withMap e).GoodIn
      (fun a => K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr (fa a.1.1) (a.1.2, a.2))
      (fun _ => True) Rin Rout :=
  k10_law_at_pick R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv
    hP pS Pr b H base
    ⟨((pieceOf (held b) base (dB :: dE :: List.replicate (Yc cK10).k dR) [] x).withMap e).ext,
      x.err⟩
    hcap fa xp hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB Rin Rout hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_law_at_pick
#print axioms VerifiableInference.Desc.First.Close.k10_law_withMap
