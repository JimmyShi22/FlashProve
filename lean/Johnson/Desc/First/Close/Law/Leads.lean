-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Leads.lean: THE LAW OF K10 OVER ITS WRITTEN ROUNDS, IN THE PLAIN FORM:
on the statements with `on` the prover has lost, at the start, towards "what is carried behind the
closing gives the joint in front". Definitions, a statement and its proof.

  `closeRed ρ P g mask stOf`: the closing's text as a reduction over the k + 2 written rounds "BAT",
    "FOLD epsilon", k times "FOLD round": at a statement a and a written transcript τ it puts out
    what `closing` (Johnson/Desc/First/Close/Closing.lean) returns at the statement `stOf a` on the
    reading of τ, with a itself; nothing where `closing` refuses. A, the type of statements, is a
    letter.
  `CarriedAt`: what stands behind: `CarryAt` (Carry.lean) of the claim handed on, at the fold, at
    the reading of the point handed on, of the group's word, arranged, and of the fresh mask's word;
    and a witness of the kept messages' own joint at what the batching round carries.
  `batX_snd`: what the batching round carries does not hang on the seed.
  `k10_leads`: `(closeRed ..).Leads on Q ε'` (Johnson/Desc/Plain/Leads.lean), with Q a b := b.1 = a
    ∧ (CarriedAt (of `fa a` and of the claim in b) → the relaxed relation of the typed joint in
    front of the batching has a witness at `fa a`). By `leads_of_know`
    (Johnson/Desc/Plain/Carry.lean) from `tied_and_known`: the proved block is carried to the
    written rounds, not proved again.
  `k10_leads_good`: the same with `BatFoldOKAt`, `Reshape.Fix` and the shape's laws paid from the
    group's data (`RowsK.Good`, `InJ`, `CountsAt`, `Evader.OK`, `Grp.Fits`, the radius below the
    distance, each member's change of shape fixed): by `RowsK.foldCaller_ok` and
    `RowsK.rho_fix`.

Premises. Those of `tied_and_known`; of these the ones that read a written transcript (`DefAt`: the
readings of a seed and of a challenge are defined; `OrderedV`) are asked ONLY WHERE `closing` SAYS
YES, at the statements with `on`; that the written counts ε' bear the proved block's own errors
along the readings (`CarryS.Fits`); that `on` gives the condition of the typed joint in front. fa,
which reads a statement as the typed one with its oracles, is a letter, and so are the six readings.
P, g and mask stand in front of all statements: one plan, one group, one mask.
Limits. Those of Carry.lean. The form is `Leads` with "there is a witness" on both sides: right at a
whole border; the table of joints wants it for every world (by a page that is not in this
library): not here. Of what is put out Q says for certain only that the statement in front rides
along (b.1 = a); of the statement behind (b.2.2) nothing: what a next block's `on` wants of it is
owed. `closeRed` is the function `closing`, not the block of the kind under `Block.step`, and
not `closeFrame`, where group and mask come off the frame. In `CarriedAt` the seed z is idle
(`batX_snd`). Called at no value: at `on` := never, or at counts ε' as large as a round's number of
challenges, it is true and empty. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Carry
import Johnson.Desc.Plain.Carry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

/-- The closing's text as a reduction over its written rounds. -/
noncomputable def closeRed {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR)
    (P : Plan) (g : Nat) (mask : Option Nat) {A : Type} (stOf : A → Statement) :
    Reduction A (A × SingleRows × Statement) where
  shape := rB :: rE :: List.replicate (Yc c).k rR
  out a τ := match closing P (stOf a) g mask (ρ.V τ) with
    | .ok x => some (a, x.1, x.2)
    | .error _ => none

theorem closeRed_out {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR) (P : Plan)
    (g : Nat) (mask : Option Nat) {A : Type} (stOf : A → Statement) (a : A)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (b : A × SingleRows × Statement)
    (h : (closeRed ρ P g mask stOf).out a τ = some b) :
    closing P (stOf a) g mask (ρ.V τ) = .ok (b.2.1, b.2.2) ∧ b.1 = a := by
  unfold closeRed at h
  dsimp only at h
  split at h
  · next x hx =>
    obtain rfl := Option.some.inj h
    exact ⟨hx, rfl⟩
  · cases h

/-- What the batching round carries does not hang on the seed. -/
theorem batX_snd (c : BatFoldCaller GE)
    (a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp) (z z' : c.s.Z.D) :
    (batX c a z).2 = (batX c a z').2 := rfl

section Caller
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **What stands behind the closing**, of the typed statement with its oracles in front (x) and the
claim that the closing hands on. -/
def CarriedAt (L : List (BatFoldCaller GE))
    (x : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (out : SingleRows) : Prop :=
  CarryAt R N out (foldedAt (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁))
      (readP (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k out.gamma)
      (R.Sh.rho.map.map ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map x.2.1).1) x.2.2) ∧
    ∃ (z : Z.D) (v : (S.sub (R.sizeB keep Sb sl Z).kp).Wit × Wp),
      ((S.sub (R.sizeB keep Sb sl Z).kp).over A₀).relR
        ((batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) x.1 z).2,
          ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map x.2.1).2) v

/-- **THE LAW OF K10 OVER ITS WRITTEN ROUNDS.** -/
theorem k10_leads (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hOK : BatFoldOKAt (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁))
    (hFix : R.Sh.rho.Fix R.G.e) (hL : R.Sh.rho.Laws)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (P : Plan) (g : Nat) (mask : Option Nat) {A : Type} (stOf : A → Statement)
    (fa : A → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : A → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on (fa a))
    (ε' : Err (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (hFit : ρ.carS.Fits (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx
      (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) fun _ => bZ) ε')
    (hD : ∀ a, on a → ∀ τ x, closing P (stOf a) g mask (ρ.V τ) = .ok x → ρ.DefAt (ρ.V τ))
    (hO : ∀ a, on a → ∀ (τ : Tr (rB :: rE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR)) x,
      closing P (stOf a) g mask (ρ.V τ) = .ok x → ∀ G e z lay,
      (stOf a).groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun (stOf a) g G).layout g = some lay →
      OrderedV R Sb sl Z N fr (fa a).1.1.1 (fa a).1.2 z e (begun (stOf a) g G) lay
        (runRows (stOf a) G).toList)
    (hM : ∀ a, on a → ∀ G lay, (stOf a).groups[g]? = some G →
      (begun (stOf a) g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (stOf a) G).toList, MaskFits (begun (stOf a) g G) lay w)
    (hR : ∀ a, on a → ∀ G, (stOf a).groups[g]? = some G →
      ∀ w ∈ (runRows (stOf a) G).toList, RowFits (begun (stOf a) g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((stOf a).codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    (closeRed ρ P g mask stOf).Leads on
      (fun a b => b.1 = a ∧ (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1 →
        ∃ w, ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).relR (fa a) w))
      ε' := by
  obtain ⟨hK, hT⟩ := tied_and_known R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ hS hst hfx hOK
    hFix hL fr hfr _ rfl
  refine leads_of_know (closeRed ρ P g mask stOf)
    (Tower.batFoldRide (R.sizeB keep Sb sl Z) R.Sh fx St₀ E₀).red (fun _ => ρ.carS) _ ε'
    (fun _ => hFit) fa on _ _ _ _ _ hon ?_ hK
  intro a τ b ha hb
  obtain ⟨hc, hb1⟩ := closeRed_out ρ P g mask stOf a τ b hb
  obtain ⟨z, τ', a', -, h2, h3, h5, h6, h7, h8⟩ := hT P (stOf a) b.2.2 g mask b.2.1 (fa a) τ
    (hD a ha τ _ hc) hc (hO a ha τ _ hc) (hM a ha) (hR a ha) hk hh (hZ a ha)
  refine ⟨τ', a', h2, h3, fun himp => ⟨hb1, fun hcar => himp (h8.2 ?_)⟩⟩
  obtain ⟨k1, z0, v, k2⟩ := hcar
  refine ⟨by rw [h6]; exact k1, v, ?_⟩
  rw [h5, h7]
  exact k2

/-- **The same, with the proved block's conditions paid from the group's data**: `RowsK.Good`, the
Johnson radius (`InJ`), the counts (`CountsAt`), the evader's law, "the joint radius implies each
member's own", the radius below the stage's distance, and each member's change of shape fixed. -/
theorem k10_leads_good (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hZo : Z.OK) (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (P : Plan) (g : Nat) (mask : Option Nat) {A : Type} (stOf : A → Statement)
    (fa : A → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : A → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on (fa a))
    (ε' : Err (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (hFit : ρ.carS.Fits (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx
      (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) fun _ => bZ) ε')
    (hD : ∀ a, on a → ∀ τ x, closing P (stOf a) g mask (ρ.V τ) = .ok x → ρ.DefAt (ρ.V τ))
    (hO : ∀ a, on a → ∀ (τ : Tr (rB :: rE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR)) x,
      closing P (stOf a) g mask (ρ.V τ) = .ok x → ∀ G e z lay,
      (stOf a).groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun (stOf a) g G).layout g = some lay →
      OrderedV R Sb sl Z N fr (fa a).1.1.1 (fa a).1.2 z e (begun (stOf a) g G) lay
        (runRows (stOf a) G).toList)
    (hM : ∀ a, on a → ∀ G lay, (stOf a).groups[g]? = some G →
      (begun (stOf a) g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (stOf a) G).toList, MaskFits (begun (stOf a) g G) lay w)
    (hR : ∀ a, on a → ∀ G, (stOf a).groups[g]? = some G →
      ∀ w ∈ (runRows (stOf a) G).toList, RowFits (begun (stOf a) g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((stOf a).codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    (closeRed ρ P g mask stOf).Leads on
      (fun a b => b.1 = a ∧ (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1 →
        ∃ w, ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).relR (fa a) w))
      ε' :=
  k10_leads R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ hS hst hfx
    (R.foldCaller_ok keep Sb sl Z fx A₀ bC bZ w₀ w₁ hZo hFi hg hj hc) (R.rho_fix hg he hv)
    (ldGroup_shape_laws GE S R.G R.Sh (R.sh_ok hg)).1 fr hfr P g mask stOf fa on hon ε' hFit hD hO
    hM hR hk hh hZ

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_leads
#print axioms VerifiableInference.Desc.First.Close.k10_leads_good
