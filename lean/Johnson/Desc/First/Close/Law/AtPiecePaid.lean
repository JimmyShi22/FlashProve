-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtPiecePaid.lean: THE LAW OF K10 AT A PIECE, WITH ITS PREMISE ON THE
ERRORS PAID AT A PRICED PLACE. A statement and its proof.

`k10_piece` (AtPiece.lean, beside this file) asks that the cap bears the proved block's own errors
along the real readings (hFit). `real_fits_caller_of_paid` (RealPaid.lean) shows that from
`FoldedPlace.Paid` (Johnson/Bridge/FoldPriced.lean): a stage and a radius whose counts at "FOLD
epsilon" and at every "FOLD round" are at most 2^-128 of the round's written challenges.
  `k10_piece_paid`: `k10_piece` with hFit so paid. In its place stand: a priced place x whose stage
    and radius are the group's; the caller's two counts are at most x's; the written rounds "FOLD
    epsilon" and "FOLD round" are the format's own; `SendsDraws` at the three rounds; the reading of
    a seed is one to one; and ONE count is left: at "BAT" the list bound times the evader's number
    is below 2^-128 of that round's written challenges.
Limits. That the description's K10 stands at a place of the written table
(Johnson/Bridge/FoldAtWritten.lean) is not shown. This file rests, through RealPaid.lean and
FoldPriced.lean, on the files under ThirdParty/ (lean/LIMITS.md, L15). Those of AtPiece.lean and of
the files named. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtPiece
import Johnson.Desc.First.Close.Law.RealPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **THE LAW OF K10 AT A PIECE, WITH ITS ERRORS PAID AT A PRICED PLACE.** -/
theorem k10_piece_paid (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ιZ : GE → Z.D) (ιC : GE → (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).Ch)
    (hval : ∀ x, (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val (ιC x) = x)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) dB dE dR (oneOf ιZ) (oneOf ιC))
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hZo : Z.OK) (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry)
    {Sr Cl W : Type} {F : Frame} (p : Piece (ckP .two) F Sr Cl W) (hb : p.back = [])
    (hds : p.ds = dB :: dE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement) (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' →
      ∃ x, closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (fa : Sr × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : Sr × F.E.Str → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on (fa a))
    (hιZ : Function.Injective ιZ)
    {nB aB nE aE nR aR : ℕ} (sB : SendsDraws (toRD dB) nB 1 0 aB)
    (sE : SendsDraws (toRD dE) nE 1 0 aE) (sR : SendsDraws (toRD dR) nR 1 0 aR)
    (x : Johnson.Bridge.FoldedPlace) (hx : x.Paid) (hxs : x.s = R.s) (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC) (hxZ : bZ ≤ x.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (cB : RoundBelow ((R.sizeB keep Sb sl Z).L * Z.err) (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hO : ∀ a, on a → ∀ (τ : Tr (wT dB :: wT dE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k (wT dR))) x,
      closing P (rd a.1).2.2 g mask (ρ.V τ) = .ok x → ∀ G e z lay,
      (rd a.1).2.2.groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun (rd a.1).2.2 g G).layout g = some lay →
      OrderedV R Sb sl Z N fr (fa a).1.1.1 (fa a).1.2 z e (begun (rd a.1).2.2 g G) lay
        (runRows (rd a.1).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rd a.1).2.2 G).toList, MaskFits (begun (rd a.1).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rd a.1).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rd a.1).2.2 G).toList, RowFits (begun (rd a.1).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rd a.1).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    p.ior.red.Leads (fun a => on a ∧ AtPlace P g mask es (rd a.1))
      (fun a a' => ∃ f' S', a'.1 = wr a.1 f' S' ∧ (∃ τ, a'.2 = p.ior.imp a.2 τ) ∧
        ((rd a.1).1 = none ∧ ∃ lk, (rd a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧
          (rd a.1).2.1.next = .laterOrClose ∧ (rd a.1).2.1.moment = reqMoments lk) ∧
        f' = { (rd a.1).2.1 with
          rows := f'.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first } ∧
        (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) f'.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
              (begun (rd a.1).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rd a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) :=
  k10_piece R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L dB dE dR ιZ ιC hval ρ hρ hst hfx hZo hFi hg hj hc
    he hv fr hfr P g mask es p hb hds rd wr hdec fa on hon
    (hρ ▸ real_fits_caller_of_paid R keep Sb sl Z fx A₀ bC bZ w₀ w₁
      (realReads_of_sends _ dB dE dR ιZ ιC hιZ
        (fun x y h => by rw [← hval x, ← hval y, h]) sB sE sR) x hx hxs hxe hxC hxZ iE iR cB)
    hO hM hR hk hh hZ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_piece_paid
