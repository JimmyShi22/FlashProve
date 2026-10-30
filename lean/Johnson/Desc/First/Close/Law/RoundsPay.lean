-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RoundsPay.lean: K10's LAW AT A PIECE, WITH ONE PREMISE A WRITTEN ROUND.
A statement and its proof.

`k10_piece_on` (OnK10.lean, beside this file) asks two things of each of the three written rounds:
that it is the format's own (iB, iE, iR: `IsRd`) and what it sends and draws (sB, sE, sR:
`SendsDraws`). The second follows from the first: `rBatN_sd`, `rEps_sd`, `rTwo_sd`
(OnBytes/Slice/RoundsOf.lean).
  `k10_piece_fmt`: `k10_piece_on` without sB, sE, sR and their six numbers.
Limits. Those of OnK10.lean. `IsRd` is an equation of whole entries: at K10's own entries
(Close/Kind.lean) it forces work 0 at all three rounds and the entry's number of rows to be the
place's. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.OnK10
import OnBytes.Slice.RoundsOf

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
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_piece_fmt
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
      dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
      dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx (rd2
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
      bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits)
    (hg : R.Good)
    (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (P : Plan)
    (g : Nat)
    (mask : Option Nat)
    (es : List Fmt.Entry)
    {Sr Cl W : Type}
    {F : Frame}
    (p : Piece (ckP .two) F Sr Cl W)
    (hb : p.back = [])
    (hds : p.ds = dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement)
    (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' → ∃ x, closeFrame
      (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (rdB : Sr → ReqFrame × Statement)
    (hrw : ∀ s f S', rdB (wr s f S') = (f, S'))
    (fa : Sr × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull)
      (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (x : Johnson.Bridge.FoldedPlace)
    (hx : x.Paid)
    (hxs : x.s = R.s)
    (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC)
    (hxZ : bZ ≤ x.bZ)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace)
    (hy : y.Paid)
    (hys : y.s = R.s)
    (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1)
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (hk : P.k = R.s.h + R.s.g)
    (hh : P.h = R.s.h) :
    p.ior.red.Leads (K10On R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS P g mask es rd fa) (fun a a'
      => (∃ τ, a'.2 = p.ior.imp a.2 τ ∧ sTests (ckP .two) p.stage a.2 τ = true ∧ closeFrame (rd
      a.1).1 (rd a.1).2.1 (rd a.1).2.2 es ((sView (ckP .two) p.stage a.2 τ).rounds.map noDigest) =
      .ok (rdB a'.1)) ∧ a'.1 = wr a.1 (rdB a'.1).1 (rdB a'.1).2 ∧ ((rd a.1).1 = none ∧ ∃ lk, (rd
      a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧ (rd a.1).2.1.next = .laterOrClose ∧ (rd
      a.1).2.1.moment = reqMoments lk) ∧ (rdB a'.1).1 = {
          (rd a.1).2.1 with
          rows := (rdB a'.1).1.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdB
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rd
        a.1).2.2.groups[g]? = some G → (begun (rd a.1).2.2 g G).layout g = some lay → ∀ (r : R.G.C.Q
        → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rd
        a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j =
        readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) :=
  k10_piece_on R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
    pS P g mask es p hb hds rd wr hdec rdB hrw fa (rBatN_sd iB) (rEps_sd iE) (rTwo_sd iR) x hx hxs
    hxe hxC hxZ iE iR y hy hys hye hyz iB hk hh

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_piece_fmt
