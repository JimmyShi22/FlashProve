-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtBlockSelf.lean: THE LAW OF K10 AT K10's OWN BLOCK, WITH THE GROUP,
THE MASK AND THE PLAN READ OFF THE RECORD ITSELF. Definitions, statements and proofs.

`k10_block` (AtBlock.lean, beside this file) has three letters P, g, mask, and its promise asks that
the record stands at them (`AtPlace`). But a law in the form `Leads` speaks of each statement by
itself (Johnson/Desc/Plain/Leads.lean: for every a with the promise ..): so a letter may be a
function of the statement. Here g is the frame's own group, mask the frame's own mask, P the plan
that the closing's text itself makes of the frame: and `AtPlace` holds by make.
  `planOf es x`: the frame's two codes, the k and h of the frame's record of the group at its link,
    the entries es: what `closeFrame` hands `closing`
    (Johnson/Desc/First/Close/Closing.lean:214-218). The place Pr of the block enters by its entries
    alone. `atPlace_self`: `AtPlace` at these three.
  `K10OnS .. a`: the promise: the frame's record of the group has the stage's k and h (two equations
    of numbers, on the record), and `K10On` at the record's own three. `k10OnS_of`: it follows from
    these two and five of `K10On`'s six clauses: the sixth, place, is gone.
  `k10_block_self`: the law with that promise; the end speaks of the frame's own group.
What is left, by the binders' names: L · dB dE dR · ρ · hρ · hst · hfx · hFi · hg · hj · hc · he ·
hv · hP · pS · Cl W · F · Pr · base · ext · err · fa · x · hx · hxs · hxe · hxC · hxZ · na nb · iE ·
iR · y · hy · hys · hye · hyz · iB.
Limits. Those of AtBlock.lean. Nothing is proved that was not: three letters and two premises have
moved into the promise, and one clause of the promise is paid. Where the frame has no record of a
group at its link `planOf` reads the default's numbers; the closing refuses there ("K10.group").
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtBlock

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

/-- The plan that the closing's text makes of the frame. -/
def planOf (es : List Fmt.Entry) (x : Option Nat × ReqFrame × Statement) : Plan :=
  ⟨x.2.1.shape.code, x.2.1.shape.maskCode, (x.2.1.groups[x.2.1.link]?.getD default).k,
    (x.2.1.groups[x.2.1.link]?.getD default).h, es⟩

theorem atPlace_self (es : List Fmt.Entry) (x : Option Nat × ReqFrame × Statement) :
    AtPlace (planOf es x) x.2.1.group x.2.1.mask es x := by
  refine ⟨rfl, rfl, fun G hG => ?_⟩
  simp [planOf, hG]

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **K10's condition in front, at the record's own group, mask and plan.** -/
def K10OnS (L : List (BatFoldCaller GE))
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (Pr : Par) {F : Frame}
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a : VerifiableInference.Desc.First.S × F.E.Str) : Prop :=
  (planOf (entries Pr) (rdK a.1)).k = R.s.h + R.s.g ∧ (planOf (entries Pr) (rdK a.1)).h = R.s.h ∧
    K10On R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS (planOf (entries Pr) (rdK a.1)) (rdK
      a.1).2.1.group (rdK a.1).2.1.mask (entries Pr) rdK fa a

/-- The promise from two equations of numbers and five clauses: `K10On`'s sixth, place, is paid. -/
theorem k10OnS_of (L : List (BatFoldCaller GE))
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (Pr : Par) {F : Frame}
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a : VerifiableInference.Desc.First.S × F.E.Str)
    (hk : (planOf (entries Pr) (rdK a.1)).k = R.s.h + R.s.g)
    (hh : (planOf (entries Pr) (rdK a.1)).h = R.s.h)
    (front : ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
      R.Sh.par.Cw.nat).on (fa a))
    (tied : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay → RowsTied R n num N pS (fa a).1.1.1
      (fa a).1.2 (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay (runRows (rdK a.1).2.2 G).toList)
    (masks : ∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2
      (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧ ∀
      w ∈ (runRows (rdK a.1).2.2 G).toList, MaskFits (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay
      w)
    (rows : ∀ G, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → ∀ w ∈ (runRows (rdK a.1).2.2
      G).toList, RowFits (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) w)
    (code : ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK a.1)).maskCode default).ell =
      R.s.Z.l) :
    K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa a :=
  ⟨hk, hh, ⟨front, tied, masks, rows, code, atPlace_self _ _⟩⟩

theorem k10_block_self
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
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
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
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows)) :
    (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10OnS R N keep
      pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceAt (Cl := Cl) (W :=
      W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R
      n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceAt (Cl := Cl) (W
      := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV
      R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧ closeFrame (rdK a.1).1 (rdK
      a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F)
      Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀
      bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1
      (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK
      a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment =
      reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
        G).layout (rdK a.1).2.1.group = some lay → ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows
        (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
        lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE
        (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE
          dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext
              err).ds)) :=
  fun a ha =>
    k10_block R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP pS
      (planOf (entries Pr) (rdK a.1)) (rdK a.1).2.1.group (rdK a.1).2.1.mask Pr base ext err fa x hx
      hxs hxe hxC hxZ iE iR y hy hys hye hyz iB ha.1 ha.2.1 a ha.2.2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.atPlace_self
#print axioms VerifiableInference.Desc.First.Close.k10OnS_of
#print axioms VerifiableInference.Desc.First.Close.k10_block_self
