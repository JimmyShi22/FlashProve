-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtAny.lean: THE LAW OF K10 AT ANY BLOCK ON THE FIRST CHAIN's RECORD
WHOSE YES IS `closeFrame`'s YES. A definition, statements and proofs.

`k10_block` and `k10_block_self` (AtBlock.lean, AtBlockSelf.lean, beside this file) speak of the
piece of `K9.closing Pr`. A description does not seat that block bare: its seat lays wrappers around
it (another name and place; a guard on the mark; a guard on the reply; the claims' type). The law
spends of the block ONE thing: where it says yes, `closeFrame` said yes on what `recOf` reads, at
the place's entries, and what is returned is `putRec` of "nothing owed", the frame and the
statement. So here the block is a letter b with that one premise H.
  `pieceOn b base dB dE dR k ext err`: the piece with the block `below b` and these rounds' data.
  `k10_any`: `k10_piece_fmt` (RoundsPay.lean) at that piece: `k10_block` with b and H in `K9.closing
    Pr`'s place. `k10_any_self`: the same with the group, the mask and the plan read off the record
    (the promise `K10OnS`): `k10_block_self`'s like.
What is left of `k10_any_self`, by the binders' names: L · dB dE dR · ρ · hρ · hst · hfx · hFi · hg
· hj · hc · he · hv · hP · pS · Cl W · F · Pr · b · H · base · ext · err · fa · x · hx · hxs · hxe ·
hxC · hxZ · na nb · iE · iR · y · hy · hys · hye · hyz · iB.
Limits. Those of AtBlock.lean and AtBlockSelf.lean. H is a premise: who pays it for a seated block
is that seat's law. The block's declared rounds are not read: dB, dE, dR and their number are
letters. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtBlockSelf

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

/-- The piece of a block on the first chain's record, UNDER `below`, with these rounds' data. -/
def pieceOn {Cl W : Type} {F : Frame} (b : Block VerifiableInference.Desc.First.S Cl) (base : ℕ)
    (dB dE dR : RDT) (k : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str →
      Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR))) :
    Piece (ckP .two) F VerifiableInference.Desc.First.S Cl W :=
  { b := below b, base := base, ds := dB :: dE :: List.replicate k dR, ext := ext, err := err }

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_any
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
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
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
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (hk : P.k = R.s.h + R.s.g)
    (hh : P.h = R.s.h) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10On R N keep pull n num fx A₀ bC bZ w₀ w₁
      L pS P g mask (entries Pr) rdK fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base
      dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext
      err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage
      a.2 τ = true ∧ closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP
      .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull)
      (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK
      a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK
      a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK
      a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[g]? = some G → (begun (rdK a.1).2.2 g G).layout g = some lay → ∀ (r :
        R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N
        (begun (rdK a.1).2.2 g G) lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg
        m, r)).1 j = readE (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) :=
  k10_piece_fmt R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
    pS P g mask (entries Pr) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV
    R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err) rfl rfl rdK wrK (fun s rs gs s' _
    h => H s rs gs s' (below_yes _ _ _ _ _ h)) rdBK (fun s f S' => Prod.ext (recOf_putRec s ⟨none,
    f, S'⟩).1 (recOf_putRec s ⟨none, f, S'⟩).2) fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB hk
    hh

theorem k10_any_self
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
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
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
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10OnS R N keep pull n num fx A₀ bC bZ w₀
      w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE dR (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp
      a.2 τ ∧ sTests (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx
      A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK
      a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK
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
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) :=
  fun a ha =>
    k10_any R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP pS
      (planOf (entries Pr) (rdK a.1)) (rdK a.1).2.1.group (rdK a.1).2.1.mask Pr b H base ext err fa
      x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB ha.1 ha.2.1 a ha.2.2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_any
#print axioms VerifiableInference.Desc.First.Close.k10_any_self
