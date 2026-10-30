-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtBlock.lean: THE LAW OF K10 AT K10's OWN BLOCK, LIFTED TO THE FIRST
CHAIN's RECORD. Definitions, a statement and its proof.

`k10_piece_fmt` (RoundsPay.lean, beside this file) is a law of any piece p that meets eight
premises: nothing is put behind its rounds; its rounds' data are dB, dE and k times dR; its block
decides by `closeFrame`, read by rd and written by wr; what rdB reads off what wr wrote is what was
written. In the driver a segment's closing is three
blocks (`closeKinds` := K9, K10, K9: Johnson/Desc/First/Driver/Chain.lean:117), and K9's files,
which lay them, lay as the middle one `K9.closing P` := K10's own block (`kind P`,
Johnson/Desc/First/Close/Kind.lean) lifted to the record S by `recOf` and `putRec`
(Johnson/Desc/First/Batch/Place.lean:47, :70). Here the law is laid at the piece of that block.
  `rdK`, `wrK`, `rdBK`: the reading and the writing: what is owed, the frame and the statement of
    `recOf s` (`recOf` hands on "some 0" as "none": so "nothing owed" says that nothing waits, not
    that the field is none); `putRec s` of "nothing owed", a frame and a statement; the frame and
    the statement of `recOf s`.
  `pieceAt_closing`: the piece's block IS `below (K9.closing Pr)`: by make. (What a rule above the
    pieces asks of their blocks is "the chain's blocks under `below`": this is the hook for "K10's
    block sits in the chain".)
  `k10_block`: `k10_piece_fmt` at p := `pieceAt Pr recOf putRec base dB dE dR k ext err`
    (PieceOf.lean), k the number of the caller's fold rounds, at the entries of the place Pr: THE
    EIGHT PREMISES ON THE PIECE ARE GONE: by `pieceAt_dec` and `recOf_putRec` (LensAt.lean); the
    first two by make.
What is left, by the binders' names: L · dB dE dR · ρ · hρ · hst · hfx · hFi · hg · hj · hc · he ·
hv · hP · pS · P · g · mask · Cl W · F · Pr · base · ext · err · fa · x · hx · hxs · hxe · hxC · hxZ
· na nb · iE · iR · y · hy · hys · hye · hyz · iB · hk · hh.
Limits. Those of RoundsPay.lean and OnK10.lean. THAT THE BASE's CHAIN HOLDS THIS PIECE'S BLOCK AT
ITS CLOSINGS IS NOT SHOWN: `pieceAt`'s block is `below` of the kind's block, lifted; what the driver
lays is the driver's. k is the caller's number of fold rounds: that the place's own number Pr.k is
that number is not asked and not shown: where they part, the block's declared rounds are not the
piece's data. dB, dE, dR, base, ext and err are letters. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.RoundsPay
import Johnson.Desc.First.Close.Law.PieceOf
import Johnson.Desc.First.Close.Law.LensAt

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

/-- What K10's block reads off the record. -/
def rdK (s : VerifiableInference.Desc.First.S) : Option Nat × ReqFrame × Statement :=
  ((recOf s).owed, (recOf s).frame, (recOf s).st)

/-- What it writes. -/
def wrK (s : VerifiableInference.Desc.First.S) (f : ReqFrame) (S' : Statement) :
    VerifiableInference.Desc.First.S := putRec s ⟨none, f, S'⟩

/-- The frame and the statement that stand in the record. -/
def rdBK (s : VerifiableInference.Desc.First.S) : ReqFrame × Statement := ((recOf s).frame, (recOf
    s).st)

/-- **The piece's block is `below` of the very block that K9's files lay as the middle one of a
segment's closing.** -/
theorem pieceAt_closing {Cl W : Type} {F : Frame} (Pr : Par) (base : ℕ) (dB dE dR : RDT) (k : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str →
      Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR))) :
    (pieceAt (Cl := Cl) Pr recOf putRec base dB dE dR k ext err).b =
      below (VerifiableInference.Desc.K9.closing Pr) := rfl

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

theorem k10_block
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
    (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10On R N keep
      pull n num fx A₀ bC bZ w₀ w₁ L pS P g mask (entries Pr) rdK fa) (fun a a' => (∃ τ, a'.2 =
      (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP
      .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceAt
      (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc (R.foldCaller keep (SbV R B)
      (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) =
      .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk,
      (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧
      (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[g]? = some G → (begun (rdK a.1).2.2 g G).layout g = some lay → ∀ (r :
        R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N
        (begun (rdK a.1).2.2 g G) lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg
        m, r)).1 j = readE (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE
          dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext
              err).ds)) :=
  k10_piece_fmt R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
    pS P g mask (entries Pr) (pieceAt (Cl := Cl) (W := W) (F := F) Pr recOf putRec base dB dE dR (Yc
    (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err) rfl rfl
    rdK wrK (fun s rs gs s' _ h => pieceAt_dec Pr recOf putRec base dB dE dR _ ext err s rs gs s' h)
    rdBK (fun s f S' => Prod.ext (recOf_putRec s ⟨none, f, S'⟩).1 (recOf_putRec s ⟨none, f, S'⟩).2)
    fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB hk hh

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.pieceAt_closing
#print axioms VerifiableInference.Desc.First.Close.k10_block
