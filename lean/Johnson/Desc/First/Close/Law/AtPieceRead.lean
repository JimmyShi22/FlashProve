-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtPieceRead.lean: THE LAW OF K10 AT A PIECE, WITH ITS END SAID OF WHAT
IS READ OFF THE RECORD BEHIND. Statements and proofs.

The end of `k10_piece`, `k10_piece_paid`, `k10_piece_priced` and `k10_piece_all` (beside this file)
reads: THERE ARE a frame f' and a statement S' of which the record behind is wr, and of f' this and
that holds. But wr is a letter with no law; at a wr
that forgets the frame's rows any f' fills the "there are", and the end says nothing: a block that
ran the closing's tests and forgot the claim would have that law. So these four are weaker than
their name at the letter.
  `k10_piece_read`: `k10_piece_all` with a reader rdB of the record behind and ONE PREMISE MORE, a
    law of the lens: hrw: what rdB reads off wr s f S' is the frame f and the statement S'. Its end
    has no "there are": it is said of (rdB a'.1).1, THE FRAME THAT rdB READS OFF THE RECORD BEHIND:
    that frame is the frame in front with its own rows, no mask, the next link, "first"; and if what
    is carried holds of ITS rows, every member's word decodes and every row of `runRows` holds. (rdB
    is a letter of its own, not rd: where the closing stands between other steps of one block, what
    is read in front and what is read behind are two readings. At the closing alone rdB s := (rd
    s).2.)
  `k10_piece_tied`: the same, and in front of its end: THERE ARE ROUNDS ON WHICH `closeFrame`, AT
    WHAT rd READS OFF THE RECORD IN FRONT, SAID YES AND RETURNED JUST THE FRAME AND THE STATEMENT
    THAT rdB READS OFF THE RECORD BEHIND. So whatever a yes of the frame's closing says of the
    statement behind (Lays.lean, Whole.lean's `closing_inv2`: its codes are those in front; the
    fold's test on the batched row holds at it) can be drawn from the end. This holds for certain:
    it costs no error.

  `k10_piece_one`: the strongest form: ONE written transcript τ under one "there is": the stage's
    tests passed at τ; the oracles behind are those that the stage leaves at τ; and `closeFrame`, on
    the rounds that the stage shows of τ (without the sealed digest), returned just the frame and
    the statement that rdB reads off the record behind. (In
    `k10_piece_tied` the rounds and the oracles stand under two separate "there is".)
Limits. fa IS A LETTER, AND NO PREMISE TIES ITS ORACLE HALF TO THE PIECE's ORACLES a.2 (the same
kind of gap as at wr): `RowsTied` speaks of the typed targets, states
and samples; the promise in front of typed data alone. So "every member's word" means THE TYPED
WORDS THAT fa LAYS: at an fa that lays fixed code words whatever was committed, all premises can
still be met. The end has its name's meaning only once fa's second half is fixed as the reading of
a.2: owed where the table of joints fixes fa. hrw is a premise here (LensAt.lean has it at K9's
reading and writing of the record). hdec is asked only of lists of as many rounds as the piece's
stretch has (asked of every list it could not be met at a block
that hands the closing a part of its rounds). The rounds under "there are" are not tied to the
oracles behind. Those of AtPieceAll.lean. Called at no value. Nothing on an honest prover or on
hiding.

-/
import Johnson.Desc.First.Close.Law.AtPieceAll

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

/-- **THE LAW OF K10 AT A PIECE, WITH ITS END SAID OF WHAT IS READ OFF THE RECORD BEHIND.** -/
theorem k10_piece_read (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
        dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
        dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
        bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry)
    {Sr Cl W : Type} {F : Frame} (p : Piece (ckP .two) F Sr Cl W) (hb : p.back = [])
    (hds : p.ds = dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement) (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' →
      ∃ x, closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (rdB : Sr → ReqFrame × Statement) (hrw : ∀ s f S', rdB (wr s f S') = (f, S'))
    (fa : Sr × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
        num) fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).E.Str)
    (on : Sr × F.E.Str → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
          R.Sh.par.Cw.nat).on (fa a))
    {nB aB nE aE nR aR : ℕ} (sB : SendsDraws (toRD dB) nB 1 0 aB)
    (sE : SendsDraws (toRD dE) nE 1 0 aE) (sR : SendsDraws (toRD dR) nR 1 0 aR)
    (x : Johnson.Bridge.FoldedPlace) (hx : x.Paid) (hxs : x.s = R.s) (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC) (hxZ : bZ ≤ x.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (hT : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay →
      RowsTied R n num N pS (fa a).1.1.1 (fa a).1.2 (begun (rd a.1).2.2 g G) lay
        (runRows (rd a.1).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rd a.1).2.2 G).toList, MaskFits (begun (rd a.1).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rd a.1).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rd a.1).2.2 G).toList, RowFits (begun (rd a.1).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rd a.1).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    p.ior.red.Leads (fun a => on a ∧ AtPlace P g mask es (rd a.1))
      (fun a a' => a'.1 = wr a.1 (rdB a'.1).1 (rdB a'.1).2 ∧ (∃ τ, a'.2 = p.ior.imp a.2 τ) ∧
        ((rd a.1).1 = none ∧ ∃ lk, (rd a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧
          (rd a.1).2.1.next = .laterOrClose ∧ (rd a.1).2.1.moment = reqMoments lk) ∧
        (rdB a'.1).1 = { (rd a.1).2.1 with
          rows := (rdB a'.1).1.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first }
              ∧
        (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a)
            (rdB a'.1).1.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
              (begun (rd a.1).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rd a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  refine (k10_piece_all R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc
      he hv hP pS P g mask es p hb hds rd wr hdec fa on hon sB sE sR x hx hxs hxe hxC hxZ iE iR y hy
          hys hye hyz iB hT hM hR hk hh hZ).conseq
    (fun _ k => k) fun a _ a' _ _ hq => ?_
  obtain ⟨f', S', q1, q2, q3, q4, q5⟩ := hq
  have e : rdB a'.1 = (f', S') := by
    rw [q1]
    exact hrw _ _ _
  have e1 : (rdB a'.1).1 = f' := congrArg Prod.fst e
  have e2 : (rdB a'.1).2 = S' := congrArg Prod.snd e
  rw [e1, e2]
  exact ⟨q1, q2, q3, q4, q5⟩

/-- **THE SAME, WITH THE FRAME AND THE STATEMENT BEHIND TIED TO A YES OF THE FRAME's CLOSING.** -/
theorem k10_piece_tied (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
        dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
        dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
        bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry)
    {Sr Cl W : Type} {F : Frame} (p : Piece (ckP .two) F Sr Cl W) (hb : p.back = [])
    (hds : p.ds = dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement) (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' →
      ∃ x, closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (rdB : Sr → ReqFrame × Statement) (hrw : ∀ s f S', rdB (wr s f S') = (f, S'))
    (fa : Sr × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
        num) fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).E.Str)
    (on : Sr × F.E.Str → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
          R.Sh.par.Cw.nat).on (fa a))
    {nB aB nE aE nR aR : ℕ} (sB : SendsDraws (toRD dB) nB 1 0 aB)
    (sE : SendsDraws (toRD dE) nE 1 0 aE) (sR : SendsDraws (toRD dR) nR 1 0 aR)
    (x : Johnson.Bridge.FoldedPlace) (hx : x.Paid) (hxs : x.s = R.s) (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC) (hxZ : bZ ≤ x.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (hT : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay →
      RowsTied R n num N pS (fa a).1.1.1 (fa a).1.2 (begun (rd a.1).2.2 g G) lay
        (runRows (rd a.1).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rd a.1).2.2 G).toList, MaskFits (begun (rd a.1).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rd a.1).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rd a.1).2.2 G).toList, RowFits (begun (rd a.1).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rd a.1).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    p.ior.red.Leads (fun a => on a ∧ AtPlace P g mask es (rd a.1))
      (fun a a' => (∃ rs, closeFrame (rd a.1).1 (rd a.1).2.1 (rd a.1).2.2 es rs = .ok (rdB a'.1)) ∧
        a'.1 = wr a.1 (rdB a'.1).1 (rdB a'.1).2 ∧ (∃ τ, a'.2 = p.ior.imp a.2 τ) ∧
        ((rd a.1).1 = none ∧ ∃ lk, (rd a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧
          (rd a.1).2.1.next = .laterOrClose ∧ (rd a.1).2.1.moment = reqMoments lk) ∧
        (rdB a'.1).1 = { (rd a.1).2.1 with
          rows := (rdB a'.1).1.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first }
              ∧
        (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a)
            (rdB a'.1).1.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
              (begun (rd a.1).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rd a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  refine (k10_piece_read R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc
      he hv hP pS P g mask es p hb hds rd wr hdec rdB hrw fa on hon sB sE sR x hx hxs hxe hxC hxZ iE
          iR
          y hy hys hye hyz iB hT hM hR hk hh hZ).conseq
    (fun _ k => k) fun a τ a' _ hout hq => ⟨?_, hq⟩
  obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := p.out_decide a a' τ hout
  have hl := shown_len p hb a.2 τ
  obtain ⟨x, hx, hs⟩ := hdec a.1 _ gs a'.1 hl hd
  have e : rdB a'.1 = x := by
    rw [hs]
    exact hrw _ _ _
  exact ⟨_, e ▸ hx⟩

/-- **THE SAME, WITH THE ORACLES BEHIND, THE FRAME AND THE STATEMENT BEHIND TIED TO ONE
    TRANSCRIPT.** -/
theorem k10_piece_one (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
        dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
        dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
        bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry)
    {Sr Cl W : Type} {F : Frame} (p : Piece (ckP .two) F Sr Cl W) (hb : p.back = [])
    (hds : p.ds = dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement) (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' →
      ∃ x, closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (rdB : Sr → ReqFrame × Statement) (hrw : ∀ s f S', rdB (wr s f S') = (f, S'))
    (fa : Sr × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
        num) fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
          w₁)).E.Str)
    (on : Sr × F.E.Str → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
          R.Sh.par.Cw.nat).on (fa a))
    {nB aB nE aE nR aR : ℕ} (sB : SendsDraws (toRD dB) nB 1 0 aB)
    (sE : SendsDraws (toRD dE) nE 1 0 aE) (sR : SendsDraws (toRD dR) nR 1 0 aR)
    (x : Johnson.Bridge.FoldedPlace) (hx : x.Paid) (hxs : x.s = R.s) (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC) (hxZ : bZ ≤ x.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (hT : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay →
      RowsTied R n num N pS (fa a).1.1.1 (fa a).1.2 (begun (rd a.1).2.2 g G) lay
        (runRows (rd a.1).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
      (begun (rd a.1).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rd a.1).2.2 G).toList, MaskFits (begun (rd a.1).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rd a.1).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rd a.1).2.2 G).toList, RowFits (begun (rd a.1).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rd a.1).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    p.ior.red.Leads (fun a => on a ∧ AtPlace P g mask es (rd a.1))
      (fun a a' => (∃ τ, a'.2 = p.ior.imp a.2 τ ∧ sTests (ckP .two) p.stage a.2 τ = true ∧
          closeFrame (rd a.1).1 (rd a.1).2.1 (rd a.1).2.2 es
            ((sView (ckP .two) p.stage a.2 τ).rounds.map noDigest) = .ok (rdB a'.1)) ∧
        a'.1 = wr a.1 (rdB a'.1).1 (rdB a'.1).2 ∧
        ((rd a.1).1 = none ∧ ∃ lk, (rd a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧
          (rd a.1).2.1.next = .laterOrClose ∧ (rd a.1).2.1.moment = reqMoments lk) ∧
        (rdB a'.1).1 = { (rd a.1).2.1 with
          rows := (rdB a'.1).1.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first }
              ∧
        (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a)
            (rdB a'.1).1.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
              (begun (rd a.1).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rd a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  refine (k10_piece_read R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc
      he hv hP pS P g mask es p hb hds rd wr hdec rdB hrw fa on hon sB sE sR x hx hxs hxe hxC hxZ iE
          iR
          y hy hys hye hyz iB hT hM hR hk hh hZ).conseq
    (fun _ k => k) fun a τ a' _ hout hq => ⟨⟨τ, ?_⟩, hq.1, hq.2.2⟩
  obtain ⟨ht, -, ⟨gs, hd⟩, hi⟩ := p.out_decide a a' τ hout
  have hl := shown_len p hb a.2 τ
  rw [hb, List.append_nil] at hd hl
  obtain ⟨x, hx, hs⟩ := hdec a.1 _ gs a'.1 hl hd
  have e : rdB a'.1 = x := by
    rw [hs]
    exact hrw _ _ _
  exact ⟨hi, ht, e ▸ hx⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_piece_read
#print axioms VerifiableInference.Desc.First.Close.k10_piece_tied
#print axioms VerifiableInference.Desc.First.Close.k10_piece_one
