-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtPiece.lean: THE LAW OF K10 AT A PIECE OF THE DESCRIPTION, OVER THE
REAL ROUNDS, AT THE CAP. Statements and proofs.

A law of `frameRed` (FrameLaw.lean, beside this file) at the real readings (`realRd`,
RealRounds.lean) and at the cap is carried to the reduction of a piece (`Piece`,
Johnson/Desc/Sound/ChainRule.lean) whose block decides by `closeFrame`.
  `frame_to_piece`: let p be a piece with nothing put behind its rounds, whose declared rounds are
    dB, dE and k times dR, and whose block's decision, where it says yes with a record s', is a yes
    of `closeFrame` at what rd reads off the record, with s' made by wr of the frame and the
    statement behind. Then a law of `frameRed ρ es (rd of the record)`, ρ the real readings, with an
    end Q, at the cap, gives `p.ior.red.Leads on Q' (the cap)`, Q' a a' := there are a frame f' and
    a statement S' with: the record behind is wr of them; the oracles behind are those that the
    piece's stage leaves at some written transcript; and Q a (a, f', S'). By `leads_written`
    (RealLeads.lean) and `piece_leads_of_written` (RealPiece.lean).
  `k10_piece`: `k10_rows_asks` (EndToEnd.lean) so carried: `p.ior.red.Leads (on and AtPlace) Q'
    (Err.cap 128 (uLT (ckP .two) p.ds))`: on the statements with `on` that stand at the place the
    prover has lost, at the start, at 2^-128 a round, towards: whatever the piece puts out, the
    record behind is wr of a frame f' and a statement; nothing was owed, the link is there, the
    frame stood at "later or close" at the link's last moment; f' is the frame in front with the
    claim laid into `rows`, no mask, the next link, "first"; and IF what is carried holds of that
    claim THEN every member's word decodes with its sample and every row of `runRows` holds of these
    messages, as `rowVec` on the arranged message.
Premises of `k10_piece`: those of `k10_rows_asks`, with the six readings now `realRd` at "the one
element drawn", read through ιZ and ιC (`oneOf`); of the three premises on readings, `Scal` is paid
from one law on ιC (its value is the element read), "defined at every list of one element" by
`oneOf_some`; `hFit`, at the cap, STAYS A PREMISE: the proved block's own errors fit 2^-128 a round
along the readings (`real_fits_cap`, `real_fits_held` beside this file bring it to counts). The
three on the piece: nothing put behind; the declared rounds; the decision.
Limits. The premises on the piece are shown of no piece of a description here. ρ stands as a letter
with an equation: at the written term Lean's elaborator ran out of time. Those of the files named.
Called at no value. Nothing on an honest prover or on hiding. hdec is asked only of lists of as many
rounds as the piece's stretch has.

-/
import Johnson.Desc.First.Close.Law.EndToEnd
import Johnson.Desc.First.Close.Law.RealPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

theorem frame_to_piece (c : BatFoldCaller GE) (dB dE dR : RDT) (rdZ : List E → Option c.s.Z.D)
    (rdCh : List E → Option (Yc c).Ch) (ρ : Rd c (wT dB) (wT dE) (wT dR))
    (hρ : ρ = realRd c dB dE dR rdZ rdCh) (es : List Fmt.Entry) {Sr Cl W : Type} {F : Frame}
    (p : Piece (ckP .two) F Sr Cl W) (hb : p.back = [])
    (hds : p.ds = dB :: dE :: List.replicate (Yc c).k dR)
    (rd : Sr → Option Nat × ReqFrame × Statement) (wr : Sr → ReqFrame → Statement → Sr)
    (hdec : ∀ s rs gs s', rs.length = p.ds.length → p.b.decide s rs gs = .ok s' →
      ∃ x, closeFrame (rd s).1 (rd s).2.1 (rd s).2.2 es rs = .ok x ∧ s' = wr s x.1 x.2)
    (on : Sr × F.E.Str → Prop)
    (Q : Sr × F.E.Str → (Sr × F.E.Str) × ReqFrame × Statement → Prop)
    (h : (frameRed ρ es fun a : Sr × F.E.Str => rd a.1).Leads on Q
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR)))) :
    p.ior.red.Leads on
      (fun a a' => ∃ f' S', a'.1 = wr a.1 f' S' ∧ (∃ τ, a'.2 = p.ior.imp a.2 τ) ∧
        Q a (a, f', S'))
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  subst hρ
  have h1 := leads_written c dB dE dR rdZ rdCh
    (fun (a : Sr × F.E.Str) rs =>
      match closeFrame (rd a.1).1 (rd a.1).2.1 (rd a.1).2.2 es rs with
      | .ok x => some (a, x.1, x.2)
      | .error _ => none) on Q h
  rw [← hds] at h1
  refine piece_leads_of_written p hb _ on Q _ _ (fun a rs gs s' hl hd => ?_) h1
  obtain ⟨x, hx, rfl⟩ := hdec a.1 rs gs s' hl hd
  refine ⟨(a, x.1, x.2), ?_, fun τ hq => ⟨x.1, x.2, rfl, ⟨τ, rfl⟩, hq⟩⟩
  show (match closeFrame (rd a.1).1 (rd a.1).2.1 (rd a.1).2.2 es rs with
    | .ok x => some (a, x.1, x.2)
    | .error _ => none) = _
  rw [hx]

section Caller
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **THE LAW OF K10 AT A PIECE OF THE DESCRIPTION, OVER THE REAL ROUNDS, AT THE CAP.** -/
theorem k10_piece (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
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
    (hFit : ρ.carS.Fits (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx
      (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) fun _ => bZ)
      (Err.cap 128 (wT dB :: wT dE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k (wT dR))))
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
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  have hS : ρ.Scal := by
    rw [hρ]
    exact realRd_scal_one _ dB dE dR ιZ ιC hval
  have hZ1 : ∀ e, (ρ.rdZ [e]).isSome := by
    rw [hρ]
    exact oneOf_some ιZ
  have hC1 : ∀ e, (ρ.rdCh [e]).isSome := by
    rw [hρ]
    exact oneOf_some ιC
  have h0 := k10_rows_asks R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (wT dB) (wT dE) (wT dR) ρ hS hst hfx
    hZo hFi hg hj hc he hv fr hfr P g mask es (fun a : Sr × F.E.Str => rd a.1) fa on hon _ hFit
    hZ1 hC1 hO hM hR hk hh hZ
  have h1 := frame_to_piece _ dB dE dR (oneOf ιZ) (oneOf ιC) ρ hρ es p hb hds rd wr hdec _ _ h0
  refine h1.conseq (fun _ k => k) fun a _ a' _ _ hq => ?_
  obtain ⟨f', S', q1, q2, -, q3⟩ := hq
  exact ⟨f', S', q1, q2, q3⟩

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.frame_to_piece
#print axioms VerifiableInference.Desc.First.Close.k10_piece
