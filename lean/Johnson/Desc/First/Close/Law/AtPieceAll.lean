-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AtPieceAll.lean: THE LAW OF K10 AT A PIECE, WITH ITS ERRORS PAID AT
PRICED PLACES AND ITS PREMISE `OrderedV` PAID FROM THE ROWS' TIE. A definition, statements and
proofs.

`k10_piece_priced` (AtPiecePriced.lean, beside this file) is general in the typed rows of the claim,
in the batching's coefficients and in the further weights, and asks `OrderedV` of them. Here they
are chosen as in OrderedOf.lean, OrderedNum.lean and OrderedAll.lean, and `orderedV_all` pays the
premise.
  `RowsTied R n num N pS x σ T L rows`: what `orderedV_all` asks of the rows, name by name, as one
    proposition: the list has n rows; a row b of the claim has the reading of the target of the
    program's row number num b as its target and `rowVec` of that row as its state; of a member's
    sample row: the answer, pS at the seed, `NamesOne` and `SampleFits`.
  `frOf_free`: the chosen further weights are 0 off the free rows.
  `k10_piece_all`: `k10_piece_priced` at: a typed row's state := a vector on the whole cube; its
    form := pull of it; the coefficients := the powers of one element along the numbering num
    (`Cb.Pv.Bat.powersZ n num`); the further weights := `frOf pull (frSOf pS)`; both readings of an
    element := the element read (`oneOf id`). GONE from the premises: `OrderedV`; the evader's law
    (`powersZ_ok`); "the further weights are 0 off the free rows"; the two on the readings of an
    element. IN THEIR PLACE: `Pulls R pull` and, at every statement with `on`, `RowsTied` at the
    group's layout and `runRows`.
Limits. `Pulls` (PullsOf.lean pays it from two conditions) and `RowsTied` are premises: shown of no
data here. One pS and one numbering must serve all statements with `on`. For the claim's rows there
is one text, not two held against each other. Those of the files named; through FoldPriced.lean it
rests on the files under ThirdParty/ (lean/LIMITS.md, L15). Called at no value. Nothing on an honest
prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtPiecePriced
import Johnson.Desc.First.Close.Law.OrderedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

section Tied
variable {S : Sig GE} (R : RowsK S) {B : Type} (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE)

/-- **What `orderedV_all` asks of the rows, name by name**, as one proposition. -/
def RowsTied (n : ℕ) (num : R.G.Row B ≃ Fin n) (N : SlotNames R)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (x : (B → GE) × (B → R.Sh.Cin.J → GE)) (σ : S.Smp) (T : Statement) (L : GroupLayout)
    (rows : List OnBytes.Row) : Prop :=
  ∃ hn : rows.length = n,
    (∀ b, x.1 b = readE (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)).target ∧
      x.2 b = rowVec N T L (rows[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt))) ∧
    ∀ as, (σ as.1.1).2 as.2 =
        readE (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)).target ∧
      pS as (σ as.1.1).1 = rowVec N T L (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) ∧
      ∃ o, NamesOne (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) o ∧
        SampleFits N T L (rows[(num (.inr as)).val]'(hn ▸ (num (.inr as)).isLt)) o as.1
          (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
            ((S.om as.1.1).row as.2) (σ as.1.1).1)

open Classical in
/-- The further weights of OrderedOf.lean and OrderedAll.lean are 0 off the free rows. -/
theorem frOf_free
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (ν : R.G.Row B) (s : R.G.RowSt (fun _ : B => R.Sh.Cin.J → GE) ν) (j : R.Sh.Cin.J)
    (hj : ¬ FreeAt R.Sh j) : frOf R pull (frSOf R pS) ν s j = 0 := by
  cases ν with
  | inl b =>
    show (if FreeAt R.Sh j then _ else 0) = (0 : GE)
    rw [if_neg hj]
  | inr as =>
    show (if FreeAt R.Sh j then _ else 0) = (0 : GE)
    rw [if_neg hj]

/-- The chosen states of the claim's typed rows: vectors on the whole cube. -/
abbrev SbV (B : Type) : B → Type := fun _ => R.Sh.Cin.J → GE

/-- The chosen forms: pull of the state. -/
abbrev slV : ∀ b : B, Slf GE (SbV R B b) R.G.C.J := fun _ V => pull V

/-- The chosen coefficients: the powers of one element along a numbering. -/
abbrev ZV (n : ℕ) (num : R.G.Row B ≃ Fin n) : Evader GE (R.G.Row B) :=
  Cb.Pv.Bat.powersZ (E := GE) n num

end Tied

section Caller
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)

variable (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n
      num)).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **THE LAW OF K10 AT A PIECE, WITH ITS ERRORS PAID AT PRICED PLACES AND `OrderedV` PAID FROM THE
ROWS' TIE.** -/
theorem k10_piece_all (L : List (BatFoldCaller GE)) (dB dE dR : RDT)
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
      (fun a a' => ∃ f' S', a'.1 = wr a.1 f' S' ∧ (∃ τ, a'.2 = p.ior.imp a.2 τ) ∧
        ((rd a.1).1 = none ∧ ∃ lk, (rd a.1).2.1.shape.link[(rd a.1).2.1.link]? = some lk ∧
          (rd a.1).2.1.next = .laterOrClose ∧ (rd a.1).2.1.moment = reqMoments lk) ∧
        f' = { (rd a.1).2.1 with
          rows := f'.rows, mask := none, link := (rd a.1).2.1.link + 1, next := .first } ∧
        (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) f'.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rd a.1).2.2.groups[g]? = some G →
              (begun (rd a.1).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rd a.1).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rd a.1).2.2 g G) lay (runRows (rd a.1).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rd a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) p.ds)) := by
  refine k10_piece_priced R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L dB dE dR
      id id (fun _ => rfl) ρ hρ
    hst hfx (Cb.Pv.Bat.powersZ_ok n num num.injective) hFi hg hj hc he hv
    (frOf R pull (frSOf R pS)) (frOf_free R pull pS) P g mask es p hb hds rd wr hdec fa on hon
    (fun _ _ h => h) sB sE sR x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB ?_ hM hR hk hh hZ
  intro a ha τ _ _ G e z lay hG hd gz hl
  obtain ⟨hn, hB, hS⟩ := hT a ha G lay hG hl
  have hz : z = readE e := by
    rw [drawnOf_one hd, hρ] at gz
    exact (Option.some.inj gz).symm
  rw [hz]
  exact orderedV_all R pull n num N hP pS _ _ e _ lay _ hn hB hS

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.frOf_free
#print axioms VerifiableInference.Desc.First.Close.k10_piece_all
