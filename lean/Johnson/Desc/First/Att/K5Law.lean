-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Law.lean: the law of kind K5, at letters. Where the kind's block
(Att/K5AttentionKind.lean:
attentionKind) says yes, the proved chain of attention's own rounds (Cb/Pv/Att/Own.lean), run on the typed
transcript made of what the block's rounds hold, puts out its run, and its last claim, at which the
chain's knowledge soundness ends, holds exactly if the kind's bill is paid: each row that a sumcheck
leaves is worth 0 in the world, each end value's typed claim holds, and the letters' linear claims
hold.

Main names:
  `RowPrem S D C hh f W m`: f is formOf hh at a summand S0, with (D1), (D2), (D4) at S0.
  `Paid`, `out_iff`: a stage's output claims are: its row is worth 0, and all its end values'
    claims.
  `TailPrem`, `UnitsPrem`; `TailBill`, `UnitsBill`, `tail_bill`, `units_bill`: the chain's debts,
    with
    each sumcheck's output claims so unfolded.
  `k5_last`: the chain's last claim on the run holds exactly if Dn, UnitsBill and TailBill.
  `k5_law`: from decide's yes.
The score at the index owes the letter owF, not its output claims: the bill keeps owF.

Premises: PartHearLaw, PartRowLaw (Part/MaskedSumLaw.lean) · Sized of the ledger that the seat hands
·
each beta reads other than 0 · facts of the letters at a value: their sizes against the plan; the
letters' claims; RowPrem's three equations.
Sources: what Att/K5LeftLaw.lean names, and OnBytes/Tie/Pv/Att/OwnTie.lean (the data's statements,
Claims, Owes, UnitsClaims, UnitsOwed, seenAfter, ownTrs, own_out, own_last); Cb/Pv/Att/Chain.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5LeftLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims UnitsOwed seenAfter ownTrs own_out own_last)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends PartHearLaw PartRowLaw)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

/-- f is the row of the sumcheck at a summand S0 with the three equations. -/
def RowPrem {X : Type} (S : SumL K M X) (D : SumH ρ S) (C : Aff) (hh : MaskedSum.Heard) (f : Aff) (W : World K)
    (m : M) : Prop :=
  ∃ S0 : E, f = formOf hh S0 {} ∧
    S.T.our.par.W D.st (S.msg m) = OnBytes.Road.Hd.place W.slot (S.T.our.par.vars D.st) hh.first ∧
    S.T.our.par.inc D.st (S.msg m) = ρ.val hh.target - C.value ρ W ∧
    S.T.S D.st (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) D.out.vals = ρ.val S0

/-- What a sumcheck's stage owes, in K5's words: its row is worth 0; each end value's claim. -/
def Paid {X : Type} (S : SumL K M X) (D : SumH ρ S) (f : Aff) (W : World K) (m : M) : Prop :=
  f.value ρ W = 0 ∧ ∀ a, S.T.our.par.EHolds D.out (S.msg m) a

theorem out_iff (law : PartRowLaw) {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh)
    (h : SumAt C st riders H hh Gf) {W : World K} {m : M} {f : Aff} (p : RowPrem S D C hh f W m) (x : X) :
    S.Out (D.nx x) m ↔ Paid S D f W m := by
  obtain ⟨S0, e, D1, D2, D4⟩ := p
  subst e
  exact and_congr_left' (row_uholds law S D hs hD h W S0 m D1 D2 D4).symm

/-! ## The eleven stages behind the softmax-table units -/

/-- The premises on the rows of the five sumchecks of the tail that owe their output claims. -/
structure TailPrem {X : Type} {T : Tail K M X} (dt : TailH ρ T) (x : Params.AttentionRounds) (h : Heard) (l : Left)
    (W : World K) (m : M) : Prop where
  pE : RowPrem T.sE dt.dE (.slot (h.five + 1)) h.division l.division W m
  pM : RowPrem T.sVM dt.dVM (.slot h.values) h.below l.below W m
  pVD : RowPrem T.sVD dt.dVD (.slot (h.values + 1)) h.on l.on W m
  pD : RowPrem T.sD dt.dD (batched x.pairs h.om' h.atIndex.sEnd 2 1) h.key l.key W m
  pH : RowPrem T.sH dt.dH (.ofConst zeroE) h.cells l.cells W m

/-- The tail's bill. -/
def TailBill {X : Type} {T : Tail K M X} (D : TailH ρ T) (x : X) (l : Left) (W : World K) (m : M) : Prop :=
  T.sE.L x D.dE.rd m ∧ Paid T.sE D.dE l.division W m ∧
  T.sVM.L (D.x2 x) D.dVM.rd m ∧ Paid T.sVM D.dVM l.below W m ∧
  T.sVD.L (D.x3 x) D.dVD.rd m ∧ Paid T.sVD D.dVD l.on W m ∧
  T.lF (D.x5 x) (Johnson.L5.Layers.rd ρ T.np D.mx) m ∧
  T.sF.L (D.x6 x) D.dF.rd m ∧ T.owF (D.dF.nx (D.x6 x)) m ∧
  T.sD.L (D.x8 x) D.dD.rd m ∧ Paid T.sD D.dD l.key W m ∧
  T.sH.L (D.x10 x) D.dH.rd m ∧ Paid T.sH D.dH l.cells W m

theorem tail_bill (law : PartRowLaw) {X : Type} {T : Tail K M X} (dt : TailH ρ T) {x : Params.AttentionRounds}
    {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L) (ho : TailOfP dt x h L) {l : Left} {W : World K} {m : M}
    (p : TailPrem dt x h l W m) (x0 : X) : dt.Owes x0 m ↔ TailBill dt x0 l W m := by
  unfold TailH.Owes TailBill
  rw [out_iff law T.sE dt.dE ho.zE ho.oE hs.sE p.pE x0]
  rw [show T.sVM.Out (dt.x3 x0) m ↔ _ from out_iff law T.sVM dt.dVM ho.zM ho.oM hs.sM p.pM (dt.x2 x0)]
  rw [out_iff law T.sVD dt.dVD ho.zVD ho.oVD hs.sVD p.pVD (dt.x3 x0)]
  rw [out_iff law T.sD dt.dD ho.zD ho.oD hs.sD p.pD (dt.x8 x0)]
  rw [out_iff law T.sH dt.dH ho.zH ho.oH hs.sH p.pH (dt.x10 x0)]

/-! ## The softmax-table units -/

/-- The premises on the units' rows. -/
def UnitsPrem {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → List (Nat × MaskedSum.Heard) →
    List Aff → World K → M → Prop
  | [], _, [], [], _, _ => True
  | u :: us, d, o :: os, f :: fs, W, m => RowPrem u d.1 (.slot (o.1 + 6)) o.2 f W m ∧ UnitsPrem us d.2 os fs W m
  | _, _, _, _, _, _ => False

/-- The units' bill. -/
def UnitsBill {X : Type} : (us : List (SumL K M (Seen K X))) → UnitsH ρ us → Seen K X → List Aff → World K → M → Prop
  | [], _, _, [], _, _ => True
  | u :: us, d, s, f :: fs, W, m =>
    u.L s d.1.rd m ∧ Paid u d.1 f W m ∧ UnitsBill us d.2 (s.1, s.2 ++ [List.ofFn d.1.rd]) fs W m
  | _, _, _, _, _, _ => False

theorem units_bill (law : PartRowLaw) {X : Type} {G : Fork} {W : World K} {m : M} :
    ∀ (us : List (SumL K M (Seen K X))) (d : UnitsH ρ us) (ps : List (Nat × Nat))
      (os : List (Nat × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)) (fs : List Aff) (s : Seen K X),
      UnitsAt ps os pre l G → UnitsOfP us d ps os pre l → UnitsPrem us d os fs W m →
      (UnitsOwed us d s m ↔ UnitsBill us d s fs W m)
  | [], _, [], [], _, [], [], _, _, _, _ => Iff.rfl
  | u :: us, d, _ :: ps, _ :: os, _, (_, _) :: l, _ :: fs, s, ⟨_, _, a3, _, a5⟩, ⟨z, of, hn⟩, ⟨q, qs⟩ =>
    and_congr_right' (and_congr (out_iff law u d.1 z of a3 q s)
      (units_bill law us d.2 ps os [] l fs _ a5 hn qs))
  | [], _, [], [], _, [], _ :: _, _, _, _, hp => hp.elim
  | [], _, [], [], _, _ :: _, _, _, _, ho, _ => ho.elim
  | [], _, [], _ :: _, _, _, _, _, _, ho, _ => ho.elim
  | [], _, _ :: _, _, _, _, _, _, _, ho, _ => ho.elim
  | _ :: _, _, [], _, _, _, _, _, _, ho, _ => ho.elim
  | _ :: _, _, _ :: _, [], _, _, _, _, _, ho, _ => ho.elim
  | _ :: _, _, _ :: _, _ :: _, _, [], _, _, _, ho, _ => ho.elim
  | _ :: _, _, _ :: _, _ :: _, _, _ :: _, [], _, _, _, hp => hp.elim

/-! ## The whole -/

/-- **The chain's last claim, on the run made of what was heard, is K5's bill.** -/
theorem k5_last (law : PartRowLaw) {X : Type} (A : AttOwn K M X) (du : UnitsH ρ A.units) (dt : TailH ρ A.tail)
    {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L)
    (hu : UnitsOfP A.units du x.score h.scores.toList L.planes.flatten L.units) (ht : TailOfP dt x h L)
    (Dn : X → M → Prop) (x0 : X) (m : M) (cu : UnitsClaims A.units du (x0, []))
    (ct : dt.Claims (seenAfter A.units du (x0, []))) {l : Left} {W : World K}
    (pu : UnitsPrem A.units du h.scores.toList l.scores.toList W m) (pt : TailPrem dt x h l W m) :
    A.ch.Last Dn (A.ch.run x0 (ownTrs A du dt)) m ↔
      Dn x0 m ∧ UnitsBill A.units du (x0, []) l.scores.toList W m ∧
        TailBill dt (seenAfter A.units du (x0, [])) l W m :=
  (own_last A du dt Dn x0 m cu ct).trans (and_congr_right' (and_congr
    (units_bill law A.units du _ _ _ _ _ _ hs.units hu pu) (tail_bill law dt hs ht pt _)))

/-- **K5's law, at letters.** -/
theorem k5_law (hearLaw : PartHearLaw) (rowLaw : PartRowLaw) {S : Type} (seat : Seat S) (p : Par) (s s' : S)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hz : ∀ F, seat.ledger s = some F → Sized F) :
    ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      RoundsAre L.rounds rs ∧ Said p.own h G L ∧ Sized G ∧ Stays F G ∧
      ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (M X : Type) (A : AttOwn K M X) (du : UnitsH ρ A.units)
        (dt : TailH ρ A.tail), UnitsOfP A.units du p.own.score h.scores.toList L.planes.flatten L.units →
        TailOfP dt p.own h L →
        (UnitsAreP A.units du h.scores.toList ∧ TailIsP dt p.own h L) ∧
        (∀ (Ex : ExtSpec) (x0 : X) (y : Ex.Str),
          (A.ch.R Ex).red.out (x0, y) (A.ch.join Ex (ownTrs A du dt)) = some (A.ch.run x0 (ownTrs A du dt), y)) ∧
        ∀ (Dn : X → M → Prop) (x0 : X) (m : M), UnitsClaims A.units du (x0, []) →
          dt.Claims (seenAfter A.units du (x0, [])) → ∀ (l : Left) (W : World K),
          UnitsPrem A.units du h.scores.toList l.scores.toList W m → TailPrem dt p.own h l W m →
          (A.ch.Last Dn (A.ch.run x0 (ownTrs A du dt)) m ↔
            Dn x0 m ∧ UnitsBill A.units du (x0, []) l.scores.toList W m ∧
              TailBill dt (seenAfter A.units du (x0, [])) l W m) := by
  obtain ⟨_, F, h, G, a1, a2, a3⟩ := (decide_lays seat p s s' rs).1 hd
  obtain ⟨L, b1, b2, b3, b4, b5⟩ := hear_law hearLaw a2 (hz F a1)
  exact ⟨F, G, h, L, a1, a3, b1, b2, b3, b4, fun K _ _ ρ M X A du dt hu ht =>
    ⟨b5 K ρ M X A du dt hu ht, fun Ex x0 y => own_out A du dt Ex x0 y,
      fun Dn x0 m cu ct l W pu pt => k5_last rowLaw A du dt b2 hu ht Dn x0 m cu ct pu pt⟩⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.out_iff
#print axioms VerifiableInference.Desc.First.Att.P.tail_bill
#print axioms VerifiableInference.Desc.First.Att.P.units_bill
#print axioms VerifiableInference.Desc.First.Att.P.k5_last
#print axioms VerifiableInference.Desc.First.Att.P.k5_law
