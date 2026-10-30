-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/DsTailLens.lean: K4's WRITTEN ROUNDS MEET THE THREE PREMISES ON THE WRITTEN ROUNDS
OF THE MAPS TO THE LIBRARY's CHAIN OF A LAYERS' SUB-PROOF's OWN ROUNDS
(OnBytes/Desc/First/P1/OwnMaps.lean, OwnMapsPlan.lean): `DrawsPt` at the points in front, `TailDs`,
`TailLens`; UNDER THESE PREMISES: the chain's numbers are those of a planner's record x (`TailIs`,
OnBytes/Tie/Pv/Lay/OwnPlan.lean; and one | three equations on its points), nine numbers of x are
K4's (`LensTie`), and three numbers of the place are the layout's sums (`Mu`). Definitions,
statements and proofs. (The maps take `TailIs` and a numbering of the end values besides.)

`LensTie p x`: nine numbers of the record x are the place's: lt, ls, lNI, lPd, ll, lPf, lfe, lamS,
lkW. `lensTie_numbers`: so it is at the record from which the format's planner plans these rounds
(`Verify.layerNumbers p.P p.hp p.g`, OnBytes/Model/VerifySubproofs.lean), by definition.
`Mu P`: the three product layers' numbers of variables are the sums that the layout's routine
computes. `mu_of_pub`, `mu_of_public`: so it is at what `Layer.Pub.of` returns, and at the public
record's layers with whatever tokens laid in (by `Fo.pubOf_mu`, `Fo.public_mu`).
`Pieces.tailLens`: under `Mu` and `LensTie` the seven sumchecks' rounds for their variables are as
many as x says. `Pieces.at_chain`: under `LensTie` and `TailIs`: `TailDs`.
`own_at` (meant for g ≠ 0), `ownFirst_at` (meant for g = 0; neither has a premise on g): UNDER
`Mu p.P`, `LensTie p x`, `TailIs A.tail x` AND THE EQUATIONS ON A's POINTS (A.gT = x.lt; for the
second also A.gA = x.ls + x.lt, A.gB = x.lPd - x.ls): `DrawsPt`, `TailDs A.tail R` and
`TailLens R x` AT THE DATA: R is `tailR (numsOf p.P p.hp p.g)`, the points' rounds are `rdOf` of
their rows (Johnson/Road/K4/DsTailR.lean). `k4_own`, `k4_ownFirst`: the same under «there are»,
with `k4Ds p` the list that `ownM` (`ownFirstM`) is written over.
`sent_at_plan`: at a chain whose numbers are those of `Verify.layerNumbers p.P p.hp p.g`, the three
rounds of sent scalars send as many elements as the chain's three rounds hold.

Limits. `TailIs` and the points' equations are premises on the chain's letters: no chain's value is
made here. That a chain's record x (made from the library's sizes, say) meets `LensTie` at a real
plan's place is nine equations between two sets of numbers: not shown here, but at
`Verify.layerNumbers`. TEN FIELDS OF x ARE TIED TO NOTHING BY `LensTie` (NI NS NP NO withTerms
shownByTheTerms neverSent weightClaims firstGroup routed), AND `TailDs` LEAVES OPEN HOW MANY
ELEMENTS A ROUND SENDS: so `k4_own` also holds at an x whose firstGroup is true though g ≠ 0, where
the chain's round of the weight claims holds a scalar that the written round does not send (the maps
then read 0). Of the seven sumchecks' messages no count is compared with the chain's here; whoever
does so will want `covers`: the end values of the third and the fourth (nEndT; 1 + LamM) need not be
the planner's numbers where there are no terms or no routed experts. THAT A PIECE OF A CHAIN HAS
THESE ROUNDS (`k4Ds par = some pc.ds`) IS WHOEVER CUTS THE CHAIN's TO SHOW. This speaks of the
rounds that K4's block declares (DsTail.lean's Limits). Nothing on which written scalar is which
typed one, on the errors, or on soundness.
-/
import Johnson.Road.K4.DsTailR
import OnBytes.Desc.First.P1.OwnMapsPlan
import OnBytes.Model.VerifySubproofs
import OnBytes.Tie.Pv.Lookup.Ends.FoLayerMu

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Slice OnBytes.Flat
open OnBytes.Desc.First.K4 OnBytes.Desc.First.P1

/-- Nine numbers of a planner's record are the place's. -/
structure LensTie (p : Par) (x : Params.LayerRounds) : Prop where
  lt : x.lt = p.P.y.h.lt
  ls : x.ls = p.P.y.ls
  lNI : x.lNI = p.P.rd.lNI
  lPd : x.lPd = p.P.y.lPd
  ll : x.ll = p.P.y.h.ll
  lPf : x.lPf = p.P.y.lPf
  lfe : x.lfe = p.P.y.lfe
  lamS : x.lamS = p.hp.lamS
  lkW : x.lkW = p.P.wsLay.lk

/-- So it is at the record from which the format's planner plans these rounds. -/
theorem lensTie_numbers (p : Par) : LensTie p (Verify.layerNumbers p.P p.hp p.g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The three product layers' numbers of variables are the layout's sums. -/
structure Mu (P : Layer.Pub) : Prop where
  v : P.rd.muV = P.rd.lNI + P.y.lPd + P.y.h.lt
  h : P.rd.muH = P.y.h.ll + P.y.lPf + P.y.h.lt
  h2 : P.rd.muH2 = P.y.h.ll - 1 + P.y.lfe + P.y.h.lt

theorem mu_of_pub {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {P : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok P) : Mu P :=
  ⟨(Fo.pubOf_mu h).1, (Fo.pubOf_mu h).2.1, (Fo.pubOf_mu h).2.2⟩

theorem mu_of_public {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (tk : Array Nat) :
    Mu { X.layers with tokv := tk } :=
  ⟨(Fo.public_mu h tk).1, (Fo.public_mu h tk).2.1, (Fo.public_mu h tk).2.2⟩

/-- **The seven sumchecks' rounds for their variables are as many as the record says**, under `Mu`
and `LensTie`. -/
theorem Pieces.tailLens {p : Par} {x : Params.LayerRounds} {R : TailR} {gN gR : Nat}
    (h : Pieces R gN gR p.P.rd.muV p.P.y.h.lt p.P.y.h.lt p.hp.lamS p.P.rd.muH p.P.rd.muH2
      p.P.wsLay.lk) (m : Mu p.P) (t : LensTie p x) : TailLens R x :=
  ⟨by rw [h.n1, m.v, t.lNI, t.lPd, t.lt], by rw [h.n2, t.lt], by rw [h.n3, t.lt],
    by rw [h.n4, t.lamS], by rw [h.n5, m.h, t.ll, t.lPf, t.lt],
    by rw [h.n6, m.h2, t.ll, t.lfe, t.lt], by rw [h.n7, t.lkW]⟩

/-- What OwnMaps.lean asks of the written rounds, at a chain whose numbers are the record's, under
`LensTie` and `TailIs`. -/
theorem Pieces.at_chain {M X : Type} {T : Cb.Pv.Lay.LayTail OnBytes.Slice.GE M X} {p : Par}
    {x : Params.LayerRounds} {R : TailR} {l1 l2 l3 l4 l5 l6 l7 : Nat}
    (h : Pieces R p.P.rd.lNI (p.P.y.h.ll - 1) l1 l2 l3 l4 l5 l6 l7) (t : LensTie p x)
    (hT : OnBytes.Tie.Pv.Lay.TailIs T x) : TailDs T R := by
  have h' : Pieces R T.gN T.gR l1 l2 l3 l4 l5 l6 l7 := by
    rw [hT.gN, hT.gR, t.lNI, t.ll]
    exact h
  exact h'.tailDs

/-! ### At the data -/

/-- **The data of K4's written rounds meet the three premises on the written rounds**, under `Mu`,
`LensTie`, `TailIs` and the equation on the chain's point. -/
theorem own_at {M X : Type} (A : Cb.Pv.Lay.LayOwn OnBytes.Slice.GE M X) {p : Par}
    {x : Params.LayerRounds} (m : Mu p.P) (t : LensTie p x) (hT : A.gT = x.lt)
    (h : OnBytes.Tie.Pv.Lay.TailIs A.tail x) :
    DrawsPt A.gT (rdOf (pointRd .zero p.P.y.h.lt)) ∧
      TailDs A.tail (tailR (numsOf p.P p.hp p.g)) ∧ TailLens (tailR (numsOf p.P p.hp p.g)) x := by
  have hP : Pieces (tailR (numsOf p.P p.hp p.g)) p.P.rd.lNI (p.P.y.h.ll - 1) p.P.rd.muV p.P.y.h.lt
      p.P.y.h.lt p.hp.lamS p.P.rd.muH p.P.rd.muH2 p.P.wsLay.lk := tailR_pieces _
  refine ⟨?_, hP.at_chain t h, hP.tailLens m t⟩
  rw [hT, t.lt]
  exact rdOf_draws (pointRd .zero p.P.y.h.lt) (Nat.zero_le _)

/-- **The same at a chain of a first sub-proof**, under `Mu`, `LensTie`, `TailIs` and the equations
on the chain's three points. -/
theorem ownFirst_at {M X : Type} (A : Cb.Pv.Lay.LayOwnFirst OnBytes.Slice.GE M X) {p : Par}
    {x : Params.LayerRounds} (m : Mu p.P) (t : LensTie p x) (hT : A.gT = x.lt)
    (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls)
    (h : OnBytes.Tie.Pv.Lay.TailIs A.tail x) :
    DrawsPt A.gT (rdOf (pointRd .zero p.P.y.h.lt)) ∧
      DrawsPt A.gA (rdOf (pointRd .zero (p.P.y.ls + p.P.y.h.lt))) ∧
      DrawsPt A.gB (rdOf (pointRd .zero (p.P.y.lPd - p.P.y.ls))) ∧
      TailDs A.tail (tailR (numsOf p.P p.hp p.g)) ∧ TailLens (tailR (numsOf p.P p.hp p.g)) x := by
  have hP : Pieces (tailR (numsOf p.P p.hp p.g)) p.P.rd.lNI (p.P.y.h.ll - 1) p.P.rd.muV p.P.y.h.lt
      p.P.y.h.lt p.hp.lamS p.P.rd.muH p.P.rd.muH2 p.P.wsLay.lk := tailR_pieces _
  refine ⟨?_, ?_, ?_, hP.at_chain t h, hP.tailLens m t⟩
  · rw [hT, t.lt]
    exact rdOf_draws (pointRd .zero p.P.y.h.lt) (Nat.zero_le _)
  · rw [hA, t.ls, t.lt]
    exact rdOf_draws (pointRd .zero (p.P.y.ls + p.P.y.h.lt)) (Nat.zero_le _)
  · rw [hB, t.lPd, t.ls]
    exact rdOf_draws (pointRd .zero (p.P.y.lPd - p.P.y.ls)) (Nat.zero_le _)

/-- **The three rounds of sent scalars send as many elements as the chain's rounds hold**, at a
chain whose numbers are those of the format's planner's own record at the place. -/
theorem sent_at_plan {M X : Type} {T : Cb.Pv.Lay.LayTail OnBytes.Slice.GE M X} {p : Par}
    (h : OnBytes.Tie.Pv.Lay.TailIs T (Verify.layerNumbers p.P p.hp p.g)) :
    (tailR (numsOf p.P p.hp p.g)).dL.items = List.replicate T.nL .e ∧
      (tailR (numsOf p.P p.hp p.g)).dP.items = List.replicate T.nP .e ∧
      (tailR (numsOf p.P p.hp p.g)).dW.items = List.replicate T.nW .e := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.nL]
    exact rdOf_items _
  · rw [h.nP]
    exact rdOf_items _
  · rw [h.nW]
    exact rdOf_items _

/-! ### Under «there are» -/

/-- **K4's written rounds meet the three premises on the written rounds**, at a sub-proof that is
not the first, under `Mu`, `LensTie`, `TailIs` and the equation on the chain's point. -/
theorem k4_own {M X : Type} (A : Cb.Pv.Lay.LayOwn OnBytes.Slice.GE M X) {p : Par}
    {x : Params.LayerRounds} (hg : (p.g == 0) = false) (m : Mu p.P) (t : LensTie p x)
    (hT : A.gT = x.lt) (h : OnBytes.Tie.Pv.Lay.TailIs A.tail x) :
    ∃ (dT : RDT) (R : TailR), k4Ds p = some ([dT] ++ R.all) ∧ DrawsPt A.gT dT ∧
      TailDs A.tail R ∧ TailLens R x :=
  ⟨_, _, k4Ds_later hg, own_at A m t hT h⟩

/-- **The first sub-proof's**, under `Mu`, `LensTie`, `TailIs` and the equations on the chain's
three points. -/
theorem k4_ownFirst {M X : Type} (A : Cb.Pv.Lay.LayOwnFirst OnBytes.Slice.GE M X) {p : Par}
    {x : Params.LayerRounds} (hg : (p.g == 0) = true) (m : Mu p.P) (t : LensTie p x)
    (hT : A.gT = x.lt) (hA : A.gA = x.ls + x.lt) (hB : A.gB = x.lPd - x.ls)
    (h : OnBytes.Tie.Pv.Lay.TailIs A.tail x) :
    ∃ (dT dA dB : RDT) (R : TailR), k4Ds p = some ([dT] ++ ([dA] ++ ([dB] ++ R.all))) ∧
      DrawsPt A.gT dT ∧ DrawsPt A.gA dA ∧ DrawsPt A.gB dB ∧ TailDs A.tail R ∧ TailLens R x :=
  ⟨_, _, _, _, k4Ds_first hg, ownFirst_at A m t hT hA hB h⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.lensTie_numbers
#print axioms OnBytes.Road.K4.mu_of_pub
#print axioms OnBytes.Road.K4.mu_of_public
#print axioms OnBytes.Road.K4.Pieces.tailLens
#print axioms OnBytes.Road.K4.own_at
#print axioms OnBytes.Road.K4.ownFirst_at
#print axioms OnBytes.Road.K4.sent_at_plan
#print axioms OnBytes.Road.K4.k4_own
#print axioms OnBytes.Road.K4.k4_ownFirst
