-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestPaid.lean: "the hidden scalar ZC is the batch of the reads of the
committed denominators" (the equation of `ZCRead`, Johnson/Desc/First/Att/K05Guest.lean; the first
conjunct of `TailLin`) from what the own claims of the kind K5 say, where every table is true of the
matrices.

Statements and proofs.
Main names:
  `zc_slot`: at any letters, the typed data's scalar number 2 of the sumcheck "denominator times
    output", less its mask entry, is the slot five + 2 of the ledger's world.
  `ZcSetting`: the setting and the premises of `linZcF` (Johnson/Desc/First/Att/Claims/LinZc.lean),
    gathered.
  `zc_world`: by `linZcF`, the line zc of `SayAt` makes that slot rv … .zc on the cells cellsK S M.
  `zc_paid`: the two together: dt.dE.rd iZC - msg m (kE iZC) = `zcAt P x0 m`.
  `le_paid`: at the closed parameters whose Λ.LE is the reading alone, the letter LE holds at the
    data heard.
  `matsOf`, `cells_base`, `le_paid_base`: over the committed symbols (`baseOf`), with the world's
    matrices those that the message's own symbols spell through the map of places, the last two
    premises of `zc_paid` hold by unfolding.
  `three_ord_closed`: `Three` at the closed parameters over the committed symbols (`baseOf`,
    Johnson/Desc/First/Att/K05Caller.lean), with `BaseAt`, the bound on beta and the keys' clause,
    gives L5.AttOrd S (zsOf pl Mz) by `att_ord_base` (Johnson/Road/Rows/AttStartBase.lean).
  `bounds_full`, `bounds_small`: the two bounds of `joint_bites`
    (Johnson/Desc/First/Att/K05Guest.lean) at two records of sizes, where call 2 has 2 ^ 26 and 2 ^
    20 keys.
Premises of `zc_paid`: `Said`; `TailOfP`; the plan has a unit; the place of ZC's mask entry;
`PointsAre`; `SayAt`; `ZcSetting` (every table is true of the matrices in the world; piece b is pair
b; the pieces' weights and the two points are the library's at the lookup's point; the table on the
denominators lies in the list; the indices read lie in it); L5.dimOf S = P.D; cellsK S M = P.tOf m.
Used of OnBytes, Johnson/Road and Inst: plain records, pure functions and lemmas on
them alone; no routine in a context and no theorem on a run: `AttAt`, `PiecesAll`, `TabAt`,
`cellsK`, `L5.dimOf`, `pt`, `eqTab`, `wp`, `yg`, `yi`, `rv`, `att_ord_base`, `BaseAt`, `zsOf`,
`cellValS`, `Mats`. Of this folder: `d2_slot`, `units_ne`, `msg_slot`, `Said`, `TailOfP`,
`closedOf`, `baseOf`, `SayAt`, `PointsAre`, `oldOf`.
Limits: that a table is true is not shown in this file or in what it imports. In `le_paid_base` the
matter of the last two premises lies in the setting: the shape is the planner's, the matrices fit,
and every table is true of the matrices that the message's own symbols spell. `ZcSetting` is shown
to be met at no value: `TabAt` can hold at `oldOf S gL i` only because that record's list of tables
is the kind's own (Johnson/Desc/First/Att/Claims/Any.lean: `tabBack`). `le_paid` pays a chain whose
LE says nothing of the other scalars of that message (ACC, ZO, the two high parts, the index's bits,
the last two): if another statement wants their readings of the same letter, LE grows to a
conjunction and `le_paid` has to grow with it. In `bounds_full` and `bounds_small` the number of
keys of call 2 is a premise; 2 ^ 26 is that of `Calls.ref`; neither is read off a plan. Nothing on
an honest prover or on hiding.

-/
import Johnson.Desc.First.Att.K05GuestWhole
import Johnson.Desc.First.Att.K05Caller
import Johnson.Desc.First.Att.Claims.LinZc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Road OnBytes.Road.Rows
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (SayAt PointsAre oldOf linZcF)
open Cb.Pv.Tail (Size Syms JCell cellValS BaseAt)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type}

/-- **The hidden ZC of the typed data is the ledger's world's slot five + 2.** -/
theorem zc_slot (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap) {x : Params.AttentionRounds} {h : Heard}
    {G : Fork} {L : Lists} (hs : Said x h G L) (hne : x.score ≠ []) (dt : TailH ρ (P.own Mn).tail)
    (ho : TailOfP dt x h L) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M)
    (hk : P.msg m (P.kE P.iZC) = mask (h.five + 2)) :
    dt.dE.rd P.iZC - P.msg m (P.kE P.iZC) = (G.worldOf ρ mask entry).slot (h.five + 2) := by
  have e : dt.dE.rd P.iZC = ρ.val (L.v5.getD 2 zeroE) := by
    show ρ.val (dt.dE.r.getD 2 zeroE) = _
    rw [ho.oE.r]
    unfold Lists.ridersE
    rw [units_ne hs.units hne, List.nil_append, List.getD_append _ _ _ _ (by rw [hs.l5]; omega)]
  have d := d2_slot (ρ := ρ) (hs.p5 2 (by rw [hs.l5]; omega)) rfl mask entry
  rw [Aff.value_slot] at d
  rw [e, hk, ← d]
  ring

/-- The setting and the premises of `linZcF`, at a record h' : Attention.Heard, gathered. -/
structure ZcSetting (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (Mm : Mats K) (h' : Attention.Heard)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) (C : Calls) (z : ℕ → K) : Prop where
  /-- the reading takes numerals to numbers; the shape is the planner's; the matrices fit; every
  table is true of the matrices in W -/
  att : AttAt ρ W tl K3 Mm h' lid cf fs
  /-- piece b is pair b -/
  pieces : PiecesAll h'.S h'.d.pwW
  /-- the pieces' weights are the library's -/
  hw : ∀ b < h'.S.NP, ρ.val (h'.d.pwW.getD b default).wp = wp (L5.dimOf h'.S) C z .w3 b
  hzg : h'.d.zgW.size = h'.S.cf.lgk
  hzi : h'.d.ziW.size = h'.S.cf.lt
  /-- the verifier's two points are the library's -/
  hg : ∀ j < h'.S.cf.lgk, pt ρ h'.d.zgW j = yg (L5.dimOf h'.S) C z j
  hi : ∀ j < h'.S.cf.lt, pt ρ h'.d.ziW j = yi (L5.dimOf h'.S) C z j
  /-- the table on the denominators lies in the list -/
  tab : TabAt tl h' h'.t.hW h'.S.cf.NAs h'.S.T (eqTab h'.d.ziW)
  /-- the indices read lie in the table -/
  hin : ∀ b < h'.S.NP, ∀ g < 2 ^ h'.S.cf.lgk, ∀ l < 4,
    h'.S.oZr + (l * h'.S.Lam + (h'.d.pwW.getD b default).lam) * h'.S.cf.H +
      (g * h'.S.HA + (h'.d.pwW.getD b default).a) < (h'.t.tabLen.lookup h'.t.hW).getD 0

omit [Fintype K] in
/-- **What the kind's own claims say of that slot.** -/
theorem zc_world {W : World K} {tl : HTailF2} {K3 : ℕ} {Mm : Mats K} {S : Attention.Shape} {gL : Forest.Heard}
    {i : Runs.In} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} (z : ℕ → K)
    (Zs : ZcSetting ρ W tl K3 Mm (oldOf S gL i) lid cf fs C z) (Sy : SayAt ρ W S gL i K3)
    {zk : Array (Array E)} {h : Heard} {l : Left} (H : PointsAre i.g zk h l i.p) :
    W.slot (h.five + 2) = rv (L5.dimOf S) C (pubOfZ K z) (cellsK S Mm) .zc := by
  have e := linZcF (p := pubOfZ K z) Zs.att Zs.pieces Zs.hw Zs.hzg Zs.hzi Zs.hg Zs.hi Zs.tab Zs.hin Sy.s5.zc
  rw [← H.s5]
  exact e

/-- **The guest's debt, paid at the data heard.** -/
theorem zc_paid (P : OwnPar K M X) (Mn : Means K P.D P.C P.kap) {x : Params.AttentionRounds} {h : Heard}
    {G : Fork} {L : Lists} (hs : Said x h G L) (hne : x.score ≠ []) (dt : TailH ρ (P.own Mn).tail)
    (ho : TailOfP dt x h L) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : M)
    (hk : P.msg m (P.kE P.iZC) = mask (h.five + 2)) (x0 : X)
    {tl : HTailF2} {K3 : ℕ} {Mm : Mats K} {S : Attention.Shape} {gL : Forest.Heard} {i : Runs.In} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (Zs : ZcSetting ρ (G.worldOf ρ mask entry) tl K3 Mm (oldOf S gL i) lid cf fs P.C (P.zOf x0))
    (Sy : SayAt ρ (G.worldOf ρ mask entry) S gL i K3) {zk : Array (Array E)} {l : Left}
    (H : PointsAre i.g zk h l i.p) (hD : L5.dimOf S = P.D) (hcell : cellsK S Mm = P.tOf m) :
    dt.dE.rd P.iZC - P.msg m (P.kE P.iZC) = zcAt P x0 m := by
  rw [zc_slot P Mn hs hne dt ho mask entry m hk, zc_world (P.zOf x0) Zs Sy H, hD, hcell]
  rfl

/-- **At the closed parameters whose Λ.LE is the reading alone, the letter LE holds at the data
heard.** -/
theorem le_paid {M0 Mg : Type} (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums)
    (hΛ : ∀ s r m, Λ.LE s r m ↔ r P0.iZC - Λ.maskOf m (N.five + 2) =
      AttSeg.rv P0.D P0.C (pubOfZ K (P0.zOf s.1)) (P0.tOf (Λ.restOf m)) .zc)
    (Mn : Means K (closedOf P0 Λ ns N).D (closedOf P0 Λ ns N).C (closedOf P0 Λ ns N).kap)
    {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L) (hne : x.score ≠ [])
    (dt : TailH ρ ((closedOf P0 Λ ns N).own Mn).tail) (ho : TailOfP dt x h L) (entry : ℕ → ℕ → ℕ → K) (m : Mg)
    (hN : N.five = h.five) (hns : N.five + 2 ≤ ns) (sn : Seen K X)
    {tl : HTailF2} {K3 : ℕ} {Mm : Mats K} {S : Attention.Shape} {gL : Forest.Heard} {i : Runs.In} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (Zs : ZcSetting ρ (G.worldOf ρ (Λ.maskOf m) entry) tl K3 Mm (oldOf S gL i) lid cf fs P0.C (P0.zOf sn.1))
    (Sy : SayAt ρ (G.worldOf ρ (Λ.maskOf m) entry) S gL i K3) {zk : Array (Array E)} {l : Left}
    (H : PointsAre i.g zk h l i.p) (hD : L5.dimOf S = P0.D) (hcell : cellsK S Mm = P0.tOf (Λ.restOf m)) :
    (closedOf P0 Λ ns N).LE sn dt.dE.rd m := by
  have hk : (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kE (closedOf P0 Λ ns N).iZC) =
      Λ.maskOf m (h.five + 2) := by
    rw [← hN]
    exact msg_slot P0 Λ ns N m hns
  have e := zc_paid (closedOf P0 Λ ns N) Mn hs hne dt ho (Λ.maskOf m) entry m hk sn.1 Zs Sy H hD hcell
  rw [hk, ← hN] at e
  exact (hΛ sn _ m).2 e

section Fit
variable {s : Size} {Mg : Type}

/-- **The letters fit**: `Three` at the closed parameters over the committed symbols is the premises
own1, own2 and ridden of `att_ord_base`. -/
theorem three_ord_closed (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (zOf : X → ℕ → K) (Λ : Lin (baseOf (K := K) S pl C npl zOf) Mg) (ns : ℕ) (N : Nums) (m : Mg)
    (h3 : Three (closedOf (baseOf S pl C npl zOf) Λ ns N) m)
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (φ : Cb.Gl.F →+* K)
    (hB : BaseAt (Λ.restOf m) Mz) (h2 : 2 * (s.beta : ℤ) ≤ 2 ^ 18)
    (keys : ∀ (q : Fin 4) (Y : ℕ), Y < (L5.dimOf S).used q →
      keyVec (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S)
          ((closedOf (baseOf S pl C npl zOf) Λ ns N).tOf m) q Y ∈
        lutSet (lut (scl := L5.sclOf S) (L5.dimOf S) (L5.tbOf S) q)) :
    L5.AttOrd S (zsOf pl Mz) :=
  att_ord_base φ hB pl h2 (t := (closedOf (baseOf S pl C npl zOf) Λ ns N).tOf m)
    (fun _ => rfl) h3.1 h3.2.1 keys h3.2.2

/-- The matrices that the committed symbols spell, through the map of places. -/
noncomputable def matsOf (pl : ℕ → ℕ → ℕ → JCell s) (y : Syms K s) : Mats K := fun a r c => cellValS y (pl a r c)

omit [Fintype K] in
/-- **The seam of the cells is a definition's unfolding** over the committed symbols: the cells read
in these matrices are the cells of the closed parameters' base. -/
theorem cells_base [Fintype K] (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (zOf : X → ℕ → K) (y : Syms K s) :
    cellsK S (matsOf pl y) = (baseOf (K := K) S pl C npl zOf).tOf y := rfl

/-- **le_paid over the committed symbols**: hD and hcell are no premises of their own any more:
their matter now lies in the setting, which speaks of the matrices that the message's own symbols
spell (the shape is the planner's; the matrices fit; every table is true of these matrices). -/
theorem le_paid_base (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (zOf : X → ℕ → K) (Λ : Lin (baseOf (K := K) S pl C npl zOf) Mg) (ns : ℕ) (N : Nums)
    (hΛ : ∀ sn r m, Λ.LE sn r m ↔ r (baseOf (K := K) S pl C npl zOf).iZC - Λ.maskOf m (N.five + 2) =
      AttSeg.rv (L5.dimOf S) C (pubOfZ K (zOf sn.1)) ((baseOf (K := K) S pl C npl zOf).tOf (Λ.restOf m)) .zc)
    (Mn : Means K (closedOf (baseOf S pl C npl zOf) Λ ns N).D (closedOf (baseOf S pl C npl zOf) Λ ns N).C
      (closedOf (baseOf S pl C npl zOf) Λ ns N).kap)
    {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (hs : Said x h G L) (hne : x.score ≠ [])
    (dt : TailH ρ ((closedOf (baseOf S pl C npl zOf) Λ ns N).own Mn).tail) (ho : TailOfP dt x h L)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) (hN : N.five = h.five) (hns : N.five + 2 ≤ ns) (sn : Seen K X)
    {tl : HTailF2} {K3 : ℕ} {gL : Forest.Heard} {i : Runs.In} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape}
    (Zs : ZcSetting ρ (G.worldOf ρ (Λ.maskOf m) entry) tl K3 (matsOf pl (Λ.restOf m)) (oldOf S gL i) lid cf fs C
      (zOf sn.1))
    (Sy : SayAt ρ (G.worldOf ρ (Λ.maskOf m) entry) S gL i K3) {zk : Array (Array E)} {l : Left}
    (H : PointsAre i.g zk h l i.p) :
    (closedOf (baseOf S pl C npl zOf) Λ ns N).LE sn dt.dE.rd m :=
  le_paid (baseOf S pl C npl zOf) Λ ns N hΛ Mn hs hne dt ho entry m hN hns sn Zs Sy H rfl rfl

end Fit

/-- The two bounds of `joint_bites` at the sizes ⟨3, 3, 6, 7, 5, 4, u0⟩, with call 2 of 2 ^ 26 keys.
-/
theorem bounds_full (u0 : ℕ) (C : AttSeg.Calls) (hC : C.a 2 = 26) :
    1 ≤ (⟨3, 3, 6, 7, 5, 4, u0⟩ : AttSeg.Dim).nb ∧
      (⟨3, 3, 6, 7, 5, 4, u0⟩ : AttSeg.Dim).nb ≤ 2 ^ (C.a 2 - (⟨3, 3, 6, 7, 5, 4, u0⟩ : AttSeg.Dim).lW) := by
  rw [hC]
  exact ⟨by show 1 ≤ 4 * 5; norm_num, by show 4 * 5 ≤ 2 ^ (26 - (1 + 3 + (3 + 1 + 6) + 7)); norm_num⟩

/-- The same at the sizes ⟨1, 1, 4, 7, 2, 4, u0⟩, with call 2 of 2 ^ 20 keys. -/
theorem bounds_small (u0 : ℕ) (C : AttSeg.Calls) (hC : C.a 2 = 20) :
    1 ≤ (⟨1, 1, 4, 7, 2, 4, u0⟩ : AttSeg.Dim).nb ∧
      (⟨1, 1, 4, 7, 2, 4, u0⟩ : AttSeg.Dim).nb ≤ 2 ^ (C.a 2 - (⟨1, 1, 4, 7, 2, 4, u0⟩ : AttSeg.Dim).lW) := by
  rw [hC]
  exact ⟨by show 1 ≤ 4 * 2; norm_num, by show 4 * 2 ≤ 2 ^ (20 - (1 + 1 + (1 + 1 + 4) + 7)); norm_num⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.zc_slot
#print axioms VerifiableInference.Desc.First.Att.P.zc_world
#print axioms VerifiableInference.Desc.First.Att.P.zc_paid
#print axioms VerifiableInference.Desc.First.Att.P.le_paid
#print axioms VerifiableInference.Desc.First.Att.P.three_ord_closed
#print axioms VerifiableInference.Desc.First.Att.P.cells_base
#print axioms VerifiableInference.Desc.First.Att.P.le_paid_base
#print axioms VerifiableInference.Desc.First.Att.P.bounds_full
#print axioms VerifiableInference.Desc.First.Att.P.bounds_small
