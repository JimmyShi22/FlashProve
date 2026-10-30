-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkOne.lean: ONE NAMED Ok FOR THE LAW OF A LINK, A SORT AT A TIME.
Definitions (structures of sentences on what is fixed), and theorems: projections.
READ THIS FIRST. IT IS A DEFINITION BY CONJUNCTION. Many clauses of the three sorts' Takes
(PayLayers.lean, PayAttention.lean, PayHead.lean), of `fuEq_full` (FullEq.lean), of the seven
sisters (SistersFull.lean) and of the link's one list (LinkList.lean: hOk4, okDig, okEnts) BEGIN
WITH Ok: "for all q: Ok q, guards on q: a body at q". Here Ok IS the conjunction of these bodies
under their guards. So each such field follows by a projection. **THE PROJECTIONS ARE NO PAYMENTS:
NOBODY MAY COUNT THEM AS SUCH.** All their weight lies on one debt a link: `Ok‹sort› (fixed9 φ a.1)`
at the states of `LinkOwes`' hready and of HitemsJoin.lean's hon.
WHAT IS NOT GATHERED HERE. OTHER FIELDS NAME Ok ON THE OTHER SIDE: the Takes' h4, k3, k3d and
`OwesNumbers`' hok ask a law of a run UNDER Ok (`RunOk .. (O9 φ Ok Fu) (Fx9 φ Ok) ..`). A stronger
Ok makes these easier, and THE THEOREMS THAT END IN THEM ASK SOMETHING OF Ok: for k3: `K3Ok`
(Johnson/Top/H/Keep/RunsPlain.lean) at the link's two lookup seats. NONE OF THAT IS A CLAUSE HERE.
SO AT Ok := `OkLayers`, `OkAtt` OR `OkHead` ALONE THE FIELD k3 MAY HAVE NO PAYER. The cure stands
outside this file: Ok := the named Ok AND one more letter; every `core_*` below, and the Takes'
builders, are general in Ok.
THE DANGER OF SUCH A DEFINITION: it may ask too much, so that no state has it, and the list is
empty.
  `OkCore nU tlD q`: snap, there: the snapshot and the structure are there; static (`StaticOk`,
    OkJoin.lean); fits; dig (`DigStatic`, RestStatic.lean); pos (`fuEq_full`'s okPos); four (the
    list's hOk4); ents4 (the list's okEnts). ITS LETTER nU IS READ BY NONE OF THE EIGHT: it stands
    so that the four structures bear one row of letters. ents4 SAYS LITTLE: where the digits' lookup
    has made what was heard, the forms of `four8` name no entry
    (Johnson/Top/H/Keep/Four8Slots.lean).
  `EntsOk nU q l`: the test `entsAtB` (EntAtTests.lean) says yes of the forms l at q's structure and
    the snapshot's looks. `OkLayers`, `OkAtt`, `OkHead`: the core, the sort's own promises on filled
    slots, and `EntsOk` of each run's forms. `OkAt sub ..`: by the sort.
  `core_*`: the fields that the core gives, for whatever Ok holds the core: okEq; fuEq; hOk4; okDig;
    okEnts. `okL_*`, `okA_*`, `okH_*`: each sort's fields. Behind each sort an `example` with
    `oneText`: Lean's check that the projection and the structure's field have ONE TYPE, up to
    unfolding of definitions: not that two texts agree sign for sign.
  `snap_there_of_part`: where a part is there, the clauses snap and there hold of what is fixed.
WHAT OF THE DEBT IS OPEN is held by Lean, not here: CoreAtBatch.lean and SortsAtBatch.lean join the
clauses that are shown at reached states elsewhere, and keep the others as the fields of
`OkCoreLeft`, `OkLayersLeft`, `OkAttLeft`, `OkHeadLeft`.
Limits. NOTHING IS SHOWN OF ANY STATE HERE but `snap_there_of_part`. WHETHER ANY STATE HAS
`OkLayers`, `OkAtt` OR `OkHead` WHOLE IS NOT KNOWN. Nothing on soundness.


-/
import Johnson.Desc.First.Link.Law.EntAtTests
import Johnson.Desc.First.Link.Law.FullEq
import Johnson.Desc.First.Link.Law.WorthLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Sized Filled)
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU Fits)
open VerifiableInference.Desc.K4Values (backForms frontForms frontWins winOf)
open VerifiableInference.Desc.First.TailClaims (rkSelfTestP)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

/-- Two proofs of one sentence. Where Lean takes `oneText a b`, a and b have one type, up to
unfolding of definitions. -/
theorem oneText {P : Prop} (_ _ : P) : True := trivial

variable {β : Type}

/-! ## 1 The definitions -/

/-- **WHAT EVERY SORT's Ok HOLDS.** -/
structure OkCore (nU : Array ℕ) (tlD : HTailF2) (q : Q β) : Prop where
  /-- the snapshot is there -/
  snap : q.2.isSome = true
  /-- the structure is there -/
  there : ((pi8 q.1).1).isSome = true
  static : ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F
  fits : ∀ tlb, (pi8 q.1).1 = some tlb → Fits tlb
  dig : ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v → DigStatic tlD tlb v.F
  pos : ∀ tlb funs v, pi8 q.1 = (some tlb, some funs) → q.2 = some v →
    ∀ x ∈ readsList tlb funs, ∀ d, d < (tlb.mats.getD x.1.mat {}).k →
      posOf tlb x.1 x.2 d < colsU v.F (uOf tlb x.1)
  four : ∀ v tlb g, q.2 = some v → (pi8 q.1).1 = some tlb → tlb.heard = some g →
    Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
      K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1
  ents4 : ∀ tlb g, (pi8 q.1).1 = some tlb → tlb.heard = some g →
    ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row

/-- The test on the entries says yes of the forms l, at q's structure and the snapshot's looks. -/
def EntsOk (nU : Array ℕ) (q : Q β) (l : List Aff) : Prop :=
  ∀ tlb v, (pi8 q.1).1 = some tlb → q.2 = some v →
    entsAtB nU tlb (v.F.trees.toList.map look) l = true

/-- **Ok AT A LAYERS' LINK.** -/
structure OkLayers (p : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD : HTailF2) (q : Q β) :
    Prop where
  core : OkCore nU tlD q
  front : ∀ o v, q.1.own = some o → q.2 = some v → Sized v.F ∧
    (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1
  back : ∀ o v, q.1.own = some o → q.2 = some v → Sized v.F ∧
    ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1
  entsFront : ∀ o v, q.1.own = some o → q.2 = some v →
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → EntsOk nU q l
  entsBack : ∀ o, q.1.own = some o → EntsOk nU q (backForms o)

/-- **Ok AT AN ATTENTION LINK.** -/
structure OkAtt (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (nU : Array ℕ)
    (tlD : HTailF2) (q : Q β) : Prop where
  core : OkCore nU tlD q
  k5 : ∀ v g h, q.2 = some v → rd q.1 = some (g, h) → K5OkAt c g.zk h v.F
  entsFirst : ∀ l, fsFirst rd c q = some l → EntsOk nU q l
  entsSecond : ∀ l, fsSecond rd c q = some l → EntsOk nU q l

/-- **Ok AT THE HEAD's LINK.** -/
structure OkHead (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen) (nU : Array ℕ) (tlD : HTailF2) (q : Q β) : Prop where
  core : OkCore nU tlD q
  k6 : ∀ z u, kap q.1 = some z → q.2 = some u → K6Ready h iU3 p z u.F
  join : ∀ z u g, kap q.1 = some z → q.2 = some u → z.lookHeard = some g → CEndFilled g u.F
  merge : ∀ wo v, q.1.wo = some wo → q.2 = some v → Sized v.F ∧
    ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList, K4Values.InWin (winOf wo.p) x.1 ∨ Filled v.F x.1
  entsK6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ l, fsK6 h iU3 p kap name q = some l →
    EntsOk nU q l
  entsJoin : ∀ l, fsJoin h iU3 p kap q = some l → EntsOk nU q l
  entsMerge : ∀ wo, q.1.wo = some wo → EntsOk nU q [wo.p.rowForm wo.fvp {}]

/-- **Ok, BY THE LINK's SORT.** -/
def OkAt (sub : First.ModelPart) (pL : OnBytes.Desc.First.K4.Par)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (pH : Kinds.Head.Par) (kap : Phi β → Option Seen)
    (nU : Array ℕ) (tlD : HTailF2) :
    Q β → Prop :=
  match sub with
  | .layers => OkLayers pL nU tlD
  | .attention => OkAtt rd c nU tlD
  | .head => OkHead h iU3 pH kap nU tlD

/-! ## 2 What the core gives, for whatever Ok holds it -/

section Core
variable {nU : Array ℕ} {tlD : HTailF2} {Ok : Q β → Prop} (hc : ∀ q, Ok q → OkCore nU tlD q)
include hc

theorem core_k8 : ∀ q, Ok q → OkK8 pi8 q := fun q h => ⟨(hc q h).snap, (hc q h).static⟩

/-- The entries of forms that pass the test stand at virtual row 0 of a table's vector. -/
theorem core_ents {q : Q β} (h : Ok q) {l : List Aff} (he : EntsOk nU q l) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt pi8 nU q x := by
  obtain ⟨tlb, h1⟩ := Option.isSome_iff_exists.1 (hc q h).there
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hc q h).snap
  exact entAt_of_B pi8 h1 hv (he tlb v h1 hv)

/-- The three Takes' field okEq. -/
theorem core_okEq : ∀ q tlb, Ok q → (pi8 q.1).1 = some tlb → Fits tlb :=
  fun q tlb h h1 => (hc q h).fits tlb h1

/-- The three Takes' field fuEq, at `FullAt nU`. -/
theorem core_fuEq (u : HTailF2) (ψ : S → β) :
    ∀ q t b ts funs, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      t.tl? = some ts → t.funs? = some funs →
      rkSelfTestP ts b.F = .ok () ∧
        (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
        ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
          ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1) :=
  fuEq_full u ψ Ok nU (okK8_blocks pi8 Ok (core_k8 hc))
    (fun q tlb funs v h => (hc q h).pos tlb funs v) (okK8_apart pi8 Ok (core_k8 hc))
    (okK8_looks pi8 Ok (core_k8 hc))

/-- The list's field hOk4. -/
theorem core_hOk4 (C : Q β → Prop) : ∀ q v tlb g, (Ok q ∧ C q) → q.2 = some v →
    (pi8 q.1).1 = some tlb → tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g,
      ∀ x ∈ cl.form.slots.toList, K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1 :=
  fun q v tlb g h => (hc q h.1).four v tlb g

/-- The list's field okDig. -/
theorem core_okDig (C : Q β → Prop) : ∀ q tlb v, (Ok q ∧ C q) → (pi8 q.1).1 = some tlb →
    q.2 = some v → DigStatic tlD tlb v.F := fun q tlb v h => (hc q h.1).dig tlb v

/-- The list's field okEnts. -/
theorem core_okEnts (C : Q β → Prop) : ∀ q tlb g, (Ok q ∧ C q) → (pi8 q.1).1 = some tlb →
    tlb.heard = some g → ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row :=
  fun q tlb g h => (hc q h.1).ents4 tlb g

end Core

/-- **Where a part is there, the snapshot and the structure are there.** -/
theorem snap_there_of_part (u : HTailF2) (ψ : S → β) (s : S)
    (h : (atS.get? s).isSome = true) :
    (fixed9 (phiAll u ψ) s).2.isSome = true ∧
      ((pi8 (fixed9 (phiAll u ψ) s).1).1).isSome = true := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h
  refine ⟨by simpa [fixed9] using h, ?_⟩
  show (s.tl?.map (blank u)).isSome = true
  have hs := K9.segAt_of_atS s a ha
  unfold K9.segAt? at hs
  cases ht : s.tl? with
  | some tl => rfl
  | none =>
    rw [ht] at hs
    cases s.link? <;> cases s.fork? <;> simp at hs

/-! ## 3 The sorts' own fields -/

section Layers
variable (p : OnBytes.Desc.First.K4.Par) (nU : Array ℕ) (tlD : HTailF2)

theorem okL_core : ∀ q : Q β, OkLayers p nU tlD q → OkCore nU tlD q := fun _ h => h.core

theorem okL_front : ∀ (q : Q β) o v, OkLayers p nU tlD q → q.1.own = some o → q.2 = some v →
    Sized v.F ∧ (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
      (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1 := fun _ o v h => h.front o v

theorem okL_back : ∀ (q : Q β) o v, OkLayers p nU tlD q → q.1.own = some o → q.2 = some v →
    Sized v.F ∧ ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1 := fun _ o v h => h.back o v

theorem okL_fuFront (u : HTailF2) (ψ : S → β) :
    ∀ q o v t b y, Fx9 (phiAll u ψ) (OkLayers p nU tlD) q t → FullAt nU t →
    atS.get? t = some b → q.1.own = some o → q.2 = some v →
    ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuFront_full u ψ (OkLayers p nU tlD) nU p fun _ o v h ho hv l hl =>
    core_ents (okL_core p nU tlD) h (h.entsFront o v ho hv l hl)

theorem okL_fuBack (u : HTailF2) (ψ : S → β) :
    ∀ q o t b y, Fx9 (phiAll u ψ) (OkLayers p nU tlD) q t → FullAt nU t →
    atS.get? t = some b → q.1.own = some o → ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuBack_full u ψ (OkLayers p nU tlD) nU fun _ o h ho =>
    core_ents (okL_core p nU tlD) h (h.entsBack o ho)

/-- Lean's own check: the six are `LayersTake`'s fields at this Ok, `FullAt nU` and `entUnit`. -/
example {L : Link S Claim} {u : HTailF2} {ψ : S → β} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ (OkLayers p nU tlD) (FullAt nU) p nU entUnit tm4 t3 l3) : True :=
  have _ := oneText A.okFront (okL_front p nU tlD)
  have _ := oneText A.okBack (okL_back p nU tlD)
  have _ := oneText A.okEq (core_okEq (okL_core p nU tlD))
  have _ := oneText A.fuEq (core_fuEq (okL_core p nU tlD) u ψ)
  have _ := oneText A.fuFront (okL_fuFront p nU tlD u ψ)
  oneText A.fuBack (okL_fuBack p nU tlD u ψ)

end Layers

section Attention
variable (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (nU : Array ℕ)
  (tlD : HTailF2)

theorem okA_core : ∀ q : Q β, OkAtt rd c nU tlD q → OkCore nU tlD q := fun _ h => h.core

theorem okA_k5 : ∀ (q : Q β) v g h, OkAtt rd c nU tlD q → q.2 = some v → rd q.1 = some (g, h) →
    K5OkAt c g.zk h v.F := fun _ v g h H => H.k5 v g h

theorem okA_fuFirst (u : HTailF2) (ψ : S → β) :
    ∀ q l t b y, Fx9 (phiAll u ψ) (OkAtt rd c nU tlD) q t → FullAt nU t →
    atS.get? t = some b → fsFirst rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuFirst_full u ψ (OkAtt rd c nU tlD) nU rd c fun _ l h hl =>
    core_ents (okA_core rd c nU tlD) h (h.entsFirst l hl)

theorem okA_fuSecond (u : HTailF2) (ψ : S → β) :
    ∀ q l t b y, Fx9 (phiAll u ψ) (OkAtt rd c nU tlD) q t → FullAt nU t →
    atS.get? t = some b → fsSecond rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuSecond_full u ψ (OkAtt rd c nU tlD) nU rd c fun _ l h hl =>
    core_ents (okA_core rd c nU tlD) h (h.entsSecond l hl)

/-- Lean's own check: the five are `AttTake`'s fields. -/
example {L : Link S Claim} {u : HTailF2} {ψ : S → β} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ (OkAtt rd c nU tlD) (FullAt nU) rd c nU entUnit tm4 t3 l3) : True :=
  have _ := oneText A.okK5 (okA_k5 rd c nU tlD)
  have _ := oneText A.okEq (core_okEq (okA_core rd c nU tlD))
  have _ := oneText A.fuEq (core_fuEq (okA_core rd c nU tlD) u ψ)
  have _ := oneText A.fuFirst (okA_fuFirst rd c nU tlD u ψ)
  oneText A.fuSecond (okA_fuSecond rd c nU tlD u ψ)

end Attention

section HeadLink
variable (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par) (kap : Phi β → Option Seen)
  (nU : Array ℕ) (tlD : HTailF2)

theorem okH_core : ∀ q : Q β, OkHead h iU3 p kap nU tlD q → OkCore nU tlD q := fun _ H => H.core

theorem okH_k6 : K6Promise h iU3 p kap (OkHead h iU3 p kap nU tlD) := fun _ z u H => H.k6 z u

theorem okH_join : JoinPromise kap (OkHead h iU3 p kap nU tlD) := fun _ z u g H => H.join z u g

theorem okH_merge : ∀ (q : Q β) wo v, OkHead h iU3 p kap nU tlD q → q.1.wo = some wo →
    q.2 = some v → Sized v.F ∧ ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList,
      K4Values.InWin (winOf wo.p) x.1 ∨ Filled v.F x.1 := fun _ wo v H => H.merge wo v

theorem okH_fuK6 (u : HTailF2) (ψ : S → β) :
    ∀ name ∈ ["norm", "policy", "logits"], ∀ q l t b y,
    Fx9 (phiAll u ψ) (OkHead h iU3 p kap nU tlD) q t → FullAt nU t → atS.get? t = some b →
    fsK6 h iU3 p kap name q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuK6_full u ψ (OkHead h iU3 p kap nU tlD) nU h iU3 p kap fun name hn _ l H hl =>
    core_ents (okH_core h iU3 p kap nU tlD) H (H.entsK6 name hn l hl)

theorem okH_fuJoin (u : HTailF2) (ψ : S → β) :
    ∀ q l t b y, Fx9 (phiAll u ψ) (OkHead h iU3 p kap nU tlD) q t → FullAt nU t →
    atS.get? t = some b → fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuJoin_full u ψ (OkHead h iU3 p kap nU tlD) nU h iU3 p kap fun _ l H hl =>
    core_ents (okH_core h iU3 p kap nU tlD) H (H.entsJoin l hl)

theorem okH_fuMerge (u : HTailF2) (ψ : S → β) :
    ∀ q wo t b y, Fx9 (phiAll u ψ) (OkHead h iU3 p kap nU tlD) q t → FullAt nU t →
    atS.get? t = some b → q.1.wo = some wo → ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fuMerge_full u ψ (OkHead h iU3 p kap nU tlD) nU fun _ wo H hw x hx =>
    core_ents (okH_core h iU3 p kap nU tlD) H (H.entsMerge wo hw) _ List.mem_cons_self x hx

/-- Lean's own check: the eight are `HeadTake`'s fields. -/
example {L : Link S Claim} {u : HTailF2} {ψ : S → β} {l piece : ℕ}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ (OkHead h iU3 p kap nU tlD) (FullAt nU) h iU3 l piece p kap nU entUnit tm4
      t3 l3) : True :=
  have _ := oneText A.okK6 (okH_k6 h iU3 p kap nU tlD)
  have _ := oneText A.okJoin (okH_join h iU3 p kap nU tlD)
  have _ := oneText A.okEq (core_okEq (okH_core h iU3 p kap nU tlD))
  have _ := oneText A.okMerge (okH_merge h iU3 p kap nU tlD)
  have _ := oneText A.fuEq (core_fuEq (okH_core h iU3 p kap nU tlD) u ψ)
  have _ := oneText A.fuK6 (okH_fuK6 h iU3 p kap nU tlD u ψ)
  have _ := oneText A.fuJoin (okH_fuJoin h iU3 p kap nU tlD u ψ)
  oneText A.fuMerge (okH_fuMerge h iU3 p kap nU tlD u ψ)

end HeadLink

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.oneText
#print axioms VerifiableInference.Desc.LinkJoin.core_k8
#print axioms VerifiableInference.Desc.LinkJoin.core_ents
#print axioms VerifiableInference.Desc.LinkJoin.core_okEq
#print axioms VerifiableInference.Desc.LinkJoin.core_fuEq
#print axioms VerifiableInference.Desc.LinkJoin.core_hOk4
#print axioms VerifiableInference.Desc.LinkJoin.core_okDig
#print axioms VerifiableInference.Desc.LinkJoin.core_okEnts
#print axioms VerifiableInference.Desc.LinkJoin.snap_there_of_part
#print axioms VerifiableInference.Desc.LinkJoin.okL_core
#print axioms VerifiableInference.Desc.LinkJoin.okL_front
#print axioms VerifiableInference.Desc.LinkJoin.okL_back
#print axioms VerifiableInference.Desc.LinkJoin.okL_fuFront
#print axioms VerifiableInference.Desc.LinkJoin.okL_fuBack
#print axioms VerifiableInference.Desc.LinkJoin.okA_core
#print axioms VerifiableInference.Desc.LinkJoin.okA_k5
#print axioms VerifiableInference.Desc.LinkJoin.okA_fuFirst
#print axioms VerifiableInference.Desc.LinkJoin.okA_fuSecond
#print axioms VerifiableInference.Desc.LinkJoin.okH_core
#print axioms VerifiableInference.Desc.LinkJoin.okH_k6
#print axioms VerifiableInference.Desc.LinkJoin.okH_join
#print axioms VerifiableInference.Desc.LinkJoin.okH_merge
#print axioms VerifiableInference.Desc.LinkJoin.okH_fuK6
#print axioms VerifiableInference.Desc.LinkJoin.okH_fuJoin
#print axioms VerifiableInference.Desc.LinkJoin.okH_fuMerge
