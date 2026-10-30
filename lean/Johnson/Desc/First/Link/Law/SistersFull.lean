-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SistersFull.lean: THE SEVEN FIELDS "ON Fu" OF THE THREE SORTS' TAKES
THAT SPEAK OF THE ENTRIES WHICH A RUN's FORMS NAME (PayLayers.lean: fuFront, fuBack;
PayAttention.lean: fuFirst, fuSecond; PayHead.lean: fuK6, fuJoin, fuMerge), AT `Fu := FullAt nU`
(GoodFull.lean) AND `ent := entUnit` (EntryUnit.lean), EACH FROM ONE CLAUSE ON WHAT IS FIXED BEFORE
THE DRAW. Definitions and theorems.
Why. The one term that ended there (`ent_of_tests`, OkTests.lean) has the premise
"shape": the array's kind and number of rows AT THE FULL STATE's ledger, over all full states that
go on from q: by a reading it is empty. Since "goes on" carries the arrays' looks, these
two are the snapshot's.
  `TableAt nU tl sh t`: the array t is one of the first three vectors, with a length other than 0;
    another than the digits', the planes', the symbols' and the pieces'; and by the looks sh of the
    kind "table", with one row and a virtual row. `EntAt π nU q x`: the entry x stands at virtual
    row 0 of such an array, at the fixed structure and the snapshot's looks.
  `unit_full`: **at a full state that goes on from q such an array's first virtual row is a unit**
    (`UnitAt`): by `unitAt_full`, unturned, with `shape_at` (LooksAre.lean) and
    `goesOn_looks`. `sisters_full`: **for whatever entries a kind names: the entry in the world at
    that state is `entUnit q y`.** `ent_full`: the same at `phiAll u ψ` and `pi8`.
  `fuFront_full`, `fuBack_full`, `fuFirst_full`, `fuSecond_full`, `fuK6_full`, `fuJoin_full`,
    `fuMerge_full`: **the seven fields in their own text**, each under: every entry that the run's
    forms name has `EntAt`. Behind each an `example`: Lean's own check that the end is the Take's
    field.
  `tableAt_of_static`: at vector 2 `TableAt` follows from `StaticOk` (OkJoin.lean), where that
    vector is there and has a length other than 0.
Limits. Implications. THAT A RUN's FORMS NAME ENTRIES OF THAT SORT ALONE IS SHOWN OF NO RUN HERE AND
HAS NO MEMBER HERE: it is a sentence on what each kind's forms are at q. `EntAt` also asks that q's
structure and snapshot are there. OkOne.lean makes both named clauses of Ok, the first as the test
`entsAtB` (EntAtTests.lean). Ok's lower bound is owed elsewhere (`hready`). Nothing on soundness.


-/
import Johnson.Desc.First.Link.Law.OkTests
import Johnson.Desc.First.Link.Law.OkJoin
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (uOf)
open VerifiableInference.Desc.K4Values (backForms frontForms)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.EntryUnit (UnitAt entUnit entry_fixed)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

/-! ## 1 A table's vector, by the fixed structure and the snapshot's looks -/

/-- **The array t is a table's vector, apart from the other sorts, and looks it.** In full: t is one
of the FIRST THREE of the structure's four vectors, and that vector's planned length in nU is not 0;
t is another array than the digits', the planes', the symbols' and the pieces'; and by the looks sh
it is of the kind "table", with EXACTLY ONE row (`unitLook` asks R = 1) and at least one virtual
row.
Why three here, and four in `fuEq_full` (FullEq.lean): the self test behind `FullAt nU`
(`selfTestF`, OnBytes/Model/Tail.lean) tests "the weight is not 0" at the first three vectors alone,
below nU's lengths: so only there does its yes give a unit row. `fuEq_full`'s clause says only that
the arrays are apart, which holds of all four. -/
def TableAt (nU : Array ℕ) (tl : HTailF2) (sh : List Look) (t : ℕ) : Prop :=
  (∃ n0, n0 < 3 ∧ 0 < nU.getD n0 0 ∧ tl.ix.U.getD n0 none = some t) ∧ tl.ix.ZZ ≠ t ∧
    tl.ix.BZ ≠ t ∧ (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ t) ∧
    (∀ k p, p ∈ (tl.zOf k).pieces.toList → p.tree ≠ t) ∧ unitLook sh t = true

/-- At vector 2 it follows from the static clauses. -/
theorem tableAt_of_static {nU : Array ℕ} {tl : HTailF2} {F : Fork} (H : StaticOk tl F) {i : ℕ}
    (hU : tl.ix.U.getD 2 none = some i) (h0 : 0 < nU.getD 2 0) :
    TableAt nU tl (F.trees.toList.map look) i := by
  have e : uOf tl { tree := 2 } = i := by
    unfold uOf
    rw [hU]
    rfl
  obtain ⟨_, _, _, a3, a4, a5, a6⟩ := H.apart { tree := 2 } (Or.inr rfl)
  rw [e] at a3 a4 a5 a6
  exact ⟨⟨2, by decide, h0, hU⟩, a3, a4, a5, a6, e ▸ H.units { tree := 2 }⟩

section
variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun))

/-- **The entry stands at virtual row 0 of such an array.** -/
def EntAt (nU : Array ℕ) (q : α × Option Pub9) (x : Ent) : Prop :=
  x.row = 0 ∧ ∃ tlb v, (π q.1).1 = some tlb ∧ q.2 = some v ∧
    TableAt nU tlb (v.F.trees.toList.map look) x.tree

variable (φ : S → α) (Ok : α × Option Pub9 → Prop) (nU : Array ℕ) (u : HTailF2)
  (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
include hπ

/-- **AT A FULL STATE THAT GOES ON FROM q SUCH AN ARRAY's FIRST VIRTUAL ROW IS A UNIT.** -/
theorem unit_full (q : α × Option Pub9) (t : S) (b : K9.Part) (tlb : HTailF2) (v : Pub9)
    (hf : Fx9 φ Ok q t) (hfull : FullAt nU t) (hb : atS.get? t = some b)
    (h1 : (π q.1).1 = some tlb) (hv : q.2 = some v) (k : ℕ)
    (hT : TableAt nU tlb (v.F.trees.toList.map look) k) : UnitAt b.F k 0 := by
  obtain ⟨_, hφ, v', b', hv', hb', hgo⟩ := hf
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have e1 : t.tl?.map (blank u) = some tlb := by
    have k1 := congrArg Prod.fst (hπ t)
    rw [hφ] at k1
    exact k1.symm.trans h1
  obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.1 e1
  obtain ⟨⟨n0, hn, h0, hU⟩, hZ, hB, hS, hP, hL⟩ := hT
  have hl : LooksAre (v.F.trees.toList.map look) b'.F := by
    have k2 := congrArg Array.toList (goesOn_looks hgo)
    simpa [LooksAre] using k2
  obtain ⟨_, hk, hR⟩ := shape_at hl k hL
  exact unitAt_full nU t b' ts hfull hb hts n0 k hn h0 hU hZ hB hS hP hk
    (by rw [hR]; exact Nat.one_pos)

/-- **THE SEVEN SISTERS' COMMON END.** Named: which entries a kind names at q. The premise okNamed:
under Ok q every such entry has `EntAt`. Then, at every full state that goes on from q, the world's
value at a named entry is `entUnit q y`'s. -/
theorem sisters_full (Named : α × Option Pub9 → Ent → Prop)
    (okNamed : ∀ q x, Ok q → Named q x → EntAt π nU q x) :
    ∀ q t b y, Fx9 φ Ok q t → FullAt nU t → atS.get? t = some b → ∀ x, Named q x →
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        entUnit q y x.tree x.row x.idx := by
  intro q t b y hf hfull hb x hx
  obtain ⟨hr, tlb, v, h1, hv, hT⟩ := okNamed q x hf.1 hx
  refine entry_fixed Reading.gl φ Ok q t b y hf hb x.tree x.row x.idx ?_
  rw [hr]
  exact unit_full π φ Ok nU u hπ q t b tlb v hf hfull hb h1 hv x.tree hT

end

/-! ## 2 The seven fields -/

variable {β : Type}

/-- The common end at the closed φ, an entry at a time. -/
theorem ent_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ) (q : Q β) (t : S)
    (b : K9.Part) (y : Bound GE8) (hf : Fx9 (phiAll u ψ) Ok q t) (hfull : FullAt nU t)
    (hb : atS.get? t = some b) (x : Ent) (hx : EntAt pi8 nU q x) :
    (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  sisters_full pi8 (phiAll u ψ) Ok nU u (fun _ => rfl) (fun q x => EntAt pi8 nU q x)
    (fun _ _ _ h => h) q t b y hf hfull hb x hx

/-- **fuFront, at `FullAt nU` and `entUnit`.** -/
theorem fuFront_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ) (p : Par)
    (ok : ∀ q o v, Ok q → q.1.own = some o → q.2 = some v →
      ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        EntAt pi8 nU q x) :
    ∀ q o v t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.own = some o → q.2 = some v → ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l →
    ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q o v t b y hf hfu hb ho hv l hl f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q o v hf.1 ho hv l hl f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ) (L : Link S Claim) (p : Par)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : LayersTake L u ψ Ok (FullAt nU) p nU entUnit tm4 t3 l3) :
    ∀ q o v t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.own = some o → q.2 = some v → ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l →
    ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuFront

/-- **fuBack, at `FullAt nU` and `entUnit`.** -/
theorem fuBack_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (ok : ∀ q o, Ok q → q.1.own = some o → ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      EntAt pi8 nU q x) :
    ∀ q o t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.own = some o → ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q o t b y hf hfu hb ho f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q o hf.1 ho f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ) (L : Link S Claim) (p : Par)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : LayersTake L u ψ Ok (FullAt nU) p nU entUnit tm4 t3 l3) :
    ∀ q o t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.own = some o → ∀ f ∈ backForms o, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuBack

/-- **fuFirst, at `FullAt nU` and `entUnit`.** -/
theorem fuFirst_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (ok : ∀ q l, Ok q → fsFirst rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt pi8 nU q x) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsFirst rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q l t b y hf hfu hb hl f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q l hf.1 hl f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (L : Link S Claim) (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : AttTake L u ψ Ok (FullAt nU) rd c nU entUnit tm4 t3 l3) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsFirst rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuFirst

/-- **fuSecond, at `FullAt nU` and `entUnit`.** -/
theorem fuSecond_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (ok : ∀ q l, Ok q → fsSecond rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt pi8 nU q x) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsSecond rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q l t b y hf hfu hb hl f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q l hf.1 hl f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (L : Link S Claim) (rd : Phi β → Option (Forest.Heard × Heard)) (c : ParC)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : AttTake L u ψ Ok (FullAt nU) rd c nU entUnit tm4 t3 l3) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsSecond rd c q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuSecond

/-- **fuK6, at `FullAt nU` and `entUnit`.** -/
theorem fuK6_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par) (kap : Phi β → Option Seen)
    (ok : ∀ name ∈ ["norm", "policy", "logits"], ∀ q l, Ok q → fsK6 h iU3 p kap name q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList, EntAt pi8 nU q x) :
    ∀ name ∈ ["norm", "policy", "logits"], ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t →
    atS.get? t = some b → fsK6 h iU3 p kap name q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun name hn q l t b y hf hfu hb hl f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok name hn q l hf.1 hl f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (L : Link S Claim) (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : HeadTake L u ψ Ok (FullAt nU) h iU3 l piece p kap nU entUnit tm4 t3 l3) :
    ∀ name ∈ ["norm", "policy", "logits"], ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t →
    atS.get? t = some b → fsK6 h iU3 p kap name q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuK6

/-- **fuJoin, at `FullAt nU` and `entUnit`.** -/
theorem fuJoin_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par) (kap : Phi β → Option Seen)
    (ok : ∀ q l, Ok q → fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      EntAt pi8 nU q x) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q l t b y hf hfu hb hl f hm x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q l hf.1 hl f hm x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (L : Link S Claim) (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : HeadTake L u ψ Ok (FullAt nU) h iU3 l piece p kap nU entUnit tm4 t3 l3) :
    ∀ q l t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    fsJoin h iU3 p kap q = some l → ∀ f ∈ l, ∀ x ∈ f.ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuJoin

/-- **fuMerge, at `FullAt nU` and `entUnit`.** -/
theorem fuMerge_full (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (ok : ∀ q wo, Ok q → q.1.wo = some wo → ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
      EntAt pi8 nU q x) :
    ∀ q wo t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.wo = some wo → ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  fun q wo t b y hf hfu hb hw x hx =>
    ent_full u ψ Ok nU q t b y hf hfu hb x (ok q wo hf.1 hw x hx)

/-- Lean's own check that this is the Take's field. -/
example (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (L : Link S Claim) (h : OnBytes.Model.Head.Shape) (iU3 l piece : ℕ) (p : Kinds.Head.Par)
    (kap : Phi β → Option Seen)
    (tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (A : HeadTake L u ψ Ok (FullAt nU) h iU3 l piece p kap nU entUnit tm4 t3 l3) :
    ∀ q wo t b y, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
    q.1.wo = some wo → ∀ x ∈ (wo.p.rowForm wo.fvp {}).ents.toList,
      (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx :=
  A.fuMerge

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tableAt_of_static
#print axioms VerifiableInference.Desc.LinkJoin.unit_full
#print axioms VerifiableInference.Desc.LinkJoin.sisters_full
#print axioms VerifiableInference.Desc.LinkJoin.fuFront_full
#print axioms VerifiableInference.Desc.LinkJoin.fuBack_full
#print axioms VerifiableInference.Desc.LinkJoin.fuFirst_full
#print axioms VerifiableInference.Desc.LinkJoin.fuSecond_full
#print axioms VerifiableInference.Desc.LinkJoin.fuK6_full
#print axioms VerifiableInference.Desc.LinkJoin.fuJoin_full
#print axioms VerifiableInference.Desc.LinkJoin.fuMerge_full
