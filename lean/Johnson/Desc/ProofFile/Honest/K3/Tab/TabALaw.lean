-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabALaw.lean: a reader of the keys and bits of an attention
group's lookup that makes the factors of the two long sums once, in the base field, and lifts each
call's key once; and that it is the seated reader. Definitions with code, and theorems without a
hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: the seated reader is the field `attention` of
`ownSources` (Honest/K3/WitOwner.lean); F is the base field `Cb.Gl.F`, E the extension field
`Cb.Gl.E`; the lift is `algebraMap F E`.

What is defined.
  `ownAF`: `ownA` without the lift: the seated reading of a name, in F.
  `attnTab X g C`: the reader. In front of the structure that it returns are bound: the shape, the
    forest's shape, the two readings, the five tables of Honest/K3/Tab/TabA.lean at the reading in
    F, and the rows off them. A key is `jointKey` of the calls' vectors `kvABy` in F, lifted. The
    bits are the seated reader's.
  `tabSourcesA`, `sourcesAtTabA`, `tabWitA`: `ownSourcesBound`, `sourcesAtBound` and `boundWit`
    (Honest/K3/WitBound.lean) with the field `attention` laid anew.

What is shown.
  `ownA_lift`: the seated reading is the reading in F, lifted.
  `kvA_own`: a call's key at the seated reading is the lift of the call's key at the reading in F:
    by `kvA_map` (Johnson/HonestTrace/CountsAttentionMap.lean).
  `attnTab_eq`: **`attnTab X g C` is the seated reader at g and C.**
  `tabSourcesA_eq`, `sourcesAtTabA_eq`, `tabWitA_eq`: so `tabWitA` is `boundWit`, at every site.

Imported. Honest/K3/Tab/TabA.lean; Honest/K3/Tab/RingG.lean, for `atOwnF`; Honest/K3/WitBound.lean;
Johnson/HonestTrace/CountsAttentionMap.lean.

Users. Honest/K3/Tab/KeyAtInt.lean [not in this library], Honest/K3/Tab/TabALawToy.lean
[not in this library] and Honest/K3/Tab/TabAll.lean import this file. Meant for one reader that lays
all fields off tables.

Limits. Equations of terms: how long either side takes is not said here. The layers', the head's and
the digits' readers are the seated ones.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabA
import Johnson.Desc.ProofFile.Honest.K3.Tab.RingG
import Johnson.Desc.ProofFile.Honest.K3.WitBound
import Johnson.HonestTrace.CountsAttentionMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabA
open OnBytes.Model OnBytes.Ends OnBytes.Ends.A
open OnBytes.HonestTrace (fsAt)
open OnBytes.Road (Hd.shapeA)
open ProofFile.Honest.K3.TabG (atOwnF)

/-- `ownA` without the lift. -/
def ownAF (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (link : ℕ) :
    NameA → Cb.Gl.F := fun n => atOwnF X cell link n.M n.r n.c

/-- **The seated reading is the reading in the base field, lifted.** -/
theorem ownA_lift (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link : ℕ) :
    ownA X cell link = fun n => algebraMap Cb.Gl.F Cb.Gl.E (ownAF X cell link n) := by
  funext n
  show atOwn X cell link n.M n.r n.c = algebraMap Cb.Gl.F Cb.Gl.E (atOwnF X cell link n.M n.r n.c)
  unfold atOwn atOwnF
  cases (tlOf X link).mats[n.M]? with
  | none => exact (map_zero _).symm
  | some M => rfl

/-- A call's key at the seated reading is the lift of the call's key at the reading in the base
field. -/
theorem kvA_own (X : OnBytes.Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (link : ℕ) (S : Sh) (h : Forest.Shape) (q x : ℕ) :
    kvA S h (ownA X cell link) q x =
      algebraMap Cb.Gl.F Cb.Gl.E (kvA S h (ownAF X cell link) q x) := by
  rw [ownA_lift]
  exact OnBytes.HonestTrace.kvA_map (algebraMap Cb.Gl.F Cb.Gl.E) S h (ownAF X cell link) q x

/-- **The reader of an attention group's keys and bits that makes the tables once.** -/
def attnTab (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) : LookIn :=
  let S := Hd.shapeA X g
  let h := fsAt X g
  let cE := ownA X C.cell (linkA X g)
  let cF := ownAF X C.cell (linkA X g)
  let tq := qTab S cF
  let tk := kTab S cF
  let tv := vTab S cF
  let wm := wTab S cF false
  let wd := wTab S cF true
  let I := innerTabA S cF tq tk tv wm wd
  ⟨fun theta n =>
      jointKey h (fun q x => algebraMap Cb.Gl.F Cb.Gl.E (kvABy S cF I h q x)) theta n,
   fun u j => bitsA S h cE (u * 32 + j)⟩

variable {W₀ Rc Xi Tr : Type}

/-- **It is the seated reader.** -/
theorem attnTab_eq (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (g : ℕ) (C : Cells) :
    attnTab X g C = (ownSourcesBound X cells weights pubH).attention g C := by
  have hk : (fun q x => algebraMap Cb.Gl.F Cb.Gl.E
      (kvABy (Hd.shapeA X g) (ownAF X C.cell (linkA X g))
        (innerTabA (Hd.shapeA X g) (ownAF X C.cell (linkA X g))
          (qTab (Hd.shapeA X g) (ownAF X C.cell (linkA X g)))
          (kTab (Hd.shapeA X g) (ownAF X C.cell (linkA X g)))
          (vTab (Hd.shapeA X g) (ownAF X C.cell (linkA X g)))
          (wTab (Hd.shapeA X g) (ownAF X C.cell (linkA X g)) false)
          (wTab (Hd.shapeA X g) (ownAF X C.cell (linkA X g)) true)) (fsAt X g) q x)) =
      kvA (Hd.shapeA X g) (fsAt X g) (ownA X C.cell (linkA X g)) := by
    funext q x
    rw [kvABy_tab, ← kvA_own]
  unfold attnTab
  simp only [hk]
  rfl

/-- `ownSourcesBound` with the field `attention` off tables. -/
def tabSourcesA (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr :=
  { ownSourcesBound X cells weights pubH with attention := attnTab X }

theorem tabSourcesA_eq (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    tabSourcesA X cells weights pubH = ownSourcesBound X cells weights pubH := by
  have h : attnTab X = (ownSourcesBound X cells weights pubH).attention := by
    funext g C
    exact attnTab_eq X cells weights pubH g C
  unfold tabSourcesA
  rw [h]

/-- `sourcesAtBound` over it. -/
def sourcesAtTabA (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  tabSourcesA Z.p.X cells weights fun x =>
    let q := req x
    headPub Z.p.X q.1 q.2

theorem sourcesAtTabA_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    sourcesAtTabA cells weights req Z = sourcesAtBound cells weights req Z :=
  tabSourcesA_eq Z.p.X cells weights _

/-- `boundWit` over it: the reader of the input at a site, attention's calls off tables. -/
def tabWitA (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtTabA cells weights req Z)).wit s

/-- **It is `boundWit`, at every site.** -/
theorem tabWitA_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    tabWitA (Rc := Rc) cells weights req Z s = boundWit cells weights req Z s := by
  unfold tabWitA boundWit
  rw [sourcesAtTabA_eq]
  rfl

end ProofFile.Honest.K3.TabA

#print axioms ProofFile.Honest.K3.TabA.ownA_lift
#print axioms ProofFile.Honest.K3.TabA.kvA_own
#print axioms ProofFile.Honest.K3.TabA.attnTab_eq
#print axioms ProofFile.Honest.K3.TabA.tabSourcesA_eq
#print axioms ProofFile.Honest.K3.TabA.sourcesAtTabA_eq
#print axioms ProofFile.Honest.K3.TabA.tabWitA_eq
