-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRngOn.lean: the kind "the draw of the matrix of a smallness test" with a condition
on statements that is carried past the draw.

The block of Cb/Pv/Tail/Block.lean is sound at all statements, so both its joints have the condition
"true". In a row of blocks that loses what was known of the statement in front of the draw, such as
that the ledger in it has at most n claims: a seam behind the draw starts from "true", and a later
block that needs the condition cannot have it. Here the caller brings a condition `on`; it stands at
the joint before the draw, and at the joint behind it it is read off the statement's first part. The
rule is `Cb.Pv.Att.knowAt_ranDraw` (Cb/Pv/Att/RanCond.lean). Definitions, statements and proofs.

Main names:
  `TailCallerOn`: a caller of Johnson/Top/H/TailRng.lean and a condition on its statements. Data
    alone.
  `kTailRngOn L`, `tailRngOn_knowAt`, `tailRngOn_good`: the kind at a written list of callers; all
    four facts; every block of the lifted kind has `KObj.BK.Good`.
  `KTailRngOn`, `KTailRngOn_good`, `KTailRngOn_fills`: the kind as a family of blocks; where it
    stands at the family rng, that family's hypothesis holds.
  `KTailRngOn_true`: at the condition "true" the block is that of `KTailRng`: joints and block.

Limits: those of Johnson/Top/H/TailRng.lean. Nothing new on soundness: knowledge soundness on fewer
statements is less to prove. The seams beside the draw are stated in a file of their own.
-/
import Johnson.Top.H.TailRng
import Cb.Pv.Att.RanCond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att

/-- A caller of the draw, and a condition on its statements. Data alone. -/
structure TailCallerOn : Type 1 where
  c  : TailCaller
  on : c.X × c.Ex.Str → Prop

/-- The joint before the draw, and the joint behind it, with the condition. -/
@[reducible] def TailCallerOn.A (d : TailCallerOn) :
    Rels Unit d.c.X d.c.Ex (d.c.Sg.Msg × d.c.Wp) := ranCond (Cb.Pv.Tail.A d.c.letters) d.on

@[reducible] def TailCallerOn.B (d : TailCallerOn) :
    Rels Unit (d.c.X × Cb.Pv.Tail.Dr d.c.s) d.c.Ex (d.c.Sg.Msg × d.c.Wp) :=
  ranCond (Cb.Pv.Tail.B d.c.letters) fun b => d.on (b.1.1, b.2)

/-- The kind, at a written list of callers. -/
@[reducible] noncomputable def kTailRngOn (L : List TailCallerOn) : BaseKind.{1} Cb.Gl.E where
  Size := TailCallerOn
  sizes := L
  Sg := fun d => d.c.Sg
  Kc := fun _ => Unit
  St := fun d => d.c.X
  St' := fun d => d.c.X × Cb.Pv.Tail.Dr d.c.s
  Wp := fun d => d.c.Wp
  Wp' := fun d => d.c.Wp
  E₀ := fun d => d.c.Ex
  E₀' := fun d => d.c.Ex
  R := fun d => Cb.Pv.Tail.R d.c.letters
  A := fun d => d.A
  B := fun d => d.B
  ext := fun _ _ _ _ wp => wp
  ε := fun d => Cb.Pv.Tail.eps d.c.letters

/-- All four facts at once. -/
theorem tailRngOn_knowAt (L : List TailCallerOn) (h : ∀ d ∈ L, d.c.s.OK) :
    (kTailRngOn L).KnowAtAll :=
  fun d hd => knowAt_ranDraw d.on (Cb.Pv.Tail.knowAt d.c.letters (h d hd))

theorem tailRngOn_good (L : List TailCallerOn) (h : ∀ d ∈ L, d.c.s.OK) :
    ∀ d ∈ L, ((kTailRngOn L).toKind.block d).Good :=
  BaseKind.good_of_knowAt (tailRngOn_knowAt L h)

end VerifiableInference.OnPublicFiles

namespace KObj
open Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles Cb.Pv.Tail Cb.Pv.Att

/-- The draw of the matrix with a condition that is carried, whoever calls it. -/
noncomputable def KTailRngOn : KFam.{1} where
  ι := TailCallerOn
  mem := fun d => d.c.s.OK
  src := fun d => (kTailRngOn [d]).toKind.src d
  dst := fun d => (kTailRngOn [d]).toKind.dst d
  blk := fun d => (kTailRngOn [d]).toKind.block d

theorem KTailRngOn_good : KTailRngOn.Good := fun d hd =>
  tailRngOn_good [d] (fun d' h' => by rw [List.mem_singleton.1 h']; exact hd) d
    (List.mem_singleton.2 rfl)

theorem KTailRngOn_fills (K : PFam → KFam.{1}) (h : K .rng = KTailRngOn) : (K .rng).Good := by
  rw [h]
  exact KTailRngOn_good

/-- A joint with the further condition "true" is the joint. -/
theorem ranCond_true {K X W : Type} {Ex : ExtSpec} (A : Rels K X Ex W) :
    ranCond A (fun _ => True) = A := by
  obtain ⟨r, rr, o, k⟩ := A
  show (⟨r, rr, fun a => o a ∧ True, k⟩ : Rels K X Ex W) = ⟨r, rr, o, k⟩
  congr 1
  funext a
  exact propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- At the condition "true" the block is that of `KTailRng`. -/
theorem KTailRngOn_true (c : TailCaller) :
    (KTailRngOn.blk ⟨c, fun _ => True⟩).Same (KTailRng.blk c) := by
  have key : ∀ (A A' : Rels Unit c.X c.Ex (c.Sg.Msg × c.Wp))
      (B B' : Rels Unit (c.X × Dr c.s) c.Ex (c.Sg.Msg × c.Wp)), A = A' → B = B' →
      (⟨jOver c.Sg A, jOver c.Sg B, BK.ofSig c.Sg (Cb.Pv.Tail.R c.letters) A B
        (fun _ _ _ wp => wp) (Cb.Pv.Tail.eps c.letters)⟩ : Σ A B : JK, BK A B) =
      ⟨jOver c.Sg A', jOver c.Sg B', BK.ofSig c.Sg (Cb.Pv.Tail.R c.letters) A' B'
        (fun _ _ _ wp => wp) (Cb.Pv.Tail.eps c.letters)⟩ := by
    rintro A _ B _ rfl rfl
    rfl
  exact key _ _ _ _ (ranCond_true _) (ranCond_true _)

end KObj

#print axioms VerifiableInference.OnPublicFiles.tailRngOn_good
#print axioms KObj.KTailRngOn_good
#print axioms KObj.KTailRngOn_fills
#print axioms KObj.KTailRngOn_true
