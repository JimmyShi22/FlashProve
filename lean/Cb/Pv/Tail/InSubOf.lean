-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/InSubOf.lean: the link of a sub-proof as a whole, with the smallness test's round and the
last block in their places, over any front.

The frame is `sub_link_of` (Cb/Pv/Att/LinkOf.lean): a front R₀ with its `KnowAt` into "the base
joint, and the ledger's pull-back to the early entries holds" (`virtJ`); the sending of the reads; a
block; the sending of the digits; a last block. Here the first block is the round of
Cb/Pv/Tail/Block.lean at the frame's own letters, and the last block is the lookup on the digits,
the laying of one ledger and the draw that batches it (Cb/Pv/Tail/DigBatch.lean).

The conditions on statements are carried. `virtJ` has a condition: the base joint's, and the ledger
in the statement has at most n claims. It stands, by `ranCond` (Cb/Pv/Att/RanCond.lean), behind the
round and in front of the lookup. Behind the lookup stands a condition P₃, a letter, on the lookup's
output statement: the premises on the ledger that is laid are asked under it alone, and it stands at
the link's end.

Main names:
  `hostAt`: the frame's letters as a `Host` (Cb/Pv/Tail/InLink.lean).
  `sub_link_tail2_of`: the round in its place: B₀ for the frame, Br for what rides through the tail;
    premise: the round's input relation, with what rides, gives B₀.
  `sub_link_batch2_of`: the last block in its place too. It ends at: Br, and the one form of the
    batched ledger holds.
  `baseAnd sym Br`: the joint "`Base` of the symbols (Cb/Pv/Tail/Base.lean), and Br".
  `sub_link_fr_batch_of`: at B₀ := `baseAnd sym Br`: the lift is made by the round's input relation,
    Br rides.

Limits: those of Cb/Pv/Att/LinkOf.lean, Cb/Pv/Tail/InLink.lean and Cb/Pv/Tail/DigBatch.lean.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Att.LinkOf
import Cb.Pv.Tail.Base
import Cb.Pv.Tail.DigBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop Prob Hiop Cb IOR TWhole Reduction Cb.Sub Cb.Pv.Att Cb.LdLkp CbQ

variable {E : Type} [Field E] [Fintype E] {J₁ J₂ J₃ : Type} [Fintype J₁] [Fintype J₂] [Fintype J₃]
  [DecidableEq J₃] {X₀ Xe : Type} {Ex : ExtSpec} {s : Size}

/-- The frame's letters as a `Host`. -/
def hostAt {K Wp Wp₁ : Type} (S₁ N₁ : Sig E) (bk₁ : N₁.Msg → Wp₁ → Wp)
    (Br : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → E) (ent : N₁.Msg → J₂ → E)
    (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → E) (sym : S₁.Msg → Syms E s)
    (tab : N₁.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → E) (dig : Wp₁ → Dig E s) :
    Host E s J₁ J₂ where
  Xe := Xe
  Ex := Ex
  M := (S₁.sum N₁).Msg
  M₁ := S₁.Msg
  U₁ := N₁.Msg
  left := S₁.left N₁ (T := OMsg.Msg)
  right := S₁.right N₁ (T := OMsg.Msg)
  Wp := Wp
  Wp₁ := Wp₁
  Kc := K
  bk₁ := bk₁
  B₀ := Br
  msg₁ := msg₁
  ent := ent
  w := w
  sym := sym
  tab := tab
  dig := dig

/-- The joint "`Base` of the symbols, and Br". -/
def baseAnd {K M₁ Wp : Type} (sym : M₁ → Syms E s) (Br : Rels K Xe Ex (M₁ × Wp)) :
    Rels K Xe Ex (M₁ × Wp) :=
  ⟨fun x y w => Base (sym w.1) ∧ Br.rel x y w, fun a w => Base (sym w.1) ∧ Br.relR a w, Br.on,
    Br.core⟩

section
variable {K X₃ Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds)
  (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp) (bk₂ : N₂.Msg → Wp₂ → Wp₁)
  (B₀ Br : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → E)
  (ent : N₁.Msg → J₂ → E) (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → E)
  (sym : S₁.Msg → Syms E s) (tab : N₁.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → E)
  (dig : Wp₁ → Dig E s)

local notation "Qa" => hostAt S₁ N₁ bk₁ Br msg₁ ent w sym tab dig

omit [Fintype E] in
/-- The round in its place, over any front. -/
theorem sub_link_tail2_of {R₀ : IOR X₀ Ex (Xe × Ledger E (J₁ ⊕ J₂)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (a : Xe → J₂ → Aff E J₁) (n : ℕ)
    (h₀ : KnowAt R₀ A (virtJ B₀ a msg₁ n) idW ε₀)
    (hs : s.OK) (p : ℕ) [CharP E p] (hu : s.Uniq p) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hcell : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (haff : ∀ (x : (Qa).let.X) j v,
      (a x.1 j).val v = (affRead (Qa).let x (it j)).val fun i => v (ic i))
    (htab : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2)
    (hbase : ∀ b m w', (Cb.Pv.Tail.A (Qa).let).relR b (m, w') →
      B₀.relR (b.1.1, b.2)
        (S₁.left N₁ (T := OMsg.Msg) m, bk₁ (S₁.right N₁ (T := OMsg.Msg) m) w'))
    (k₁ k₁' : (S₁.sum N₁).Msg × Wp₁ → K)
    {T₂ : IOR ((Xe × Ledger E (J₁ ⊕ J₂)) × Dr s) Ex X₃ Ex}
    {Rl₂ : Rels K ((Xe × Ledger E (J₁ ⊕ J₂)) × Dr s) Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)}
    {C₂ : Rels K X₃ Ex (((S₁.sum N₁).sum N₂).Msg × Wp₂)} {η₂ : Err T₂.shape}
    (hDig : KnowAt T₂ Rl₂ C₂ idW η₂)
    (ho₂ : ∀ b, (virtJ B₀ a msg₁ n).on (b.1.1, b.2) → Rl₂.on b)
    (hs₂ : ∀ b m w', Rl₂.relR b (m, w') →
      (B (Qa).let).relR b ((S₁.sum N₁).left N₂ (T := OMsg.Msg) m,
        bk₂ ((S₁.sum N₁).right N₂ (T := OMsg.Msg) m) w'))
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Qa).let) T₂).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over C₂).on (S₁.over A).relR (((S₁.sum N₁).sum N₂).over C₂).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ bk₂ R₀ (R (Qa).let) T₂ d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Qa).let) T₂ ε₀ (eps (Qa).let) η₂) :=
  sub_link_of S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ bk₁ bk₂ a msg₁ ent n B₀ h₀
    (T₁ := R (Qa).let)
    (Rl₁ := ranCond (reCore (Cb.Pv.Tail.A (Qa).let) k₁) (virtJ B₀ a msg₁ n).on)
    (C₁ := ranCond (reCore (B (Qa).let) k₁') fun b => (virtJ B₀ a msg₁ n).on (b.1.1, b.2))
    (knowAt_ranDraw (virtJ B₀ a msg₁ n).on (host_know (Qa) hs k₁ k₁')) hDig
    (fun _ h => ⟨trivial, h⟩)
    (fun b m w' hw =>
      have g := host_seam (Qa) p hu a ic it hcell haff htab k₁ b m w' hw
      ⟨hbase b m w' hw, g.2.1, g.2.2⟩)
    (fun b h => ho₂ b h.2) hs₂ d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end

section
variable {K Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds)
  (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp)
  (B₀ Br : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → E)
  (ent : N₁.Msg → J₂ → E) (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → E)
  (sym : S₁.Msg → Syms E s) (tab : N₁.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → E)
  (dig : Wp₁ → Dig E s)

local notation "Qa" => hostAt S₁ N₁ bk₁ Br msg₁ ent w sym tab dig
set_option quotPrecheck false in
local notation "lf" => (S₁.sum N₁).left N₂ (T := OMsg.Msg)
set_option quotPrecheck false in
local notation "rt" => (S₁.sum N₁).right N₂ (T := OMsg.Msg)

/-- The round and the last block in their places, over any front. -/
theorem sub_link_batch2_of {R₀ : IOR X₀ Ex (Xe × Ledger E (J₁ ⊕ J₂)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (a : Xe → J₂ → Aff E J₁) (n : ℕ)
    (h₀ : KnowAt R₀ A (virtJ B₀ a msg₁ n) idW ε₀)
    (hs : s.OK) (p : ℕ) [CharP E p] (hu : s.Uniq p) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hcell : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (haff : ∀ (x : (Qa).let.X) j v,
      (a x.1 j).val v = (affRead (Qa).let x (it j)).val fun i => v (ic i))
    (htab : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2)
    (hbase : ∀ b m w', (Cb.Pv.Tail.A (Qa).let).relR b (m, w') →
      B₀.relR (b.1.1, b.2)
        (S₁.left N₁ (T := OMsg.Msg) m, bk₁ (S₁.right N₁ (T := OMsg.Msg) m) w'))
    (k₁ k₁' : (S₁.sum N₁).Msg × Wp₁ → K)
    (T : LateU (Qa).let N₂.Msg Wp₂) {pp : ℕ} (hQ : T.Q.DatOK s.lo s.hi pp) (hr : T.Reads)
    (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    (D : Tail3 (Qa) ((S₁.sum N₁).sum N₂).Msg J₃)
    {L : IOR ((Xe × Ledger E (J₁ ⊕ J₂)) × Dr s) Ex D.X' Ex} {η : Err L.shape}
    (P₃ : D.X' × Ex.Str → Prop)
    (hL : KnowAt L (ranCond (T.inD₁ lf rt k₂) fun b => (virtJ B₀ a msg₁ n).on (b.1.1, b.2))
      (ranCond (outD T lf rt k₂ D) P₃) idW η)
    (h12 : ∀ m j, D.msg₃ m (D.i12 j) =
      Sum.elim (msg₁ (S₁.left N₁ (T := OMsg.Msg) (lf m)))
        (ent (S₁.right N₁ (T := OMsg.Msg) (lf m))) j)
    (h3 : ∀ m j, D.msg₃ m (D.is j) = vals (Qa).let (lf m) (T.digs (rt m)) j)
    (hk : ∀ (x : (Qa).let.X) (msg : (Qa).let.M) μ r, D.keep μ r = false →
      (∀ i, (Qa).let.w x μ r i = 0) ∧ ∀ c, (Qa).let.tab msg μ r c = 0)
    (lay : D.X' → Ledger E J₃) (n₃ : ℕ)
    (hn₃ : ∀ x' y, P₃ (x', y) → (lay x').length ≤ n₃)
    (hlay : ∀ x' y m, P₃ (x', y) → Ledger.Holds (lay x') (D.msg₃ m) →
      Ledger.Holds (layD D x') (D.msg₃ m))
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex))).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over (ledOutA (ranCond (baseD T lf rt k₂ D) P₃) D.msg₃)).on
      (S₁.over A).relR
      (((S₁.sum N₁).sum N₂).over (ledOutA (ranCond (baseD T lf rt k₂ D) P₃) D.msg₃)).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ T.bk R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex)) d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex))
        ε₀ (eps (Qa).let)
        (Err.app η (Nums.draw K E (ledNx (J := J₃) (P := D.X')) Ex (n₃ - 1)).err)) :=
  sub_link_tail2_of S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ bk₁ T.bk B₀ Br msg₁ ent w sym tab dig a n h₀ hs p hu ic
    it hcell haff htab hbase k₁ k₁'
    (dig_know T lf rt k₂ D (fun b => (virtJ B₀ a msg₁ n).on (b.1.1, b.2)) P₃ hL h12 h3 hk lay n₃
      hn₃ hlay)
    (fun _ h => ⟨trivial, h⟩) (seam₁ T _ _ k₂ hQ hr) d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end

section
variable {K Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds)
  (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) (bk₁ : N₁.Msg → Wp₁ → Wp)
  (Br : Rels K Xe Ex (S₁.Msg × Wp)) (msg₁ : S₁.Msg → J₁ → E)
  (ent : N₁.Msg → J₂ → E) (w : Xe → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → E)
  (sym : S₁.Msg → Syms E s) (tab : N₁.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → E)
  (dig : Wp₁ → Dig E s)

local notation "Qa" => hostAt S₁ N₁ bk₁ Br msg₁ ent w sym tab dig
set_option quotPrecheck false in
local notation "lf" => (S₁.sum N₁).left N₂ (T := OMsg.Msg)
set_option quotPrecheck false in
local notation "rt" => (S₁.sum N₁).right N₂ (T := OMsg.Msg)

/-- The same with the base joint "`Base` of the symbols, and Br"; Br rides through the tail. -/
theorem sub_link_fr_batch_of {R₀ : IOR X₀ Ex (Xe × Ledger E (J₁ ⊕ J₂)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (a : Xe → J₂ → Aff E J₁) (n : ℕ)
    (h₀ : KnowAt R₀ A (virtJ (baseAnd sym Br) a msg₁ n) idW ε₀)
    (hs : s.OK) (p : ℕ) [CharP E p] (hu : s.Uniq p) (ic : JCell s → J₁) (it : J₂ → JTab s)
    (hcell : ∀ m₁ j, msg₁ m₁ (ic j) = cellValS (sym m₁) j)
    (haff : ∀ (x : (Qa).let.X) j v,
      (a x.1 j).val v = (affRead (Qa).let x (it j)).val fun i => v (ic i))
    (htab : ∀ u j, ent u j = tab u (it j).1 (it j).2.1 (it j).2.2)
    (k₁ k₁' : (S₁.sum N₁).Msg × Wp₁ → K)
    (T : LateU (Qa).let N₂.Msg Wp₂) {pp : ℕ} (hQ : T.Q.DatOK s.lo s.hi pp) (hr : T.Reads)
    (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    (D : Tail3 (Qa) ((S₁.sum N₁).sum N₂).Msg J₃)
    {L : IOR ((Xe × Ledger E (J₁ ⊕ J₂)) × Dr s) Ex D.X' Ex} {η : Err L.shape}
    (P₃ : D.X' × Ex.Str → Prop)
    (hL : KnowAt L
      (ranCond (T.inD₁ lf rt k₂) fun b => (virtJ (baseAnd sym Br) a msg₁ n).on (b.1.1, b.2))
      (ranCond (outD T lf rt k₂ D) P₃) idW η)
    (h12 : ∀ m j, D.msg₃ m (D.i12 j) =
      Sum.elim (msg₁ (S₁.left N₁ (T := OMsg.Msg) (lf m)))
        (ent (S₁.right N₁ (T := OMsg.Msg) (lf m))) j)
    (h3 : ∀ m j, D.msg₃ m (D.is j) = vals (Qa).let (lf m) (T.digs (rt m)) j)
    (hk : ∀ (x : (Qa).let.X) (msg : (Qa).let.M) μ r, D.keep μ r = false →
      (∀ i, (Qa).let.w x μ r i = 0) ∧ ∀ c, (Qa).let.tab msg μ r c = 0)
    (lay : D.X' → Ledger E J₃) (n₃ : ℕ)
    (hn₃ : ∀ x' y, P₃ (x', y) → (lay x').length ≤ n₃)
    (hlay : ∀ x' y m, P₃ (x', y) → Ledger.Holds (lay x') (D.msg₃ m) →
      Ledger.Holds (layD D x') (D.msg₃ m))
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex))).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over (ledOutA (ranCond (baseD T lf rt k₂ D) P₃) D.msg₃)).on
      (S₁.over A).relR
      (((S₁.sum N₁).sum N₂).over (ledOutA (ranCond (baseD T lf rt k₂ D) P₃) D.msg₃)).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ T.bk R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex)) d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Qa).let)
        ((L.post (fun x' => some (x', lay x')) (ExtMap.id Ex)).seq
          (IOR.draw E (ledNx (J := J₃) (P := D.X')) Ex))
        ε₀ (eps (Qa).let)
        (Err.app η (Nums.draw K E (ledNx (J := J₃) (P := D.X')) Ex (n₃ - 1)).err)) :=
  sub_link_batch2_of S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ bk₁ (baseAnd sym Br) Br msg₁ ent w sym tab dig a n h₀
    hs p hu ic it hcell haff htab (fun _ _ _ hw => ⟨base_of_relIn (Qa).let p hu hw.2, hw.1.1⟩)
    k₁ k₁' T hQ hr k₂ D P₃ hL h12 h3 hk lay n₃ hn₃ hlay d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.sub_link_tail2_of
#print axioms Cb.Pv.Tail.sub_link_batch2_of
#print axioms Cb.Pv.Tail.sub_link_fr_batch_of
