-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/BatchObj.lean: the item on knowledge soundness of the test at N instances, from a
typed list of batch blocks; and an object all of whose five sub-protocols are typed lists.

Definitions, statements and proofs.

Main names:
  `KObj.admOf`, `KObj.adm_of_hands`: "the statements of a batch agree on what ρ reads off them" is
    carried by a block that hands both parts on (`BK.Hands`, Johnson/E/KObj/Blocks.lean), under any
    annotation.
  `KObj.BB.good_ofHands`: so a plain block with its property that hands them on is a batch block
    with its property, in local rounds.
  `KObj.LB.snoc`, `KObj.LB.fam`: a list grows at its end; a family of blocks in a row.
  `KObj.linB_of_list`: for every configuration C, every S : C.Left and every N: if every block of a
    list from "what a preamble leaves; the statements of a batch share the encoded index and its
    record" to the trivial statement has its property, then `LinBKnowR` (Hiop/RecSubs.lean) holds
    of the list's batch IOP, at the list's errors. By `ldObj_linB_know`
    (Cb/Obj/LdObjectBatch.lean).
  `KObj.ObjB`, `KObj.ObjB.obj`, `KObj.ObjB.blocks`: the object with five lists; it is an object of
    Johnson/E/KObj/Obj.lean; every block of the five lists gives that object's hypotheses.
Limits: nothing is said of any value, of completeness or of zero knowledge.
-/
import Johnson.E.KObj.Batch
import Johnson.E.KObj.Obj
import Cb.Obj.LdObjectBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop IOR Cb

variable {N : ℕ}

/-! ### (H1) what a batch's statements share -/

/-- the statements of a batch agree on what ρ reads off them -/
def admOf {T U : Type} {A : JK} (ρ : Rd T U A) : (Fin N → Option (A.X × A.E.Str)) → Prop :=
  SameKey fun x => (ρ.ix x.2, ρ.rc x.1)

theorem adm_of_hands {T U : Type} {A B : JK} (b : BK A B) (ρ : Rd T U A) (σ : Rd T U B)
    (h : b.Hands ρ σ) (ann : RoundSplits b.R.shape) :
    ∀ a, admOf (N := N) ρ a → ∀ τ : BTr N b.R.shape ann,
      admOf σ fun j => (a j).bind fun aj => b.R.red.out aj (τ.slot j) := by
  intro a ha τ j j' bj bj' e1 e2
  obtain ⟨aj, h1, h2⟩ := Option.bind_eq_some_iff.1 e1
  obtain ⟨aj', h1', h2'⟩ := Option.bind_eq_some_iff.1 e2
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h2'
  have k := ha j j' aj aj' h1 h1'
  show (σ.ix (b.R.imp aj.2 _), σ.rc x) = (σ.ix (b.R.imp aj'.2 _), σ.rc x')
  rw [h.copy, h.copy, h.passes _ _ _ _ hx, h.passes _ _ _ _ hx']
  exact k

/-- a plain block with its property, which hands ρ's parts on: a batch block with its property, in
local rounds, at the same errors -/
theorem BB.good_ofHands {T U : Type} {A B : JK} (b : BK A B) (d : A.W) (ρ : Rd T U A) (σ : Rd T U B)
    (h : b.Good) (hh : b.Hands ρ σ) : (BB.ofLocal (N := N) b d (admOf ρ) (admOf σ)).Good :=
  BB.good_ofLocal b d _ _ h (adm_of_hands b ρ σ hh _)

/-! ### (H2) a list grows at its end -/

namespace LB

/-- every block has its whole property -/
def EachG : {A B : JB N} → LB A B → Prop
  | _, _, .one x => x.Good
  | _, _, .cons x l => x.Good ∧ l.EachG

def snoc : {A B C : JB N} → LB A B → BB B C → LB A C
  | _, _, _, .one x, y => .cons x (.one y)
  | _, _, _, .cons x l, y => .cons x (l.snoc y)

theorem each_snoc {A B C : JB N} (l : LB A B) (y : BB B C) : l.EachG → y.GoodC → (l.snoc y).Each :=
    by
  induction l with
  | one x =>
    intro h hy
    rw [LB.EachG] at h
    rw [LB.snoc, LB.each_cons, LB.each_one]
    exact ⟨h, hy⟩
  | cons x l ih =>
    intro h hy
    rw [LB.EachG] at h
    rw [LB.snoc, LB.each_cons]
    exact ⟨h.1, ih y h.2 hy⟩

theorem eachG_snoc {A B C : JB N} (l : LB A B) (y : BB B C) : l.EachG → y.Good → (l.snoc y).EachG :=
    by
  induction l with
  | one x =>
    intro h hy
    rw [LB.EachG] at h
    rw [LB.snoc, LB.EachG, LB.EachG]
    exact ⟨h, hy⟩
  | cons x l ih =>
    intro h hy
    rw [LB.EachG] at h
    rw [LB.snoc, LB.EachG]
    exact ⟨h.1, ih y h.2 hy⟩

/-- the blocks x 0, …, x n in a row -/
def fam (J : ℕ → JB N) (x : ∀ i, BB (J i) (J (i + 1))) : ∀ n, LB (J 0) (J (n + 1))
  | 0 => .one (x 0)
  | n + 1 => (fam J x n).snoc (x (n + 1))

theorem eachG_fam (J : ℕ → JB N) (x : ∀ i, BB (J i) (J (i + 1))) (n : ℕ)
    (h : ∀ i ≤ n, (x i).Good) : (fam J x n).EachG := by
  induction n with
  | zero =>
    rw [fam, LB.EachG]
    exact h 0 le_rfl
  | succ n ih =>
    rw [fam]
    exact eachG_snoc _ _ (ih fun i hi => h i (Nat.le_succ_of_le hi)) (h (n + 1) le_rfl)

end LB

/-! ### the fifth sub-protocol's item -/

section
variable (C : ConfigurationWithOutOfDomainSample) (S : C.Left)

/-- where the batch test begins: what a preamble leaves; the statements of a batch share the encoded
index and its record -/
@[reducible] def jbLin : JB N := ⟨jLin C S, SameKey fun a => (a.2.1, a.1.2)⟩
/-- where it ends -/
@[reducible] def jbEnd : JB N := ⟨jEnd, fun _ => True⟩

/-- the batch IOP of a list -/
@[reducible] noncomputable def LB.biop (l : LB (jbLin (N := N) C S) jbEnd) : BIOP (S.Xl × C.Rec)
    S.El :=
  ⟨l.blk.b.R, l.blk.ann⟩

/-- If every block of the list has its property, the item holds in the form for batches. -/
theorem linB_of_list (l : LB (jbLin (N := N) C S) jbEnd) (d0 : S.AMsg) (h : l.Each) :
    LinBKnowR S (l.biop C S) N d0 l.blk.b.err :=
  ldObj_linB_know C S S.AMsg (l.biop C S) N S.cond S.RlinR l.blk.b.ext l.blk.b.err id d0
    (knowB_conseq _ _ _ _ _ _ l.blk.b.R l.blk.ann N _ _ S.cond S.cond S.RlinR S.RlinR _ _
        l.blk.b.ext
      l.blk.b.err (l.good h).know (fun _ ha => ha) (fun _ ha => ha) (fun _ _ _ hw => hw)
      (fun _ _ _ => Or.inl trivial))
    (fun _ _ hc => hc) (fun _ _ _ _ hw => hw)

end

/-- THE OBJECT AT LETTERS, ALL FIVE AS LISTS -/
structure ObjB : Type 1 where
  C      : ConfigurationWithOutOfDomainSample
  off    : C.Left
  on     : C.Left
  N      : ℕ
  wf     : LK (jWf C) (jLin C off)
  linOff : LK (jLin C off) jEnd
  link   : LK (jLink C) jEnd
  req    : LK (jReq C) (jLin C on)
  linOn  : LB (jbLin (N := N) C on) jbEnd
  dOff   : off.AMsg
  dOn    : on.AMsg

/-- … is an object -/
@[reducible] noncomputable def ObjB.obj (O : ObjB) : Obj where
  C := O.C
  off := O.off
  on := O.on
  N := O.N
  wf := O.wf
  linOff := O.linOff
  link := O.link
  req := O.req
  linOn := O.linOn.biop O.C O.on
  errOn := O.linOn.blk.b.err
  dOff := O.dOff
  dOn := O.dOn

/-- The named hypotheses: every block of the five lists has its property; the request's blocks hand
record and encoded index on -/
structure ObjB.Blocks (O : ObjB) : Prop where
  wf     : O.wf.Each PG
  linOff : O.linOff.Each PG
  link   : O.link.Each PG
  req    : O.req.Each PG
  linOn  : O.linOn.Each
  hands  : O.req.HandsL (T := O.C.Rec) (U := O.C.E0.Str) ⟨Prod.snd, id⟩ ⟨Prod.snd, Prod.fst⟩

theorem ObjB.blocks (O : ObjB) (h : O.Blocks) : O.obj.Blocks where
  wf := h.wf
  linOff := h.linOff
  link := h.link
  req := h.req
  linOn := linB_of_list O.C O.on O.linOn O.dOn h.linOn
  localOn := (O.linOn.good h.linOn).isLocal
  cohOn := (O.linOn.good h.linOn).coh
  hands := h.hands

#print axioms KObj.adm_of_hands
#print axioms KObj.BB.good_ofHands
#print axioms KObj.LB.each_snoc
#print axioms KObj.LB.eachG_fam
#print axioms KObj.linB_of_list
#print axioms KObj.ObjB.blocks

end KObj
