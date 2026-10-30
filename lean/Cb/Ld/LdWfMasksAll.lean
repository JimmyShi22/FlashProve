-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfMasksAll.lean: two fields (`fresh`, `freshB`) of `Blk.Hyp`, the record of hypotheses on
the blocks of `Spec.ldWf` (Cb/Ld/LdWf.lean), at the lookups `K.sub l`, derived from one record of
conditions and one further premise.
Under the hypotheses of its statement (`Spec.ldWfMA_hyp`), the two hypotheses on masks of the
preamble of weights-formedness, with the lookups as values, follow from one named condition on
places, on the sender's layout and on the lookups' chains.

Definitions, statements (in `Cb.Spec`) and proofs. An assembly.

Main names:
  `K.blk ..`: the blocks: any sender; the lookups `K.sub l` with the parameters `K.dm Rl Cc l`
    (Cb/Ld/LdWfMasksLkp.lean); the batching reading RdB.
  `K.MaskPl D Rl`: the data: `nAt` (where the named entries are among the entries of the messages);
    `RdW` (what the wide reading shows: meant: all but the pads); `L` (the one layout of the
    sender's coins), `bk` (which of its blocks a masked block is), `eL l`, `eB` (a block's masks in
    the layout as vectors over the places of lookup l, of the batching); `atL l` (the places of
    lookup l's own masks, as named entries).
  `X.I b`, `X.pa b`, `X.vl b`, `X.rd b`: for a masked block b (a lookup, or the batching): its index
    set of places, the places, a mask value as a vector, the set of entries that it reads.
  `X.Q ..`: the data of Cb/Ld/LdWfMasksStd.lean, as one value.
  `X.OK ..`: the named condition.
    places: `ent`: the named entries are entries, at different places. `inRd`: every mask place is
    shown by the wide reading (no pad). `rdJ`: so is every named entry that a block reads. `atEq`:
    the places of lookup l's own masks are the named entries atL l. `ownL`: lookup l reads them.
    `ownB`: the batching's own condition on places.
    `apart`: a named entry that the messages of lookup j read (Sr j) is shown by the wide reading
      and is no mask place of a later block.
    sender: `pad`, `own`, `off`: Cb/Ld/LdSendFreshMany.lean's conditions on the one layout (for the
    standard family: Cb/Ld/LdSendToyFamLay.lean).
    lookups: `plOK`: to put the own masks of lookup l is to overwrite the entries at its places
    (Cb/Ld/LdLkpMaskPutLkp2.lean, from conditions on places). `link`: the chain of lookup j, started
    with Cc j, is a link whose messages read Sr j (`Spec.ldLkpMaskAsm2_link`,
    Cb/Ld/LdLkpMaskAsm2.lean, under its hypotheses). `srRd`, `ccRd`: Sr j lies in Rl j; Cc j reads
    Sr j only.
  `Spec.ldWfMA_places`: a consequence of "own" alone: mask places of two masked blocks that are
    different blocks of the layout are different entries (in both directions, earlier or later): one
    entry cannot be a coordinate of two independent parts of the coins.
  `Spec.ldWfMA_ok`: `X.OK` ⇒ `(X.Q ..).OK`. `Spec.ldWfMA_hyp`: under `X.OK ..`, with "the encodings
    hide": the two fields `fresh`, `freshB` of `B.Hyp` at these blocks.

Limits: this is what "apart" does and does not cover. Covered, at Sr j := the data and the own masks
of lookup j: no mask place of a later block is among the data (keys' entries, bits) or the own masks
of an earlier lookup; as any two masked blocks are ordered and the earlier one is a lookup, own
masks of different blocks never meet. `X.OK` does not force Sr j to hold the own masks of lookup j.
Not covered: that an own mask of an earlier lookup is not among the data of a later one.
`Spec.ldWfMA_hyp` is proved without such a clause: the two hypotheses on masks do not need it.
Not proved here: that the other hypotheses of the preamble exclude it (data are functions of the
index by the sender's law "back"; a mask entry is a coin by "own"). That no mask place is a played
bit place (`K.bAt f u j`, f ≤ `P.n`, u < 2 ^ `P.d f`, j < 2 ^ `K.w f`) is neither stated nor proved
in this library.
This file does not say that `X.OK` can be met.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfMasksLkp
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP.Lks
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks)

/-- The blocks. -/
@[reducible] def blk (D : P.S.Sender (P.Body × P.Wp) P.Wp) (Ll t : P.S.O → ℕ)
    (Rl : ℕ → P.bt.J → Prop) (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (RdB : P.bt.J → Prop)
    (p0 : C.PIdx) (r0 : P.S.Rnd) : P.Blk :=
  ⟨D, Ll, t, K.sub, K.dm Rl Cc, RdB, p0, r0⟩

/-- The data. -/
structure MaskPl (D : P.S.Sender (P.Body × P.Wp) P.Wp) (Rl : ℕ → P.bt.J → Prop) : Type 1 where
  nAt : P.N → P.S.Ent
  RdW : P.S.Ent → Prop
  L   : D.Layout
  bk  : Option (Fin (P.n + 1)) → L.Bk
  eL  : ∀ l : Fin (P.n + 1), L.Mk (bk (some l)) ≃ ((K.pl Rl l).I → E)
  eB  : L.Mk (bk none) ≃ (PIdx P.bt.fmt → E)
  atL : ∀ l : Fin (P.n + 1), (K.pl Rl l).I → P.N

namespace MaskPl
variable {K} {D : P.S.Sender (P.Body × P.Wp) P.Wp} {Rl : ℕ → P.bt.J → Prop}

def I (_ : K.MaskPl D Rl) : Option (Fin (P.n + 1)) → Type
  | some l => (K.pl Rl l).I
  | none => PIdx P.bt.fmt

variable (X : K.MaskPl D Rl)

def pa : ∀ b, X.I b → P.N
  | some l => X.atL l
  | none => P.wAt
def vl : ∀ b, X.L.Mk (X.bk b) → X.I b → E
  | some l => X.eL l
  | none => X.eB
def rd (_ : K.MaskPl D Rl) (RdB : P.bt.J → Prop) : Option (Fin (P.n + 1)) → P.bt.J → Prop
  | some l => Rl l
  | none => RdB

variable (Ll t : P.S.O → ℕ)
  (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (RdB : P.bt.J → Prop) (p0 : C.PIdx) (r0 : P.S.Rnd)

def ve : ∀ b, (K.blk D Ll t Rl Cc RdB p0 r0).MkOf b ≃ X.L.Mk (X.bk b)
  | some l => (K.pl Rl l).ve.trans (X.eL l).symm
  | none => X.eB.symm
def dec (_ : K.MaskPl D Rl) : ∀ b, (P.bt.J → E) → (K.blk D Ll t Rl Cc RdB p0 r0).KcOf b
  | some _ => fun k => k
  | none => fun k => k

/-- The data of Cb/Ld/LdWfMasksStd.lean, as one value. -/
@[reducible] def Q : (K.blk D Ll t Rl Cc RdB p0 r0).Places :=
  ⟨X.nAt, X.RdW, X.L, X.bk, X.ve Ll t Cc RdB p0 r0, X.I, X.pa, X.vl,
    X.rd RdB, X.dec Ll t Cc RdB p0 r0⟩

/-- The named condition. -/
structure OK (Sr Sw : ℕ → P.bt.J → Prop) : Prop where
  ent   : P.EntAt X.nAt
  inRd  : ∀ b i, X.RdW (X.nAt (X.pa b i))
  rdJ   : ∀ b n, X.rd RdB b (Sum.inr n) → X.RdW (X.nAt n)
  atEq  : ∀ (l : Fin (P.n + 1)) i, (K.pl Rl l).pl i = (Sum.inr (X.atL l i) : P.bt.J)
  ownL  : ∀ (l : Fin (P.n + 1)) i, Rl l (Sum.inr (X.atL l i))
  ownB  : P.bt.OwnOK RdB
  apart : ∀ b j, j < (K.blk D Ll t Rl Cc RdB p0 r0).upTo b →
    ∀ n, Sr j (Sum.inr n) → X.RdW (X.nAt n) ∧ ∀ i, n ≠ X.pa b i
  pad   : X.L.PadLaw P.Sd
  own   : ∀ b w ms f η i,
    P.S.ents (D.upM (D.put w (X.L.mk' ms f η))) (X.nAt (X.pa b i)) = X.vl b (ms (X.bk b)) i
  off   : ∀ b w ms ms' f η η' n, X.L.oth (X.bk b) ms = X.L.oth (X.bk b) ms' → X.RdW n →
    (∀ i, n ≠ X.nAt (X.pa b i)) →
    P.S.ents (D.upM (D.put w (X.L.mk' ms f η))) n = P.S.ents (D.upM (D.put w (X.L.mk' ms' f η'))) n
  plOK  : ∀ l : Fin (P.n + 1), (K.pl Rl l).OK
  link  : ∀ j, j ≤ P.n →
    (K.dc Rl j).Link ((K.asm j).chainA C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg).H
      (fun w => mjCut (Rl j) (P.msg w.1)) (fun w => mjCut (Rl j) (P.msg w.1)) (Sr j) (Sw j) (Cc j)
  srRd  : ∀ j, j ≤ P.n → ∀ a, Sr j a → Rl j a
  ccRd  : ∀ j, j ≤ P.n → ∀ k k' st, (∀ a, Sr j a → k a = k' a) → Cc j st k → Cc j st k'

end MaskPl
end LdWfP.Lks

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- Under the hypothesis below (the clause `own` of `X.OK`), mask places of different blocks of the
layout are different entries. -/
def ldWfMA_places : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (D : P.S.Sender (P.Body × P.Wp) P.Wp)
      (Rl : ℕ → P.bt.J → Prop) (X : K.MaskPl D Rl),
    (∀ b w ms f η i,
      P.S.ents (D.upM (D.put w (X.L.mk' ms f η))) (X.nAt (X.pa b i)) = X.vl b (ms (X.bk b)) i) →
    ∀ b b', X.bk b ≠ X.bk b' → ∀ i i', X.nAt (X.pa b i) ≠ X.nAt (X.pa b' i')

def ldWfMA_ok : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (D : P.S.Sender (P.Body × P.Wp) P.Wp)
      (Rl : ℕ → P.bt.J → Prop) (X : K.MaskPl D Rl) (Ll t : P.S.O → ℕ)
      (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (RdB : P.bt.J → Prop) (p0 : C.PIdx)
      (r0 : P.S.Rnd) (Sr Sw : ℕ → P.bt.J → Prop),
    X.OK Ll t Cc RdB p0 r0 Sr Sw → (X.Q Ll t Cc RdB p0 r0).OK

/-- The fields `fresh` and `freshB` of `B.Hyp`, at the blocks `K.blk ..`. -/
def ldWfMA_hyp : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (D : P.S.Sender (P.Body × P.Wp) P.Wp)
      (Rl : ℕ → P.bt.J → Prop) (X : K.MaskPl D Rl) (Ll t : P.S.O → ℕ)
      (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (RdB : P.bt.J → Prop) (p0 : C.PIdx)
      (r0 : P.S.Rnd) (Sr Sw : ℕ → P.bt.J → Prop),
    X.OK Ll t Cc RdB p0 r0 Sr Sw → D.Nn.Hides (P.S.budT t) →
    (∀ l, l ≤ P.n →
      (K.blk D Ll t Rl Cc RdB p0 r0).Fr l (K.dm Rl Cc l).kc (K.dm Rl Cc l).Mk (K.dm Rl Cc l).put) ∧
    (K.blk D Ll t Rl Cc RdB p0 r0).Fr (P.n + 1) (K.blk D Ll t Rl Cc RdB p0 r0).DmB.kc
      (K.blk D Ll t Rl Cc RdB p0 r0).DmB.Mk (K.blk D Ll t Rl Cc RdB p0 r0).DmB.put

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfMA_places : Spec.ldWfMA_places E := by
  intro C P K D Rl X hown b b' hb i i' e
  have hs : ∀ (b : Option (Fin (P.n + 1))) (v : X.I b → E), ∃ M, X.vl b M = v := fun b v => by
    cases b with
    | some l => exact ⟨(X.eL l).symm v, Equiv.apply_symm_apply _ _⟩
    | none => exact ⟨X.eB.symm v, Equiv.apply_symm_apply _ _⟩
  let ms₀ : ∀ c, X.L.Mk c := fun _ => Classical.arbitrary _
  obtain ⟨M', hM'⟩ := hs b fun _ => X.vl b' (ms₀ (X.bk b')) i' + 1
  have h1 :=
    hown b D.w0 (Function.update ms₀ (X.bk b) M') (Classical.arbitrary _) (Classical.arbitrary _) i
  have h2 := hown b' D.w0 (Function.update ms₀ (X.bk b) M') (Classical.arbitrary _)
    (Classical.arbitrary _) i'
  rw [Function.update_self, hM'] at h1
  rw [Function.update_of_ne (Ne.symm hb), ← e, h1] at h2
  exact one_ne_zero (add_eq_left.mp h2)

theorem ldWfMA_ok : Spec.ldWfMA_ok E := by
  intro C P K D Rl X Ll t Cc RdB p0 r0 Sr Sw h
  have hjn : ∀ (b : Option (Fin (P.n + 1))) j,
      j < (K.blk D Ll t Rl Cc RdB p0 r0).upTo b → j ≤ P.n := fun b j hj => by
    cases b with
    | some l => exact Nat.le_of_lt_succ (Nat.lt_trans hj l.2)
    | none => exact Nat.le_of_lt_succ hj
  refine
    { ent := h.ent, pad := h.pad, own := h.own, off := h.off, inRd := h.inRd, rdJ := h.rdJ
      inj := fun b => ?_, ownJ := fun b i => ?_, kc := fun b w => ?_, put := fun b M k => ?_
      blind := fun b j hj =>
        ldWfML_blind C P K Rl Cc j (Sr j) (Sw j) X.nAt X.RdW (X.I b) _ (X.pa b) _
          (h.link j (hjn b j hj)) (h.srRd j (hjn b j hj)) (h.ccRd j (hjn b j hj))
          h.ent (h.apart b j hj) }
  · cases b with
    | some l => exact (ldWfML_put C P K Rl Cc l (X.atL l) (h.plOK l) (h.atEq l)).1
    | none => exact fun i i' e => h.ownB.inj (congrArg Sum.inr e)
  · cases b with
    | some l => exact h.ownL l i
    | none => exact h.ownB.own i
  · cases b with
    | some l => rfl
    | none => rfl
  · cases b with
    | some l =>
        have e := (ldWfML_put C P K Rl Cc l (X.atL l) (h.plOK l) (h.atEq l)).2 M k
        have e2 : X.eL l ((X.eL l).symm ((K.pl Rl l).ve M)) = (K.pl Rl l).ve M :=
          Equiv.apply_symm_apply _ _
        show (K.dm Rl Cc l).put M k =
          Function.extend (fun i => (Sum.inr (X.atL l i) : P.bt.J))
            (X.eL l ((X.eL l).symm ((K.pl Rl l).ve M))) k
        rw [e2]
        exact e
    | none =>
        have e2 : X.eB (X.eB.symm M) = M := Equiv.apply_symm_apply _ _
        show Function.extend P.bt.wAt M k =
          Function.extend (fun i => (Sum.inr (P.wAt i) : P.bt.J)) (X.eB (X.eB.symm M)) k
        rw [e2]
        rfl

theorem ldWfMA_hyp : Spec.ldWfMA_hyp E := fun C P K D Rl X Ll t Cc RdB p0 r0 Sr Sw h hH =>
  ldWfMS_hyp C P (K.blk D Ll t Rl Cc RdB p0 r0) (X.Q Ll t Cc RdB p0 r0)
    (ldWfMA_ok C P K D Rl X Ll t Cc RdB p0 r0 Sr Sw h) hH

end
end Cb
