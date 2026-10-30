-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfMasksStd.lean: two fields (`fresh`, `freshB`) of `Blk.Hyp`, a record of hypotheses of
`Spec.ldWf` (Cb/Ld/LdWf.lean), derived from a record of conditions (`Places.OK`) and one further
premise.
`Spec.ldWfMS_hyp`: under the hypotheses of its statement, the hypotheses on masks of the preamble of
weights-formedness follow from one named condition on places.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Ld/LdWfMasks.lean: `B.Hyp.fresh`, `freshB` follow from `Y.OK` and `B.D.Nn.Hides (P.S.budT B.t)`,
for data `Y : B.MaskLay`. Cb/Ld/LdWfMasksBatt.lean: a block that reads entries of (matrix of the
index, named entries) has its reading as a function of the wide reading, if the named entries are
entries of the messages (`P.EntAt nAt`) and every named entry in RdJ lies in Rd. Here Y is defined
from places (`Q.Y`), and `Y.OK` a theorem, under `Q.OK`.

`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. Here it is
a premise of `Spec.ldWfMS_hyp`, at `B.D.Nn` (`Sig.Sender.Nn : Hiop.Enc ..`, Cb/Ld/LdSendFam.lean)
and `P.S.budT B.t` (`Sig.budT`, the same file).

Main names:
  `B.Places`: the data. `nAt`: where the named entries (`P.N`) are among the entries of the
    messages; `Rd`: the entries that the wide reading shows (meant: all but the pads); `L`, `bk`,
    `ve`: the layout of the sender's coins, which of its blocks a masked block is, the bijection of
    the two types of masks; for each masked block b: the set `RdJ b` of entries of (matrix, named
    entries) that it reads; its mask places `atN b` among the named entries; `val`: a mask value as
    a vector of entries; `dec b`: the map from such tuples of entries into the block's type of
    readings.
  `Q.OK`: the named condition. `ent`: the named entries are entries, at different places. On the
    sender: `pad`, `own`, `off` (Cb/Ld/LdSendFreshMany.lean's conditions; for the standard family:
    Cb/Ld/LdSendToyFamLay.lean). On places: `inj` (a block's places differ), `inRd` (they are shown
    by the wide reading), `rdJ` (so is every named entry that a block reads), `ownJ` (a block reads
    its own masks). On the blocks' parameters (letters): `kc` (the block reads `wfCutJ (RdJ b)`,
    through dec b), `put` (its overwriting is the overwriting at the named entries atN b, through
    dec b). `blind`: every lookup before b does not look at b's masks, for the wide reading.
  `Spec.ldWfMS_ok`: `Q.OK` ⇒ `Q.Y.OK`. `Spec.ldWfMS_hyp`: so, with "the encodings hide"
    (`B.D.Nn.Hides (P.S.budT B.t)`), the two fields `fresh`, `freshB` of `B.Hyp`.
  `Spec.ldWfMS_batt`: for the batching the two conditions on letters hold by definition at dec :=
    the identity, RdJ := `B.Rd`, atN := `P.wAt`, a mask value its own vector.
  `Spec.ldWfMS_same`: under `P.EntAt nAt`: the step to "blind": if the wide readings of w' and w
    differ by an overwriting at the places nAt (atN i), then the tuples `P.msg` (prover's index
    message, messages) of w' and w agree at every entry of a set Sr all of whose named entries are
    shown by the wide reading and are none of the atN i. For the lookups `K.sub j`:
    `Spec.ldWfML_blind`, Cb/Ld/LdWfMasksLkp.lean.

Limits: this file does not say that the two conditions on letters hold for the lookups, or that
"blind" holds: Cb/Ld/LdWfMasksLkp.lean. It does not say that `Q.OK` can be met: at a toy,
Cb/Ld/LdWfToyMasks.lean with Cb/Ld/LdWfToyItem.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfMasksBatt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace LdWfP.Blk
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (B : P.Blk)

/-- The data. -/
structure Places : Type 1 where
  nAt : P.N → P.S.Ent
  Rd  : P.S.Ent → Prop
  L   : B.D.Layout
  bk  : B.Bk → L.Bk
  ve  : ∀ b, B.MkOf b ≃ L.Mk (bk b)
  I   : B.Bk → Type
  atN : ∀ b, I b → P.N
  val : ∀ b, L.Mk (bk b) → I b → E
  RdJ : B.Bk → P.bt.J → Prop
  dec : ∀ b, (P.bt.J → E) → B.KcOf b

variable {B}

/-- the data of Cb/Ld/LdWfMasks.lean -/
@[reducible] def Places.Y (Q : B.Places) : B.MaskLay :=
  ⟨Q.L, Q.bk, Q.ve, Q.Rd, Q.I, fun b i => Q.nAt (Q.atN b i), Q.val,
    fun b k => Q.dec b (wfG (Q.RdJ b) Q.nAt k)⟩

/-- The named condition. -/
structure Places.OK (Q : B.Places) : Prop where
  ent  : P.EntAt Q.nAt
  pad  : Q.L.PadLaw P.Sd
  own  : ∀ b w ms f η i,
    P.S.ents (B.D.upM (B.D.put w (Q.L.mk' ms f η))) (Q.nAt (Q.atN b i)) = Q.val b (ms (Q.bk b)) i
  off  : ∀ b w ms ms' f η η' n, Q.L.oth (Q.bk b) ms = Q.L.oth (Q.bk b) ms' →
    Q.Rd n → (∀ i, n ≠ Q.nAt (Q.atN b i)) →
    P.S.ents (B.D.upM (B.D.put w (Q.L.mk' ms f η))) n =
      P.S.ents (B.D.upM (B.D.put w (Q.L.mk' ms' f η'))) n
  inj  : ∀ b, Function.Injective (Q.atN b)
  inRd : ∀ b i, Q.Rd (Q.nAt (Q.atN b i))
  rdJ  : ∀ b n, Q.RdJ b (Sum.inr n) → Q.Rd (Q.nAt n)
  ownJ : ∀ b i, Q.RdJ b (Sum.inr (Q.atN b i))
  kc   : ∀ b w, B.kcOf b w = Q.dec b (wfCutJ (Q.RdJ b) w)
  put  : ∀ b M k, B.putOf b M (Q.dec b k) =
    Q.dec b (Function.extend (fun i => (Sum.inr (Q.atN b i) : P.bt.J)) (Q.val b (Q.ve b M)) k)
  blind : ∀ b j, j < B.upTo b →
    (B.sub j).H.Blind (wfWide Q.Rd) (wfWide Q.Rd) (B.MkOf b)
      (wfPut (fun i => Q.nAt (Q.atN b i)) (Q.Y.vl b))
      (wfPut (fun i => Q.nAt (Q.atN b i)) (Q.Y.vl b))

end LdWfP.Blk

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldWfMS_ok : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Q : B.Places), Q.OK → Q.Y.OK

/-- The fields `fresh` and `freshB` of `B.Hyp` from the named condition.
(not all hypotheses are named here: see the statement below) -/
def ldWfMS_hyp : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Q : B.Places), Q.OK → B.D.Nn.Hides (P.S.budT B.t) →
    (∀ l, l ≤ P.n → B.Fr l (B.Dm l).kc (B.Dm l).Mk (B.Dm l).put) ∧
    B.Fr (P.n + 1) B.DmB.kc B.DmB.Mk B.DmB.put

/-- For the batching the two conditions on letters hold by definition. -/
def ldWfMS_batt : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk),
    (∀ w, B.kcOf none w = wfCutJ B.Rd w) ∧
    ∀ (M : B.MkOf none) (k : P.bt.J → E),
      B.putOf none M k = Function.extend (fun i => (Sum.inr (P.wAt i) : P.bt.J)) M k

/-- Under the hypotheses below, wide readings that differ by an overwriting: the tuples agree at the
entries of Sr. -/
def ldWfMS_same : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (nAt : P.N → P.S.Ent) (Rd : P.S.Ent → Prop) (I Mk : Type)
      (atN : I → P.N) (v : Mk → I → E) (Sr : P.bt.J → Prop),
    P.EntAt nAt → (∀ n, Sr (Sum.inr n) → Rd (nAt n) ∧ ∀ i, n ≠ atN i) →
    ∀ (w w' : P.W) (M : Mk), wfWide Rd w' = wfPut (fun i => nAt (atN i)) v M (wfWide Rd w) →
      ∀ j, Sr j → P.msg (w'.2.1.1.1, P.S.msgs w'.1) j = P.msg (w.2.1.1.1, P.S.msgs w.1) j

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfMS_same : Spec.ldWfMS_same E := by
  classical
  intro C P nAt Rd I Mk atN v Sr hE hS w w' M hk j hj
  have h1 : cutTo Rd (P.S.ents (P.S.msgs w'.1)) =
      Function.extend (fun i => nAt (atN i)) (v M) (cutTo Rd (P.S.ents (P.S.msgs w.1))) :=
    (Prod.mk.inj hk).1
  have h2 : w'.2 = w.2 := (Prod.mk.inj hk).2
  cases j with
  | inl a =>
      show P.mat w'.2.1.1.1 a = P.mat w.2.1.1.1 a
      rw [h2]
  | inr n =>
      obtain ⟨hR, hn⟩ := hS n hj
      show P.ent (P.S.msgs w'.1) n = P.ent (P.S.msgs w.1) n
      rw [hE.ent, hE.ent]
      have e := congrFun h1 (nAt n)
      rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hn i (hE.inj hi).symm)] at e
      unfold cutTo at e
      rw [if_pos hR, if_pos hR] at e
      exact e

theorem ldWfMS_ok : Spec.ldWfMS_ok E := fun C P B Q h =>
  { pad := h.pad
    inj := fun b i i' e => h.inj b (h.ent.inj e)
    inRd := h.inRd
    own := h.own
    off := h.off
    rd := fun b w => by
      rw [h.kc b w, ldWfMB_rdG C P (Q.RdJ b) Q.nAt Q.Rd h.ent (h.rdJ b) w]
    com := fun b M k => by
      rw [h.put b M]
      exact congrArg (Q.dec b)
        (ldWfMB_comG C P (Q.RdJ b) Q.nAt (Q.I b) (Q.atN b) h.ent (h.inj b)
          (h.ownJ b) (Q.val b (Q.ve b M)) k)
    blind := h.blind }

theorem ldWfMS_hyp : Spec.ldWfMS_hyp E := fun C P B Q h hH =>
  ldWfM_hyp C P B Q.Y (ldWfMS_ok C P B Q h) hH

theorem ldWfMS_batt : Spec.ldWfMS_batt E := fun _ _ _ => ⟨fun _ => rfl, fun _ _ => rfl⟩

end
end Cb
