-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfMasks.lean: two fields (`fresh`, `freshB`) of `Blk.Hyp`, a record of hypotheses of
`Spec.ldWf` (Cb/Ld/LdWf.lean), derived from a record of conditions (`MaskLay.OK`) and one further
premise.
Under the hypotheses of its statement (`Spec.ldWfM_hyp`), the two hypotheses on masks of the
preamble of weights-formedness are derived from one layout of the sender's coins and conditions on
coordinates.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Ld/LdWf.lean asks, for each masked block (the lookups 0 .. n, then the batching of tensor rows),
`B.Fr`: there is a wide reading of the witness, of which the block's own reading is a function, such
that (1) given all that the one sending shows, the block's own masks are still uniform and
independent of the rest of the wide reading (exactly: `Honest.Fresh`, Ior/KnowCollRulesMask.lean);
(2) no lookup before the block looks at them. Under `Y.OK` (for data `Y : B.MaskLay`, below) and
`B.D.Nn.Hides (P.S.budT B.t)`, here both are derived.

`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. Here it is
a premise of `Spec.ldWfM_fresh`, `Spec.ldWfM_fr` and `Spec.ldWfM_hyp`, at `B.D.Nn`
(`Sig.Sender.Nn : Hiop.Enc ..`, Cb/Ld/LdSendFam.lean) and `P.S.budT B.t` (`Sig.budT`, the same
file).

Main names:
  `B.Bk`, `B.MkOf b`, `B.KcOf b`, `B.kcOf b`, `B.putOf b`, `B.upTo b`: the masked blocks (a lookup,
    or the batching), each with the parameters of its item "masked messages" and the number of
    lookups that come before it.
  `wfWide Rd w`: the wide reading, one for all blocks: the entries in Rd of all messages (all others
    0), and the whole further witness. No encoding randomness of the messages sent. Meant: Rd = all
    entries but the pads.
  `B.MaskLay`: the data: `L`: the sender's coins that go into the messages (`B.D.Mk`; not the
    encoding randomness) laid out once (Cb/Ld/LdSendFreshMany.lean: every coming block's masks,
    further coins, pads); for each masked block b: which block of the layout it is (`bk`), how its
    type of masks is that block's (`ve`: a bijection); `Rd`; the places of its masks (`at'`), how a
    mask value is a vector of entries (`val`), how its own reading is computed from the wide one
    (`g`).
  `Y.OK`: the conditions. `pad`: at every seed the law of all answers over the pads alone does not
    depend on anything else. `inj`, `inRd`: a block's places are different entries, in Rd. `own`:
    the entry at place i of block b is the value i of b's masks. `off`: an entry in Rd off b's
    places reads neither b's masks nor the pads. `rd`, `com`: the block's own reading is g of the
    wide one, and g commutes with the overwriting (`wfPut`). `blind`: (2) itself, for the wide
    reading.
  `Spec.ldWfM_fresh`: (1), for every block: from `pad`, `inj`, `inRd`, `own`, `off` and "the
    encodings hide" (`B.D.Nn.Hides (P.S.budT B.t)`).
  `Spec.ldWfM_blind`: one way to (2): a lookup does not look at masks at the places at', for the
    wide reading, if its run (transcript, explicit part) is the same for two witnesses with the same
    further witness whose messages agree at all entries in Rd off these places, and it hands the
    witness on.
  `Spec.ldWfM_fr`: under `Y.OK` and `B.D.Nn.Hides (P.S.budT B.t)`:
    `B.Fr (B.upTo b) (B.kcOf b) (B.MkOf b) (B.putOf b)` for every block b.
  `Spec.ldWfM_hyp`: under the same two: the two fields `fresh`, `freshB` of `B.Hyp`, word for word.
Another way to (2), for the lookup of this tree: Cb/Ld/LdLkpAsm2Fmt.lean (`ldLkpFmt2_blindIdx`; at
`LkAsm`: `ldLkpFmt_blindIdx`, Cb/Ld/LdLkpFormatBlindIdx.lean) gives `Blind` for every reading that
changes no entry in the set which the lookup reads (exactly: the last premise in its statement,
which speaks of all pairs of witnesses whose readings by kc differ by the overwriting:
`kc w' = put m (kc w)`), from an item on the assembled lookup; taken in Cb/Ld/LdWfMasksLkp.lean.

Limits: this file does not say that a layout with `Y.OK` exists for given lookups.
Cb/Ld/LdWfMasksStd.lean, Cb/Ld/LdWfMasksLkp.lean, Cb/Ld/LdWfMasksAll.lean bring `Y.OK` down to
conditions on places, on the sender's layout and on the lookups' chains. This file says nothing on
the other fields of `B.Hyp`, but that its further premise is the field `hides`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWf
import Cb.Ld.LdBatSig
import Cb.Ld.LdSendFreshManyProofs
import Cb.Req1.LdSegCarryKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

section
variable {E : Type} [Field E]

/-- The wide reading. -/
def wfWide {S : Sig E} {Wp : Type} (Rd : S.Ent → Prop) (w : S.Wit × Wp) :
    (S.Ent → E) × Wp :=
  (cutTo Rd (S.ents (S.msgs w.1)), w.2)

/-- the entries at the places at' overwritten -/
def wfPut {J I Mk Wp : Type} (at' : I → J) (v : Mk → I → E)
    (M : Mk) (k : (J → E) × Wp) : (J → E) × Wp :=
  (Function.extend at' (v M) k.1, k.2)

end

namespace LdWfP.Blk
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

/-- the masked blocks: the lookups, and the batching -/
abbrev Bk (_ : P.Blk) : Type := Option (Fin (P.n + 1))

variable (B : P.Blk)

def MkOf : B.Bk → Type
  | some l => (B.Dm l).Mk
  | none => B.DmB.Mk
instance finMkOf : ∀ b, Fintype (B.MkOf b)
  | some l => (B.Dm l).finMk
  | none => B.DmB.finMk
instance neMkOf : ∀ b, Nonempty (B.MkOf b)
  | some l => (B.Dm l).neMk
  | none => B.DmB.neMk
def KcOf : B.Bk → Type
  | some l => (B.Dm l).Kc
  | none => B.DmB.Kc
def kcOf : ∀ b, P.W → B.KcOf b
  | some l => (B.Dm l).kc
  | none => B.DmB.kc
def putOf : ∀ b, B.MkOf b → B.KcOf b → B.KcOf b
  | some l => (B.Dm l).put
  | none => B.DmB.put
/-- how many lookups come before the block -/
def upTo : B.Bk → ℕ
  | some l => l
  | none => P.n + 1

/-- The data. -/
structure MaskLay : Type 1 where
  L  : B.D.Layout
  bk : B.Bk → L.Bk
  ve : ∀ b, B.MkOf b ≃ L.Mk (bk b)
  Rd : P.S.Ent → Prop
  I  : B.Bk → Type
  at' : ∀ b, I b → P.S.Ent
  val : ∀ b, L.Mk (bk b) → I b → E
  g   : ∀ b, (P.S.Ent → E) × P.Wp → B.KcOf b

variable {B}

/-- a mask value of the block b, as a vector of entries -/
def MaskLay.vl (Y : B.MaskLay) (b : B.Bk) (M : B.MkOf b) : Y.I b → E := Y.val b (Y.ve b M)

/-- The conditions. -/
structure MaskLay.OK (Y : B.MaskLay) : Prop where
  pad  : Y.L.PadLaw P.Sd
  inj  : ∀ b, Function.Injective (Y.at' b)
  inRd : ∀ b i, Y.Rd (Y.at' b i)
  own  : ∀ b w ms f η i,
    P.S.ents (B.D.upM (B.D.put w (Y.L.mk' ms f η))) (Y.at' b i) = Y.val b (ms (Y.bk b)) i
  off  : ∀ b w ms ms' f η η' n, Y.L.oth (Y.bk b) ms = Y.L.oth (Y.bk b) ms' →
    Y.Rd n → (∀ i, n ≠ Y.at' b i) →
    P.S.ents (B.D.upM (B.D.put w (Y.L.mk' ms f η))) n =
      P.S.ents (B.D.upM (B.D.put w (Y.L.mk' ms' f η'))) n
  rd   : ∀ b w, B.kcOf b w = Y.g b (wfWide Y.Rd w)
  com  : ∀ b M k, Y.g b (wfPut (Y.at' b) (Y.vl b) M k) = B.putOf b M (Y.g b k)
  blind : ∀ b j, j < B.upTo b →
    (B.sub j).H.Blind (wfWide Y.Rd) (wfWide Y.Rd) (B.MkOf b)
      (wfPut (Y.at' b) (Y.vl b)) (wfPut (Y.at' b) (Y.vl b))

end LdWfP.Blk

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- (1) Under the hypotheses below, given all that the sending shows, every block's masks are fresh,
for the wide reading. -/
def ldWfM_fresh : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Y : B.MaskLay), Y.OK → B.D.Nn.Hides (P.S.budT B.t) →
    ∀ b, (ldSendFamHon P.Sd P.WSt C.E0 B.D).Fresh P.A0.rel
      (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t).bud (wfWide Y.Rd)
      (B.MkOf b) (wfPut (Y.at' b) (Y.vl b))

/-- One way to (2): a lookup whose run reads, of the messages, only entries in Rd off the places
at', and that hands the witness on, does not look at masks at these places, for the wide reading. -/
def ldWfM_blind : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Rd : P.S.Ent → Prop) (I Mk : Type) (at' : I → P.S.Ent)
      (val : Mk → I → E) (j : ℕ),
    (∀ (w w' : P.W) x c ρ,
      (∀ n, Rd n → (∀ i, n ≠ at' i) → P.S.ents (P.S.msgs w'.1) n = P.S.ents (P.S.msgs w.1) n) →
      w'.2 = w.2 →
      (((B.sub j).H.strat w' x c).run ρ).1 = (((B.sub j).H.strat w x c).run ρ).1 ∧
      (((B.sub j).H.strat w' x c).run ρ).2.1 = (((B.sub j).H.strat w x c).run ρ).2.1) →
    (∀ w x c ρ, (((B.sub j).H.strat w x c).run ρ).2.2 = w) →
    (B.sub j).H.Blind (wfWide Rd) (wfWide Rd) Mk (wfPut at' val) (wfPut at' val)

def ldWfM_fr : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Y : B.MaskLay),
    Y.OK → B.D.Nn.Hides (P.S.budT B.t) → ∀ b, B.Fr (B.upTo b) (B.kcOf b) (B.MkOf b) (B.putOf b)

/-- The fields `fresh` and `freshB` of `B.Hyp`. -/
def ldWfM_hyp : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (Y : B.MaskLay), Y.OK → B.D.Nn.Hides (P.S.budT B.t) →
    (∀ l, l ≤ P.n → B.Fr l (B.Dm l).kc (B.Dm l).Mk (B.Dm l).put) ∧
    B.Fr (P.n + 1) B.DmB.kc B.DmB.Mk B.DmB.put

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfM_fresh : Spec.ldWfM_fresh E := by
  intro C P B Y h hH b
  have l1 := layout_laws_entries (E := E) P.S (P.Body × P.Wp) P.Wp B.D Y.L P.Sd (Y.bk b)
    P.S.Ent (Y.I b) (fun m _ => P.S.ents m) Y.Rd (Y.at' b) (Y.val b) h.pad (h.inj b)
    (h.inRd b) (h.own b) (h.off b)
  have l2 := own_laws_keep (E := E) P.S (P.Body × P.Wp) P.Wp B.D (Y.L.Mk (Y.bk b))
    (Y.L.own (Y.bk b)) P.Sd _ _ _ l1
  have l3 := layout_fresh (E := E) P.S P.Sd P.WSt (P.Body × P.Wp)
    P.Wp C.E0 B.D B.t P.A0.rel Y.L hH (Y.bk b) _ _ _ l2
  exact fresh_maskEquiv _ _ _ _ _ _ _ _ _ _ _ _ (Y.L.Mk (Y.bk b)) (B.MkOf b) (Y.ve b).symm _ l3

theorem ldWfM_blind : Spec.ldWfM_blind E := by
  intro C P B Rd I Mk at' val j hlook hhand w w' M x c ρ hk
  have h1 : cutTo Rd (P.S.ents (P.S.msgs w'.1)) =
      Function.extend at' (val M) (cutTo Rd (P.S.ents (P.S.msgs w.1))) :=
    (Prod.mk.inj hk).1
  have h2 : w'.2 = w.2 := (Prod.mk.inj hk).2
  have al : ∀ n,
      Rd n → (∀ i, n ≠ at' i) → P.S.ents (P.S.msgs w'.1) n = P.S.ents (P.S.msgs w.1) n := by
    intro n hR hn
    have e := congrFun h1 n
    rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hn i hi.symm)] at e
    unfold cutTo at e
    rw [if_pos hR, if_pos hR] at e
    exact e
  obtain ⟨t1, t2⟩ := hlook w w' x c ρ al h2
  refine ⟨t1, t2, ?_⟩
  rw [hhand, hhand]
  exact hk

theorem ldWfM_fr : Spec.ldWfM_fr E := fun C P B Y h hH b =>
  ⟨_, wfWide Y.Rd, wfPut (Y.at' b) (Y.vl b), Y.g b, h.rd b, h.com b,
    ldWfM_fresh C P B Y h hH b, h.blind b⟩

theorem ldWfM_hyp : Spec.ldWfM_hyp E := fun C P B Y h hH =>
  ⟨fun l hl => ldWfM_fr C P B Y h hH (some ⟨l, Nat.lt_succ_of_le hl⟩), ldWfM_fr C P B Y h hH none⟩

end
end Cb
