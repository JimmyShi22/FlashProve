-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshMany.lean: one sending holds the masks of several coming blocks: from one layout of
the sender's coins, all the splits at once.

This file is book-keeping for those coins of an honest prover that go into its messages
(`Sig.Sender.Mk`). One prover message has the masks that several later reductions of a chain will
use; from one description of how these coins are divided, this file states when the conditions
`Own.Laws` of Cb/Ld/LdSendFresh.lean hold for each of these reductions.

Definitions and statements (Cb.Spec.*); the proofs are in Cb/Ld/LdSendFreshManyProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is the conclusion of
`Spec.layout_fresh`.
`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. Here it is
a premise of `Spec.layout_fresh` (`D.Nn.Hides (N.budT t)`: the encoding is `D.Nn`, N the family;
`Sig.budT`: Cb/Ld/LdSendFam.lean).

Cb/Ld/LdSendFresh.lean states (proved in Cb/Ld/LdSendFreshProofs.lean), for one coming block, under
the hypotheses of `Spec.ldSendFam_fresh`: after a sending the block's own masks are still uniform,
given all that the sending shows, in this sense:
`(ldSendFamHon ..).Fresh Ri (fun _ T => N.budT t ..) .. Mb put` (`Honest.Fresh`,
Ior/KnowCollRulesMask.lean), if the sender's coins split as ((own masks × other coins) × pads) with
three conditions (`Own.Laws`: over, lay, pad).
In a protocol one oracle message holds the masks of many blocks. Here the coins are laid out once:
  `Sender.Layout` (data): a finite set Bk of coming blocks; for each b the values Mk b of its masks;
    further coins F0 (free room, masks of nobody); the pads Pd; one equivalence between the sender's
    coins and ((all blocks' masks × F0) × Pd). All the Mk b, F0 and Pd are finite and not empty. By
    this equivalence the masks of different blocks, the further coins and the pads are different
    coins, uniform and independent. Where they land among the entries of the messages (at different
    places; no pad entry read as a mask) is said block by block, by the conditions below.
  `L.own b`: the split for the block b: the other coins are the other blocks' masks and F0.
  `L.PadLaw Sd`: one condition on the pads, for all blocks: at every joint seed the law of all
    answers, over the pads alone, is the same for every witness and every fixing of all other coins.

Main names, each under the hypotheses of its statement:
  `Spec.layout_laws`: for every block b, for its reading rd and overwriting put: `PadLaw`, "over",
    and rd (messages sent) = put (masks of b) (a body that reads the witness, the other blocks'
    masks and F0) give `(L.own b).Laws`.
  `Spec.layout_laws_entries`: the block reads entries (g : messages sent, further witness ↦ J → E),
    those in a set Rd, all others being set to 0, and its masks lie at places `at'` (injective,
    inside Rd). Then, with `L.PadLaw Sd`, "over" is free, and the rest is two plain conditions:
    (own) the entry at the place i is the mask i of b;
    (off) an entry in Rd off these places reads neither b's masks nor the pads.
    This is the reading of the sumcheck for a polynomial summand (Cb/Ld/LdPscZk.lean: `O.cut`,
    `O.put`).
  `Spec.layout_fresh`: so the sending of a family is Fresh for every block, from one hypothesis on
    the encoding.
  `Spec.ldSendSig_fresh_wide`: the sending to a statement over S (Cb/Ld/LdSigSum.lean), for a
    reading that may see, beside the new messages, all of the old pairs (message, encoding
    randomness) and the further witness; never the new encoding randomness. For any split, so for
    `L.own b`.
  `Spec.own_laws_keep`: the reading may hold, beside what the block reads, the whole further witness
    that is handed on (the overwriting does not touch it): the conditions are kept. (Later honest
    provers read that witness.)

Limits: the links between the sending and a block must not look at that block's masks
(`Honest.Blind`): a matter of those links. A mask that stands in two oracle messages is not covered.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFresh
import Mathlib.Logic.Equiv.Fintype
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type}

/-- The coins that go into the messages, laid out once: every coming block's masks, further coins,
pads. Data. -/
structure Sig.Sender.Layout (D : N.Sender W W') where
  Bk : Type
  [finBk : Fintype Bk]
  [decBk : DecidableEq Bk]
  Mk : Bk → Type
  [finMk : ∀ b, Fintype (Mk b)]
  [neMk : ∀ b, Nonempty (Mk b)]
  F0 : Type
  [finF0 : Fintype F0]
  [neF0 : Nonempty F0]
  Pd : Type
  [finPd : Fintype Pd]
  [nePd : Nonempty Pd]
  κ : D.Mk ≃ ((∀ b, Mk b) × F0) × Pd

attribute [instance] Sig.Sender.Layout.finBk Sig.Sender.Layout.decBk Sig.Sender.Layout.finMk
  Sig.Sender.Layout.neMk Sig.Sender.Layout.finF0 Sig.Sender.Layout.neF0
  Sig.Sender.Layout.finPd Sig.Sender.Layout.nePd

variable {D : N.Sender W W'}

namespace Sig.Sender.Layout
variable (L : D.Layout)

/-- the coins, from their parts -/
def mk' (ms : ∀ b, L.Mk b) (f : L.F0) (η : L.Pd) : D.Mk := L.κ.symm ((ms, f), η)

/-- the other blocks' masks -/
abbrev Oth (b : L.Bk) : Type := ∀ j : {j // j ≠ b}, L.Mk j
def oth (b : L.Bk) (ms : ∀ b, L.Mk b) : L.Oth b := fun j => ms j

/-- The split for the block b. -/
def own (b : L.Bk) : D.Own (L.Mk b) where
  M0 := L.Oth b × L.F0
  Pd := L.Pd
  κ := L.κ.trans
    (Equiv.prodCongr
      ((Equiv.prodCongr (Equiv.piSplitAt b L.Mk) (Equiv.refl L.F0)).trans (Equiv.prodAssoc _ _ _))
      (Equiv.refl L.Pd))

open Classical in
/-- The one condition on the pads. -/
def PadLaw (Sd : N.Seeds) : Prop :=
  ∀ s w w' ms ms' f f', (unif L.Pd).map (fun η => D.ans Sd s w (L.mk' ms f η)) =
    (unif L.Pd).map fun η => D.ans Sd s w' (L.mk' ms' f' η)

end Sig.Sender.Layout

open Classical in
/-- the entries in Rd; all others set to 0 -/
def cutTo {J : Type} (Rd : J → Prop) (m : J → E) : J → E := fun j =>
  if Rd j then m j else 0

end

namespace Spec
open IOR
variable (E : Type) [Field E]

/-- All the splits from one layout. -/
def layout_laws : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (L : D.Layout) (Sd : N.Seeds) (b : L.Bk)
      (Kc : Type) (rd : N.Msg → W' → Kc) (put : L.Mk b → Kc → Kc),
    L.PadLaw Sd → (∀ M M' k, put M (put M' k) = put M k) →
    (∃ body : W → L.Oth b × L.F0 → Kc, ∀ w ms f η,
      rd (D.upM (D.put w (L.mk' ms f η))) (D.rest w) = put (ms b) (body w (L.oth b ms, f))) →
    (L.own b).Laws Sd rd put

/-- The case: the block reads entries, its masks lie at places of their own. -/
def layout_laws_entries : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (L : D.Layout) (Sd : N.Seeds) (b : L.Bk)
      (J I : Type) (g : N.Msg → W' → J → E) (Rd : J → Prop) (at' : I → J) (val : L.Mk b → I → E),
    L.PadLaw Sd → Function.Injective at' → (∀ i, Rd (at' i)) →
    (∀ w ms f η i, g (D.upM (D.put w (L.mk' ms f η))) (D.rest w) (at' i) = val (ms b) i) →
    (∀ w ms ms' f η η' j, L.oth b ms = L.oth b ms' → Rd j → (∀ i, j ≠ at' i) →
      g (D.upM (D.put w (L.mk' ms f η))) (D.rest w) j =
        g (D.upM (D.put w (L.mk' ms' f η'))) (D.rest w) j) →
    (L.own b).Laws Sd (fun m w' => cutTo Rd (g m w')) fun M k => Function.extend at' (val M) k

/-- Under the hypotheses below, the sending of a family is Fresh for every block. -/
def layout_fresh : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec) (D : N.Sender W W') (t : N.O → ℕ)
      (Ri : X → E₀.Str → W → Prop) (L : D.Layout),
    D.Nn.Hides (N.budT t) →
    ∀ (b : L.Bk) (Kc : Type) (rd : N.Msg → W' → Kc) (put : L.Mk b → Kc → Kc),
      (L.own b).Laws Sd rd put →
      (ldSendFamHon Sd X E₀ D).Fresh
        Ri (fun _ T => N.budT t (ldSendFamSet N Sd T)) (fun v => rd (N.msgs v.1) v.2) (L.Mk b) put

/-- The sending to a statement over S, for a reading of (new messages; old pairs, further witness).
-/
def ldSendSig_fresh_wide : Prop :=
  ∀ (S N : Sig E) (Sd : N.Seeds) (St Wp Wp' : Type) (E₀ : ExtSpec)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (t : N.O → ℕ)
      (Ri : St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : D.Own Mb) (Kc : Type) (rd : N.Msg → S.Wit × Wp' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → D.Nn.Hides (N.budT t) →
    (ldSendSigHon Sd St E₀ D).Fresh Ri (ldSendSigNums S N Sd St E₀ Unit (fun _ => 0) t).bud
      (fun v => rd (N.msgs (S.right N (T := OMsg.Wit) v.1)) (S.left N (T := OMsg.Wit) v.1, v.2))
      Mb put

/-- The reading may hold the whole further witness that is handed on. -/
def own_laws_keep : Prop :=
  ∀ (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type) (U : D.Own Mb) (Sd : N.Seeds)
      (Kc : Type) (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → U.Laws Sd (fun m w' => (rd m w', w')) fun M k => (put M k.1, k.2)

end Spec
end Cb
