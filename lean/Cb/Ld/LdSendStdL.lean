-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdL.lean: the standard sender of a given family of oracle messages, in any format, from
a layout of its messages: all that `Spec.ldSendFam_goodT` (Cb/Ld/LdSendFam.lean) asks of a sender,
from conditions on codes, formats and samples. (not all hypotheses are named here: see
`Spec.stdL_all`)

This file defines, from a layout, the data of the honest prover (`Sig.Sender`, Cb/Ld/LdSendFam.lean)
of a reduction that sends several words in one prover message; the layout says which coordinates of
each message are read off the witness and which are the prover's coins.

Definitions, statements and proofs.
Cb/Ld/LdSendStd.lean builds a family in the plain format. Here the family N is given (a parameter of
a protocol), and a layout is laid over it.

The layout (`Y : N.StdL F`). The entries of the message of the member a are of three kinds, told
apart by ν a:
  data (Dt a): read off the witness; free entries (Fr a): uniform elements of E, coins of the
  sender: masks of coming blocks; pad (Pd a): uniform elements of the subfield F, for the privacy of
  the member's sample. Any of the three may be empty.
  The format: En a: the encoder of the member a that puts out words as sent; upM a, upR a: how its
  messages and randomness are read over E; msgOf a: its message from (data and free entries, pad).
The sender (`Y.snd dat rest w0`), for any types W, W': dat : W → the data of all members;
rest : W → W': what is handed on; w0 : W: a fixed witness. All coins are independent
(Cb/Ld/LdSendMem.lean).
What is asked (`Y.OK t`): enc: a word as sent, read over E, is the code's encoding; lay: msgOf lays
data, free entries and pad at their places; priv: every member's sample is private under its pad at
every seed; hides: the encoder of the member a hides `t a` long positions.

`D.Blind Sd` (`Sig.Sender.Blind`) asks that, for every joint seed s and all witnesses w and w', the
distribution of `D.ans Sd s w k` over uniform k in `D.Mk` equal that of `D.ans Sd s w' k`;
`D.ans Sd s w k` gives the family, over the members a, of the answers `(N.om a).Z.val (Sd.sd a s)`
of `D.upM (D.put w k) a`, and the distribution is of that whole family. For one oracle message o,
`D.Blind` (`OMsg.Sender.Blind`) asks the same with a seed ρ of `o.Z` in place of s: that, for every
ρ and all w and w', the distribution of `D.ans ρ w k` over uniform k in `D.Mk` equal that of
`D.ans ρ w' k`, where `D.ans ρ w k` is `o.Z.val ρ (D.upM (D.put w k))`. Here `D.Blind Sd` is a
conclusion of `Spec.stdL_all` (its clause (blind)).
`N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages m
and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
`N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S. Here it is
a premise of `Spec.stdL_all` (the field `hides` of `Y.OK t`, of each `Y.En a`) and a conclusion (its
clause (hides), of `(Y.snd dat rest w0).Nn`).

Main names:
  `Spec.stdL_all`: under `Y.OK t`, with D := Y.snd dat rest w0:
    (enc) the first law of a sender;
    (data), (free) what stands at a place of data is dat w; at a free place: the coin;
    (laws) `D.Laws back` for every back with back (messages sent) (rest w) = w;
    (blind) at every joint seed, however seeds are shared, the joint law of all answers does not
            depend on the witness;
    (hides) the family's encoding hides t
            (in this sense: `(Y.snd dat rest w0).Nn.Hides (N.budT t)`);
    (apart) two witnesses with the same data give the same messages
            (in this sense: ∀ (w w' : W) k, dat w' = dat w →
              (Y.snd dat rest w0).put w' k = (Y.snd dat rest w0).put w k).
    "rest" is rest by definition.
  Masks of several coming blocks (`Y.layout .. ε`). Split the free entries, by any equivalence ε,
  into the masks of blocks b ∈ Bk and further coins F0 (every Mk b and F0 not empty): this is a
  layout of the sender's coins in the sense of Cb/Ld/LdSendFreshMany.lean, with all pads as its
  pads.
  `Spec.stdL_padLaw`: under `Y.OK t` its one condition on the pads holds at every joint seed. So
    that file's rules (`layout_laws`, `layout_laws_entries`, `layout_fresh`), each under the
    hypotheses of its statement, give, for every block, the conditions `Own.Laws` and freshness.
  `Spec.stdL_plain`: the family built in Cb/Ld/LdSendStd.lean has such a layout (`G.toL`), which is
    OK under `G.Priv` and `G.Zk`.

Limits: this file says nothing on the conditions on codes and samples that do not concern the sender
(laws, lists, evading samples, fair seeds).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStd
import Cb.Ld.LdSendFreshManyProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A layout of the messages of a family. -/
structure Sig.StdL (F : Type) {E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (N : Sig E) where
  Dt : N.O → Type
  [finDt : ∀ a, Fintype (Dt a)]
  Fr : N.O → Type
  [finFr : ∀ a, Fintype (Fr a)]
  Pd : N.O → Type
  [finPd : ∀ a, Fintype (Pd a)]
  ν : ∀ a, (N.om a).C.J ≃ (Dt a ⊕ Fr a) ⊕ Pd a
  En : ∀ a, Hiop.Enc (N.om a).nat
  upM : ∀ a, (En a).Msg → (N.om a).Msg
  upR : ∀ a, (En a).Rnd → (N.om a).Rnd
  msgOf : ∀ a, (Dt a ⊕ Fr a → E) → (Pd a → F) → (En a).Msg

attribute [instance] Sig.StdL.finDt Sig.StdL.finFr Sig.StdL.finPd

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)

/-- What is asked. -/
structure OK (t : N.O → ℕ) : Prop where
  enc   : ∀ a m r, (N.om a).upW ((Y.En a).enc m r) = (N.om a).C.enc (Y.upM a m) (Y.upR a r)
  lay   : ∀ a x η n, Y.upM a (Y.msgOf a x η) ((Y.ν a).symm n) = withPad (F := F) x η n
  priv  : ∀ a, ((N.om a).Z.comap (Y.ν a).symm).Private F fun _ => True
  hides : ∀ a, (Y.En a).Hides ((N.om a).C.budT (t a))

/-- the places of data and of free entries -/
def atD (a : N.O) (i : Y.Dt a) : (N.om a).C.J := (Y.ν a).symm (Sum.inl (Sum.inl i))
def atF (a : N.O) (i : Y.Fr a) : (N.om a).C.J := (Y.ν a).symm (Sum.inl (Sum.inr i))

variable {W W' : Type} (dat : W → ∀ a, Y.Dt a → E) (rest : W → W') (w0 : W)

open Classical in
/-- the sender of a member -/
@[reducible] def mem : ∀ a, (N.om a).Sender W Unit := fun a =>
  { N := Y.En a
    upM := Y.upM a
    upR := Y.upR a
    Mk := (Y.Fr a → E) × (Y.Pd a → F)
    put := fun w k => Y.msgOf a (Sum.elim (dat w a) k.1) k.2
    rest := fun _ => ()
    w0 := w0 }

open Classical in
/-- the same with the free entries fixed -/
@[reducible] def mem' (M : ∀ a, Y.Fr a → E) : ∀ a, (N.om a).Sender W Unit := fun a =>
  { N := Y.En a
    upM := Y.upM a
    upR := Y.upR a
    Mk := Y.Pd a → F
    put := fun w η => Y.msgOf a (Sum.elim (dat w a) (M a)) η
    rest := fun _ => ()
    w0 := w0 }

/-- The sender. -/
@[reducible] def snd : N.Sender W W' := Sig.Sender.ofMem (Y.mem dat w0) rest w0

open Classical in
/-- The sender's coins, laid out for several coming blocks. -/
@[reducible] def layout (Bk : Type) [Fintype Bk] [DecidableEq Bk] (Mk : Bk → Type)
    [∀ b, Fintype (Mk b)] [∀ b, Nonempty (Mk b)] (F0 : Type) [Fintype F0] [Nonempty F0]
    (ε : (∀ a, Y.Fr a → E) ≃ (∀ b, Mk b) × F0) : (Y.snd dat rest w0).Layout where
  Bk := Bk
  Mk := Mk
  F0 := F0
  Pd := ∀ a, Y.Pd a → F
  κ := { toFun := fun k => (ε fun a => (k a).1, fun a => (k a).2)
         invFun := fun z a => (ε.symm z.1 a, z.2 a)
         left_inv := fun _ => funext fun a => Prod.ext (congrFun (ε.symm_apply_apply _) a) rfl
         right_inv := fun _ => Prod.ext (ε.apply_symm_apply _) rfl }

open Classical in
/-- one block for each member -/
@[reducible] def byMember : (Y.snd dat rest w0).Layout :=
  Y.layout dat rest w0 N.O (fun a => Y.Fr a → E) Unit (Equiv.prodPUnit _).symm

end Sig.StdL

open Classical in
/-- The layout of the family built in the plain format. -/
@[reducible] def StdSig.toL
    {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (G : StdSig F E) :
    G.sig.StdL F where
  Dt := G.Dt
  Fr := G.Fr
  Pd := G.Pd
  ν := G.ν
  En := fun a => (G.C a).Nn
  upM := fun _ m => m
  upR := fun _ r => r
  msgOf := fun a x η j => withPad (F := F) x η (G.ν a j)

namespace Spec

/-- All that is asked of a sender (by `Spec.ldSendFam_goodT`). -/
def stdL_all : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E)
      (rest : W → W') (w0 : W),
    Y.OK t →
    (∀ m r a, (N.om a).upW ((Y.snd dat rest w0).Nn.enc m r a) =
      (N.om a).C.enc ((Y.snd dat rest w0).upM m a) ((Y.snd dat rest w0).upR r a)) ∧
    (∀ w k a i, (Y.snd dat rest w0).upM ((Y.snd dat rest w0).put w k) a (Y.atD a i) = dat w a i) ∧
    (∀ w (k : (Y.snd dat rest w0).Mk) a i,
      (Y.snd dat rest w0).upM ((Y.snd dat rest w0).put w k) a (Y.atF a i) = (k a).1 i) ∧
    (∀ back : N.Msg → W' → W,
      (∀ w k, back ((Y.snd dat rest w0).upM ((Y.snd dat rest w0).put w k)) (rest w) = w) →
      (Y.snd dat rest w0).Laws back) ∧
    (∀ Sd : N.Seeds, (Y.snd dat rest w0).Blind Sd) ∧
    (Y.snd dat rest w0).Nn.Hides (N.budT t) ∧
    ∀ (w w' : W) k, dat w' = dat w → (Y.snd dat rest w0).put w' k = (Y.snd dat rest w0).put w k

/-- The one condition on the pads, for every split of the free entries into blocks. -/
def stdL_padLaw : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E) (rest : W → W')
      (w0 : W) (Bk : Type) [Fintype Bk] [DecidableEq Bk] (Mk : Bk → Type) [∀ b, Fintype (Mk b)]
      [∀ b, Nonempty (Mk b)] (F0 : Type) [Fintype F0] [Nonempty F0]
      (ε : (∀ a, Y.Fr a → E) ≃ (∀ b, Mk b) × F0) (Sd : N.Seeds),
    Y.OK t → (Y.layout dat rest w0 Bk Mk F0 ε).PadLaw Sd

def stdL_plain : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (G : StdSig F E) (t : G.O → ℕ),
    G.Priv → G.Zk t → G.toL.OK t

end Spec

/-! ## Proofs -/

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {N : Sig E}
  (Y : N.StdL F) {W W' : Type} (dat : W → ∀ a, Y.Dt a → E) (w0 : W) {t : N.O → ℕ}

theorem unifM (h : Y.OK t) (a : N.O) : (Y.mem dat w0 a).Uniform := by
  classical
  exact ldSend_uniform_of_private E F (N.om a) W Unit (Y.mem dat w0 a) (Y.Dt a ⊕ Y.Fr a) (Y.Pd a)
    (Y.Fr a → E) (Y.ν a) (Equiv.refl _) (fun w μ => Sum.elim (dat w a) μ)
    (fun _ _ n => h.lay a _ _ n) (h.priv a)

theorem unifM' (h : Y.OK t) (M : ∀ a, Y.Fr a → E) (a : N.O) : (Y.mem' dat w0 M a).Uniform :=
  ldSend_uniform_of_private E F (N.om a) W Unit (Y.mem' dat w0 M a) (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) Unit
    (Y.ν a) (Equiv.punitProd _).symm (fun w _ => Sum.elim (dat w a) (M a))
    (fun _ _ n => h.lay a _ _ n) (h.priv a)

end Sig.StdL

theorem stdL_all : Spec.stdL_all := by
  intro F E _ _ _ _ _ N Y t W W' dat rest w0 h
  have henc : ∀ m r a, (N.om a).upW ((Y.snd dat rest w0).Nn.enc m r a) =
      (N.om a).C.enc ((Y.snd dat rest w0).upM m a) ((Y.snd dat rest w0).upR r a) :=
    fun m r a => h.enc a (m a) (r a)
  refine ⟨henc, fun w k a i => h.lay a _ _ _, fun w k a i => h.lay a _ _ _,
    fun back hb => ⟨henc, hb⟩, fun Sd => ?_, ?_, ?_⟩
  · exact ldSendMem_blind E N W W' (Y.mem dat w0) rest w0 Sd fun a =>
      ldSend_blind_of_uniform E (N.om a) W Unit _ (Y.unifM dat w0 h a)
  · exact ldSendMem_hides E N W W' (Y.mem dat w0) rest w0 t h.hides
  · intro w w' k hw
    funext a
    show Y.msgOf a (Sum.elim (dat w' a) (k a).1) (k a).2 =
      Y.msgOf a (Sum.elim (dat w a) (k a).1) (k a).2
    rw [hw]

theorem stdL_padLaw : Spec.stdL_padLaw := by
  intro F E _ _ _ _ _ N Y t W W' dat rest w0 Bk _ _ Mk _ _ F0 _ _ ε Sd h s w w' ms ms' f f'
  exact (ldSendMem_uniform E N W W' (Y.mem' dat w0 (ε.symm (ms, f))) rest w0 Sd
      (Y.unifM' dat w0 h _) s w).trans
    (ldSendMem_uniform E N W W' (Y.mem' dat w0 (ε.symm (ms', f'))) rest w0 Sd
      (Y.unifM' dat w0 h _) s w').symm

theorem stdL_plain : Spec.stdL_plain := by
  intro F E _ _ _ _ _ G t hP hZ
  refine ⟨fun _ _ _ => rfl, fun a x η n => ?_, fun a => ?_, hZ⟩
  · show withPad (F := F) x η (G.ν a ((G.ν a).symm n)) = _
    rw [Equiv.apply_symm_apply]
  · show (((G.Z a).comap (G.ν a)).comap (G.ν a).symm).Private F fun _ => True
    rw [Sample.comap_symm']
    exact hP a

end Cb
