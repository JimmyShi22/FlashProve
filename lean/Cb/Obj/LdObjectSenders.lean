-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectSenders.lean: the senders of a request's sendings and of the preamble of
weights-formedness are taken to be standard senders (`Y.snd`). What is asked of these senders then
becomes conditions on codes, formats, samples and layouts.

In standard terms: the honest prover's algorithm for sending encoded messages (a sender:
`Sig.Sender`, Cb/Ld/LdSendFam.lean). The theorems on whole protocols take it as a parameter with
assumed properties; here it is one fixed construction, the standard sender, and these properties are
derived from `Y.OK t` and the further premises of the three statements.

Definitions, statements and proofs.
The file builds on Cb/Ld/LdSendStdL.lean (the standard sender `Y.snd` of a given family N, from a
layout `Y : N.StdL F` of its messages into data, free entries and pads).

Why: the hypotheses of the theorems on whole protocols ask, for every sending, three properties of
the honest sender, which is a parameter there: its laws, "the law of the answers does not depend on
the witness", "the encoding hides". With the standard sender all three follow from `Y.OK t` (the
laws: with an extractor as in `Spec.stdL_back`).

Main names:
  `Y.dataOf m`, `Spec.stdL_back`: under `Y.OK t`, for an extractor that reads the data of the
    messages alone, back m r := bk (Y.dataOf m) r, with bk (dat w) (rest w) = w, the sender's laws
    hold.
  `LdSendD.std`, `Spec.ldSendD_std`: one sending of a request (`LdSendD a`, Cb/Req1/LdSegKit.lean).
    The witness is (the old pairs, a further witness); the data are read off it (dat); the old pairs
    are handed on, and rst of the further witness. `LdSendD.Hyp` holds of it, from: `Y.OK t`; bk₀
    (dat w) (rst w.2) = w.2; and the four conditions that do not concern the sender (codes' laws,
    fair seeds, lists, evading samples).
  `LdWfP.stdD`, `Spec.ldWf_std`: the sending of weights-formedness (`Blk.D`, Cb/Ld/LdWf.lean). The
    witness is (the vectors of multiplicities, a further witness); the further witness is handed on.
    The three fields sender, sBlind, hides of `Blk.Hyp` hold for it, from: `Y.OK t`; P.body reads
    the data alone and undoes dat.

The laws of a sender (`D.Laws back`, that is `Sig.Sender.Laws`; for one oracle message
`OMsg.Sender.Laws`) ask two things: for every m and r, the word `D.Nn.enc m r` (for one oracle
message, `D.N.enc m r`), read as a native word through `upW`, is the code's encoding of `D.upM m`
with randomness `D.upR r`, for a family at each member a
(`(N.om a).upW (D.Nn.enc m r a) = (N.om a).C.enc (D.upM m a) (D.upR r a)`); and `back` returns w
from `D.upM (D.put w k)` and `D.rest w`, for every witness w and every k in `D.Mk`. Here they are a
conclusion (`Spec.stdL_back`, `Spec.ldWf_std`).

Notation: `L` (in `LdSendD.std`): a map `N.O → ℕ` (`LdSendD`, Cb/Req1/LdSegKit.lean: bounds for the
lists); `t` (there): a map `N.O → ℕ` (`LdSendD`: long positions that the encodings bear).

Limits: this file says nothing on the test for linear constraints and the link (other files). It
says nothing on masks: Cb/Ld/LdSendStdL.lean's `Y.layout` and `stdL_padLaw`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdL
import Cb.Req1.LdSegKit
import Cb.Ld.LdWf
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the data, read off the messages -/
def Sig.StdL.dataOf {N : Sig E} (Y : N.StdL F) (m : N.Msg) : ∀ a, Y.Dt a → E := fun a i =>
  m a (Y.atD a i)

/-- One sending of a request, with the standard sender. -/
@[reducible] def LdSendD.std {Kc : Type} (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds)
    (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E)
    (rst : a.Wp → Wp') (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) :
    LdSendD a where
  N := N
  Sd := Sd
  Wp' := Wp'
  bk := fun m r => bk₀ (Y.dataOf m) r
  D := Y.snd dat (fun w => (w.1, rst w.2)) w0
  L := L
  t := t

/-- The sender of weights-formedness, standard. -/
@[reducible] def LdWfP.stdD {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C) (Y : P.S.StdL F)
    (dat : P.Body → ∀ a, Y.Dt a → E) (w0 : P.Body × P.Wp) :
    P.S.Sender (P.Body × P.Wp) P.Wp :=
  Y.snd (fun w => dat w.1) (fun w => w.2) w0

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- An extractor that reads the data alone. -/
def stdL_back : Prop :=
  ∀ (N : Sig E) (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E)
      (rest : W → W') (w0 : W) (bk : (∀ a, Y.Dt a → E) → W' → W),
    Y.OK t → (∀ w, bk (dat w) (rest w) = w) → (Y.snd dat rest w0).Laws fun m r => bk (Y.dataOf m) r

/-- One sending of a request. -/
def ldSendD_std : Prop :=
  ∀ (Kc : Type) (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ)
      (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    Y.OK t → (∀ w, bk₀ (dat w) (rst w.2) = w.2) → (∀ i, (N.om i).C.Laws) → Sd.Fair →
    (∀ i, (N.om i).ListLE (L i)) → (∀ i, (N.om i).Evades) →
    (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).Hyp

/-- The sending of weights-formedness. -/
def ldWf_std : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (Y : P.S.StdL F) (t : P.S.O → ℕ) (dat : P.Body → ∀ a, Y.Dt a → E)
      (w0 : P.Body × P.Wp) (bd : (∀ a, Y.Dt a → E) → P.Body),
    Y.OK t → (∀ m, P.body m = bd (Y.dataOf m)) → (∀ b, bd (dat b) = b) →
    (P.stdD Y dat w0).Laws P.back ∧
    (P.stdD Y dat w0).Blind P.Sd ∧
    (P.stdD Y dat w0).Nn.Hides (P.S.budT t)

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem stdL_data (N : Sig E) (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E)
    (rest : W → W') (w0 : W) (h : Y.OK t) (w : W) (k : (Y.snd dat rest w0).Mk) :
    Y.dataOf ((Y.snd dat rest w0).upM ((Y.snd dat rest w0).put w k)) = dat w :=
  funext fun a => funext fun i => (stdL_all F E N Y t W W' dat rest w0 h).2.1 w k a i

theorem stdL_back : Spec.stdL_back F E := fun N Y t W W' dat rest w0 bk h hb =>
  (stdL_all F E N Y t W W' dat rest w0 h).2.2.2.1 _ fun w k => by
    show bk (Y.dataOf _) (rest w) = w
    rw [stdL_data F E N Y t W W' dat rest w0 h w k]
    exact hb w

theorem ldSendD_std : Spec.ldSendD_std F E := by
  intro Kc a N Sd Wp' L t Y dat rst bk₀ w0 h hb hL hF hl he
  have A := stdL_all F E N Y t _ _ dat (fun w => (w.1, rst w.2)) w0 h
  refine ⟨hL, hF, hl, he, A.2.2.2.1 _ fun w k => ?_, A.2.2.2.2.1 Sd, A.2.2.2.2.2.1⟩
  show (w.1, bk₀ (Y.dataOf _) (rst w.2)) = w
  rw [stdL_data F E N Y t _ _ dat (fun w => (w.1, rst w.2)) w0 h w k, hb w]

theorem ldWf_std : Spec.ldWf_std F E := by
  intro C P Y t dat w0 bd h hbody hbd
  have A := stdL_all F E P.S Y t _ _ (fun w : P.Body × P.Wp => dat w.1) (fun w => w.2) w0 h
  refine ⟨A.2.2.2.1 _ fun w k => ?_, A.2.2.2.2.1 P.Sd, A.2.2.2.2.2.1⟩
  show (P.body _, w.2) = w
  rw [hbody,
    stdL_data F E P.S Y t _ _ (fun w : P.Body × P.Wp => dat w.1) (fun w => w.2) w0 h w k, hbd]

end
end Cb
