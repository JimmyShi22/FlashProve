-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinStd.lean: the three senders of the test for linear constraints on the encoded index as
standard senders: what is asked of them reduces to conditions on places, layouts, codes, samples
and numbers.

In standard terms: the file is about the honest prover's part in the three steps of the test for
linear constraints (a proximity test with claims on the encoded index) that send oracle messages. A
sender (`Sig.Sender`, Cb/Ld/LdSendFam.lean) says how the new messages are made from the witness and
coins; here the three senders are explicit terms, made from a layout of the messages.

Definitions, statements (in `Cb.Spec`) and proofs. For any data P of the test (`LdLinP`,
Cb/Ld/LdLin.lean): any three families, in any format.
Cb/Ld/LdLin.lean takes the three honest senders as data (`P.Snd`) with 21 properties (`Snd.OK`); the
batch and the masks ask two more (`Snd.Apart`, Cb/Ld/LdLinChainFresh.lean). Of these, 8 are
properties of the sender (its laws and "blind", each for the three senders; `Apart`'s two) and 3
speak of its encoder. Here the senders are terms.

Main names:
  `T : P.Std F`: the data: a layout of the messages of each family (`N.StdL F`,
    Cb/Ld/LdSendStdL.lean: every entry of a member's message is a data entry, a free entry or a pad
    entry; the format in which it is sent); pW, pU, pO: which entry of the vector (w; the folded
    full message u; ω) a data entry holds, or that it holds 0 (places that are not used, alignment:
    neither of the vector, nor a mask, nor a pad; the sample reads them like all others); qW, qU,
    qO: at which data entry of the named member an entry of the vector stands; fixed witnesses.
  `T.Places`: the places lW, lU, lO of the test are the data entries `qW`, `qU`, `qO` of the named
    members. (A member without data entries is mask-only. A further member may hold entries of the
    vector again: wider than this protocol's technical report (lean/CREDITS.md), not used,
    harmless.)
  `T.snd`: the three senders: each member's message := data read off the vector alone, free entries
    and pad from the member's own coins; what is handed on: the witness before. The members of one
    prover message have independent coins (free entries, pad, encoding randomness); each member has
    one block of pad entries of its own. Only the seed of the samples is joint (`P.SdW` ..).
  `Spec.ldLinStd_ok`: `T.Places`, the three layouts' conditions (`Y.OK t`: the format's law, the
    layout, the sample is private under the pad, the encoder hides t positions) and the 12
    conditions that do not concern a sender (laws of the codes, fair seeds, lists, evading samples)
    ⇒ `(T.snd ..).OK`.
  `Spec.ldLinStd_apart`: `(T.snd ..).Apart`, from nothing: by the form of the term.

Limits: this file does not say that layouts with these conditions exist (for the plain format, under
`G.Priv` and `G.Zk t`: `stdL_plain`, Cb/Ld/LdSendStdL.lean; toys). It says nothing on the conditions
on masks that ride in further members (`Own.Laws`): Cb/Ld/LdSendStdL.lean has the layout of the
coins and its law of the pads (`Own.Laws` at a standard sender: `Spec.stdL_own`,
Cb/Ld/LdSendStdOwn.lean; at two of these senders (`dW`, `dO`): `Spec.ldLinStdSp_snd`,
Cb/Ld/LdLinStdSp.lean; each under its hypotheses). The standard sender is no proposal for a protocol
beyond what the report says of a sending: data, masks, a pad.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainFresh
import Cb.Ld.LdSendStdL
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The three senders as standard senders: the data. -/
structure LdLinP.Std (F : Type) {E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdLinP E ι κ J Y) where
  YW : P.NW.StdL F
  YU : P.NU.StdL F
  YO : P.NO.StdL F
  /-- which entry of the vector a data entry holds; none: it holds 0 -/
  pW : ∀ a, YW.Dt a → Option P.D.Col
  pU : ∀ a, YU.Dt a → Option κ
  pO : ∀ a, YO.Dt a → Option Y
  /-- at which data entry of the named member an entry of the vector stands -/
  qW : P.D.Col → YW.Dt P.iW
  qU : κ → YU.Dt P.iU
  qO : Y → YO.Dt P.iO
  /-- fixed witnesses -/
  w0 : P.W0
  w1 : P.W1
  w3 : P.W3

namespace LdLinP.Std
variable {F E ι κ J Y : Type}
  [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F)

/-- The places of the test are data entries of the named members. -/
structure Places : Prop where
  lW : ∀ c, P.lW c = T.YW.atD P.iW (T.qW c)
  hW : ∀ c, T.pW P.iW (T.qW c) = some c
  lU : ∀ k, P.lU k = T.YU.atD P.iU (T.qU k)
  hU : ∀ k, T.pU P.iU (T.qU k) = some k
  lO : ∀ y, P.lO y = T.YO.atD P.iO (T.qO y)
  hO : ∀ y, T.pO P.iO (T.qO y) = some y

/-- the data of the messages: entries of the vector, or 0 -/
def datW (w : P.WA) : ∀ a, T.YW.Dt a → E := fun a i => (T.pW a i).elim 0 w.1
def datU (w : P.W2) : ∀ a, T.YU.Dt a → E := fun a i => (T.pU a i).elim 0 w.1
def datO (w : P.W4) : ∀ a, T.YO.Dt a → E := fun a i => (T.pO a i).elim 0 w.1

/-- The three senders. -/
@[reducible] def snd (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
    (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) : P.Snd where
  dW := T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0)
  dU := T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)
  dO := T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)
  LW := LW
  LU := LU
  LO := LO
  tW := tW
  tU := tU
  tO := tO

end LdLinP.Std

namespace Spec
section
variable (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: under the hypotheses below, the three senders `T.snd ..` have what the three sendings
ask (`Snd.OK`). -/
def ldLinStd_ok : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ),
    T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO → (∀ a, (P.NW.om a).C.Laws) → P.SdW.Fair →
    (∀ a, (P.NW.om a).ListLE (LW a)) → (∀ a, (P.NW.om a).Evades) → (∀ a, (P.NU.om a).C.Laws) →
    P.SdU.Fair → (∀ a, (P.NU.om a).ListLE (LU a)) → (∀ a, (P.NU.om a).Evades) →
    (∀ a, (P.NO.om a).C.Laws) → P.SdO.Fair → (∀ a, (P.NO.om a).ListLE (LO a)) →
    (∀ a, (P.NO.om a).Evades) → (T.snd LW LU LO tW tU tO).OK

/-- States, of `T.snd ..`: no later family's messages read an earlier family's witness
(`Snd.Apart`). It holds by the form of the term. -/
def ldLinStd_apart : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ),
    (T.snd LW LU LO tW tU tO).Apart

end
end Spec

section
variable {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldLinStd_ok : Spec.ldLinStd_ok F E ι κ J Y := by
  intro P T LW LU LO tW tU tO hP hW hU hO l1 f1 s1 e1 l2 f2 s2 e2 l3 f3 s3 e3
  obtain ⟨-, aW, -, bW, cW, dW, -⟩ :=
    stdL_all F E P.NW T.YW tW P.WA P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0) hW
  obtain ⟨-, aU, -, bU, cU, dU, -⟩ :=
    stdL_all F E P.NU T.YU tU P.W2 P.W1 T.datU (fun w => w.2) (fun _ => 0, T.w1) hU
  obtain ⟨-, aO, -, bO, cO, dO, -⟩ :=
    stdL_all F E P.NO T.YO tO P.W4 P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3) hO
  exact
    { lawsW := l1, fairW := f1, listW := s1, evW := e1
      sndW := bW P.backW fun w k => Prod.ext (funext fun c => by
        show (T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0)).upM
            ((T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0)).put w k) P.iW (P.lW c) = w.1 c
        rw [hP.lW c, aW w k P.iW (T.qW c)]
        show (T.pW P.iW (T.qW c)).elim 0 w.1 = w.1 c
        rw [hP.hW c]
        rfl) rfl
      blW := cW P.SdW, hidW := dW
      lawsU := l2, fairU := f2, listU := s2, evU := e2
      sndU := bU P.backU fun w k => Prod.ext (funext fun c => by
        show (T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).upM
            ((T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).put w k) P.iU (P.lU c) = w.1 c
        rw [hP.lU c, aU w k P.iU (T.qU c)]
        show (T.pU P.iU (T.qU c)).elim 0 w.1 = w.1 c
        rw [hP.hU c]
        rfl) rfl
      blU := cU P.SdU, hidU := dU
      lawsO := l3, fairO := f3, listO := s3, evO := e3
      sndO := bO P.backO fun w k => Prod.ext (funext fun c => by
        show (T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).upM
            ((T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).put w k) P.iO (P.lO c) = w.1 c
        rw [hP.lO c, aO w k P.iO (T.qO c)]
        show (T.pO P.iO (T.qO c)).elim 0 w.1 = w.1 c
        rw [hP.hO c]
        rfl) rfl
      blO := cO P.SdO, hidO := dO }

theorem ldLinStd_apart : Spec.ldLinStd_apart F E ι κ J Y := by
  intro P T LW LU LO tW tU tO
  refine ⟨fun w w' k h => ?_, fun w w' k h => ?_⟩
  · funext a
    show T.YU.msgOf a (Sum.elim (T.datU w' a) (k a).1) (k a).2 =
      T.YU.msgOf a (Sum.elim (T.datU w a) (k a).1) (k a).2
    unfold LdLinP.Std.datU
    rw [h]
  · funext a
    show T.YO.msgOf a (Sum.elim (T.datO w' a) (k a).1) (k a).2 =
      T.YO.msgOf a (Sum.elim (T.datO w a) (k a).1) (k a).2
    unfold LdLinP.Std.datO
    rw [h]

end
end Cb
