-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdVec.lean: the standard sender whose data are the entries of a vector that the witness
holds; the sender of the link as a standard sender.

This file has the data of the honest prover (`Sig.Sender`, Cb/Ld/LdSendFam.lean) of a reduction that
sends several words in one prover message, in the case in which what it encodes, beside its coins,
is a vector read off the witness (`vec`).

Definitions, statements and proofs.
It builds on Cb/Ld/LdSendStdL.lean (`Y : N.StdL F`, `Y.snd`, `Y.OK t`).

Why: a protocol names members of a family and places in their messages at which the entries of a
vector are (a folded message, a vector of partial products); its extractor reads the vector off
these places ("rdv"), and hands the rest of the witness through.

The laws of a sender (`D.Laws back`, that is `Sig.Sender.Laws`; for one oracle message
`OMsg.Sender.Laws`) ask two things: for every m and r, the word `D.Nn.enc m r` (for one oracle
message, `D.N.enc m r`), read as a native word through `upW`, is the code's encoding of `D.upM m`
with randomness `D.upR r`, for a family at each member a
(`(N.om a).upW (D.Nn.enc m r a) = (N.om a).C.enc (D.upM m a) (D.upR r a)`); and `back` returns w
from `D.upM (D.put w k)` and `D.rest w`, for every witness w and every k in `D.Mk`. Here
`D.Laws back` is a conclusion of `Spec.stdL_vec`.

Main names:
  `Y.vecDat vec ix`: the data of the standard sender: at the data place i of the member a is the
    entry c of the vector vec w if ix a i = some c, and 0 if ix a i = none: places that are neither
    entries of the vector, nor masks, nor pad (unused places, alignment) are data places that hold
    0; the sample reads them like all others. (Several places may hold one entry; a member without
    data has no place.)
  The one condition on places (`Y.Reads ix rdv`): every entry c of the vector is read by rdv at some
  data place (a, i) with ix a i = some c.
  `Spec.stdL_vec`: `Y.OK t`, `Y.Reads ix rdv`, mkW (vec w) (rest w) = w ⇒ the sender's laws for back
    m r := mkW (rdv m) r; the joint law of all answers does not depend on the witness, at every
    joint seed; the encoding hides t
    (in this sense: `(Y.snd (Y.vecDat vec ix) rest w0).Nn.Hides (N.budT t)`);
    two witnesses with the same vector give the same messages
    (in this sense: ∀ (w w' : W) k, vec w' = vec w →
      (Y.snd (Y.vecDat vec ix) rest w0).put w' k = (Y.snd (Y.vecDat vec ix) rest w0).put w k).
  `LdLkP.stdS ..`, `Spec.ldLk_std`: the link (Cb/Ld/LdLink.lean): the vector is (u₀, u₁), read at
    the places l₀ of the member i₀ and l₁ of the member i₁: `(P.stdS ..).OK` (`LdLkP.Snd.OK`) holds,
    from `Y.OK t`, the condition on places, and the four conditions that do not concern the sender.

Notation: `F`, `E`: finite fields, E an algebra over F; `Y`: a layout of the messages of the family
N (`N.StdL F`); `Y.Dt a`: a type (`Dt : N.O → Type`): the data entries of the message of the member
a; `rest`: a map (`W → W'`): what is handed on; `w0`: a witness (`W`), fixed (`Y`, `Y.Dt a`, `rest`,
`w0`: Cb/Ld/LdSendStdL.lean); `mkW`: a map (`(Ix → E) → W' → W`); `L`, `t`: a number for each member
of the family (`N.O → ℕ`).

Limits: this file says nothing on masks: for these see Cb/Ld/LdSendStdL.lean's `Y.layout` and
`stdL_padLaw`.
Wider than this protocol's technical report (lean/CREDITS.md): there the link has two oracle
messages, one for each folded message; by type the two named members i₀, i₁ may be one.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdL
import Cb.Ld.LdLink
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)

/-- the data: entries of a vector -/
def Sig.StdL.vecDat {W Ix : Type} (vec : W → Ix → E) (ix : ∀ a, Y.Dt a → Option Ix) :
    W → ∀ a, Y.Dt a → E :=
  fun w a i => (ix a i).elim 0 (vec w)

/-- The condition on places. -/
def Sig.StdL.Reads {Ix : Type} (ix : ∀ a, Y.Dt a → Option Ix) (rdv : N.Msg → Ix → E) : Prop :=
  ∀ c, ∃ a i, ix a i = some c ∧ ∀ m, rdv m c = m a (Y.atD a i)

end

/-- The sender of the link, standard. -/
@[reducible] def LdLkP.stdS {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E]
    [Fintype E] [Algebra F E] (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ)
    (Y : P.N.StdL F) (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (w0 : P.W1) : P.Snd where
  Sd := Sd
  dS := Y.snd (Y.vecDat (fun w : P.W1 => Sum.elim w.1.1 w.1.2) ix) (fun w => w.2) w0
  L := L
  t := t

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def stdL_vec : Prop :=
  ∀ (N : Sig E) (Y : N.StdL F) (t : N.O → ℕ) (W W' Ix : Type) (vec : W → Ix → E)
      (ix : ∀ a, Y.Dt a → Option Ix) (rest : W → W') (w0 : W)
      (rdv : N.Msg → Ix → E) (mkW : (Ix → E) → W' → W),
    Y.OK t → Y.Reads ix rdv → (∀ w, mkW (vec w) (rest w) = w) →
    (Y.snd (Y.vecDat vec ix) rest w0).Laws (fun m r => mkW (rdv m) r) ∧
    (∀ Sd : N.Seeds, (Y.snd (Y.vecDat vec ix) rest w0).Blind Sd) ∧
    (Y.snd (Y.vecDat vec ix) rest w0).Nn.Hides (N.budT t) ∧
    ∀ (w w' : W) k, vec w' = vec w →
      (Y.snd (Y.vecDat vec ix) rest w0).put w' k = (Y.snd (Y.vecDat vec ix) rest w0).put w k

/-- The link. -/
def ldLk_std : Prop :=
  ∀ (ι κ J Λ : Type) (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ) (Y : P.N.StdL F)
      (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (w0 : P.W1),
    Y.OK t → Y.Reads ix (fun m => Sum.elim (P.uv₀ m) (P.uv₁ m)) → (∀ a, (P.N.om a).C.Laws) →
    Sd.Fair → (∀ a, (P.N.om a).ListLE (L a)) → (∀ a, (P.N.om a).Evades) → (P.stdS Sd L t Y ix w0).OK

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem stdL_vec : Spec.stdL_vec F E := by
  intro N Y t W W' Ix vec ix rest w0 rdv mkW h hr hm
  have A := stdL_all F E N Y t W W' (Y.vecDat vec ix) rest w0 h
  refine ⟨A.2.2.2.1 _ fun w k => ?_, A.2.2.2.2.1, A.2.2.2.2.2.1,
    fun w w' k hw => A.2.2.2.2.2.2 w w' k ?_⟩
  · have e : rdv
          ((Y.snd (Y.vecDat vec ix) rest w0).upM ((Y.snd (Y.vecDat vec ix) rest w0).put w k)) =
        vec w := by
      funext c
      obtain ⟨a, i, hc, hrd⟩ := hr c
      rw [hrd, A.2.1 w k a i]
      show (ix a i).elim 0 (vec w) = vec w c
      rw [hc]
      rfl
    show mkW (rdv _) (rest w) = w
    rw [e]
    exact hm w
  · unfold Sig.StdL.vecDat
    rw [hw]

theorem ldLk_std : Spec.ldLk_std F E := by
  intro ι κ J Λ P Sd L t Y ix w0 h hr hL hF hl he
  have A := stdL_vec F E P.N Y t P.W1 P.W0 (κ ⊕ κ) (fun w : P.W1 => Sum.elim w.1.1 w.1.2) ix
    (fun w => w.2) w0 (fun m => Sum.elim (P.uv₀ m) (P.uv₁ m))
    (fun v r => ((fun k => v (Sum.inl k), fun k => v (Sum.inr k)), r)) h hr fun _ => rfl
  exact ⟨hL, hF, hl, he, A.1, A.2.1 Sd, A.2.2.1⟩

end
end Cb
