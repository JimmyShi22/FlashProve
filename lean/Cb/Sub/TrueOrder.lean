-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/TrueOrder.lean: a chain with a message that is sent in its middle, in the true order: the
blocks in front over the early oracle messages, the sending of the late ones, the blocks behind over
both.

Definitions, statements and their proofs.
`TWhole.KnowAt` speaks for each fixed tuple of messages. A block R in front of the late messages has
it at the early tuples (S₁.Msg), a block T behind them at the pairs (S₁.Msg × N.Msg). Each is passed
to oracle messages with samples by the library's `sigLift_know` (Cb/Ld/LdSigLift.lean): R over S₁; T
over S₁ for each fixed late tuple, and then over N. Between them stands the library's sending of the
family N (`ldSendFam`, Cb/Ld/LdSendFam.lean), with its own knowledge soundness `ldSendFam_into`:
there the witness grows by the late messages. So the late messages are NOT fixed while R runs.
The seam: what T starts from (Rl, at a pair of tuples) gives what R ends at (V, at the early tuple).
For a ledger that is `late_holds` (Cb/Sub/Late.lean): `realJ` gives `virtJ` (Cb/Sub/LateJoin.lean).

Main names:
  `sliceU u B`: a joint at the pairs of tuples, at the fixed late tuple u.
  `over2 S₁ B`: B over S₁, for each late tuple: a base joint for `N.over`.
  `lift_into`: `KnowAt` gives `KnowInto` over a signature (soundness, and the condition is carried).
  `over2_knowAt`: a block at the pairs of tuples, over S₁, is a block at the late tuples.
  `send_step`: ONE SENDING IN THE MIDDLE: whatever stands in front, the sending, a block behind. Its
    conclusion has the form of its first premise: so a chain may hold several sendings.
  `true_order`: from `KnowAt R A V` at S₁.Msg, `KnowAt T Rl C` at S₁.Msg × N.Msg, the seam, and the
    three premises of the sending (fair seeds, list bounds, evading samples): `KnowInto` of the
    three reductions in a row, from `S₁.over A` to `N.over (over2 S₁ C)`; errors in a row: R's, the
    sending's, T's.
  `late_true_order`: the same at `virtJ`, `realJ` (Cb/Sub/LateJoin.lean): a ledger on early and late
    entries; the weights are read off R's output statement.

Limits: nothing on an honest prover or on zero knowledge: each statement is true of a verifier that
rejects everything. The three are joined as reductions (`Reduction.seq` of their `.red`). The
extractor is the composed one (`extSeq`), with a default d.
(i) The condition in front holds "no collision among S₁'s lists" (`S₁.CF`): the sending of S₁ and
its error are NOT in the list of errors. (ii) R and T read no oracle message: words and samples are
only copied. (iii) The conclusions are `KnowInto` alone: `point` and `isLocal` are dropped, and
nothing leads back to `KnowAt`. (iv) Every block has the extractor that hands the further witness
back, on one type Wp. (v) A sending is the library's two rounds (words, then a joint seed; the
answers in the clear): that a program's format has them at each late message is not said here. (vi)
Errors are counts: a sending's number at or above the number of its seeds says nothing. (vii) The
chains end at the nested joint `N.over (over2 S₁ C)`: no block of the library starts there; the
library's own form is one signature `S.sum N` (Cb/Ld/LdSigSum.lean): a bridge is owed. (viii)
`send_step`'s first premise is knowledge soundness of all that stands in front: see the head of
Cb/Sub/SendBack.lean on what that asks.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.LateJoin
import Cb.Ld.LdSendFamProofs
import Ior.KnowColl

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR Reduction

variable {E : Type} [Field E]

/-- A joint at the pairs of tuples, at a fixed late tuple. -/
def sliceU {K X M U Wp : Type} {Ex : ExtSpec} (u : U) (B : Rels K X Ex ((M × U) × Wp)) :
    Rels K X Ex (M × Wp) :=
  ⟨fun x y w => B.rel x y ((w.1, u), w.2), fun a w => B.relR a ((w.1, u), w.2), B.on,
    fun w => B.core ((w.1, u), w.2)⟩

/-- B over the early signature, for each late tuple. -/
def over2 {K X U Wp : Type} {Ex : ExtSpec} (S₁ : Sig E) (B : Rels K X Ex ((S₁.Msg × U) × Wp)) :
    Rels K (X × S₁.Smp) (Ex.prod S₁.ext) (U × (S₁.Wit × Wp)) :=
  ⟨fun x y w => (S₁.over (sliceU w.1 B)).rel x y w.2,
    fun a w => (S₁.over (sliceU w.1 B)).relR a w.2,
    fun a => S₁.CF a.1.2 a.2.2 ∧ B.on (a.1.1, a.2.1),
    fun w => (S₁.over (sliceU w.1 B)).core w.2⟩

/-- `KnowAt` over a signature: soundness into the statements with the output joint's condition. -/
theorem lift_into {K X X' Wp : Type} {Ei Eo : ExtSpec} (S : Sig E) {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (S.Msg × Wp)} {B : Rels K X' Eo (S.Msg × Wp)} {ε : Err R.shape}
    (h : KnowAt R A B idW ε) :
    (R.keep S.Smp S.ext).red.KnowInto (S.over A).on (S.over B).on (S.over A).relR (S.over B).relR
      (fun _ _ w => w) ε :=
  knowInto_of_carry _ _ _ _ _ _ _ _ _ _ _
    (fun a τ b hb ha => by
      obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
      refine ⟨?_, h.onOut (a.1.1, a.2.1) τ (b.1.1, b.2.1) ha.2 h3⟩
      rw [h1, h2]
      exact ha.1)
    (sigLift_know E S K X X' Wp Wp Ei Eo R A B idW ε h.know)

/-- A block at the pairs of tuples, over the early signature: a block at the late tuples. -/
theorem over2_knowAt {K Y X'' U Wp : Type} {E₂ E₃ : ExtSpec} (S₁ : Sig E) {T : IOR Y E₂ X'' E₃}
    {Rl : Rels K Y E₂ ((S₁.Msg × U) × Wp)} {C : Rels K X'' E₃ ((S₁.Msg × U) × Wp)}
    {ε₂ : Err T.shape} (h₂ : KnowAt T Rl C idW ε₂) :
    KnowAt (T.keep S₁.Smp S₁.ext) (over2 S₁ Rl) (over2 S₁ C) idW ε₂ where
  point := h₂.point
  isLocal := IsLocal.keepE S₁.ext (isLocal_keepX h₂.isLocal S₁.Smp)
  onOut := fun a τ b ha hb => by
    obtain ⟨g1, g2, g3⟩ := keep_red_out T S₁.Smp S₁.ext a τ b hb
    refine ⟨?_, h₂.onOut (a.1.1, a.2.1) τ (b.1.1, b.2.1) ha.2 g3⟩
    rw [g1, g2]
    exact ha.1
  know := fun u =>
    sigLift_know E S₁ K Y X'' Wp Wp E₂ E₃ T (sliceU u Rl) (sliceU u C) idW ε₂
      fun m => h₂.know (m, u)

/-- ONE SENDING IN THE MIDDLE OF A CHAIN: whatever stands in front (K₀, ending at the joint A₂), the
sending of the family N, and a block T₂ that has `KnowAt` at the tuples of N. It may be used again
behind itself: its conclusion has the form of its first premise. -/
theorem send_step {K P WP Y₂ X₂ W₂ : Type} {E₂ E₃ : ExtSpec} (N : Sig E) (Sd : N.Seeds)
    (Ln : N.O → ℕ) {K₀ : Reduction P (Y₂ × E₂.Str)} {onP : P → Prop} {RP : P → WP → Prop}
    {e₀ : P → Tr K₀.shape → W₂ → WP} {ε₀ : Err K₀.shape} {A₂ : Rels K Y₂ E₂ W₂}
    {T₂ : IOR Y₂ E₂ X₂ E₃} {Rl₂ : Rels K Y₂ E₂ (N.Msg × W₂)} {C₂ : Rels K X₂ E₃ (N.Msg × W₂)}
    {ε₂ : Err T₂.shape} (dP : WP) (d₂ : W₂) (k₀ : K₀.KnowInto onP A₂.on RP A₂.relR e₀ ε₀)
    (h : KnowAt T₂ Rl₂ C₂ idW ε₂) (hon : ∀ b, A₂.on b → Rl₂.on b)
    (hseam : ∀ b u w, Rl₂.relR b (u, w) → A₂.relR b w) (hF : Sd.Fair)
    (hL : ∀ a, (N.om a).ListLE (Ln a)) (hE : ∀ a, (N.om a).Evades) :
    (K₀.seq ((ldSendFam N Sd Y₂ E₂).red.seq (T₂.keep N.Smp N.ext).red)).KnowInto
      onP (N.over C₂).on RP (N.over C₂).relR
      (Reduction.extSeq _ _ e₀ (Reduction.extSeq _ _ (fun _ _ w => w.2) (fun _ _ w => w) d₂) dP)
      (Err.app ε₀ (Err.app (s := (ldSendFam N Sd Y₂ E₂).shape) (ldSendFamErr N Sd Ln, (0, ())) ε₂))
    := by
  -- the sending: the witness grows by the late messages
  have k₂ := ldSendFam_into E N Sd K Y₂ W₂ W₂ E₂ A₂ (fun _ w => w) Ln hF hL hE
  -- the block behind, over the late signature; then the seam
  have k₃ : (T₂.keep N.Smp N.ext).red.KnowInto (N.over (N.pull A₂ fun _ w => w)).on
      (N.over C₂).on (N.over (N.pull A₂ fun _ w => w)).relR (N.over C₂).relR (fun _ _ w => w) ε₂ :=
    Know.conseq (lift_into N h) (fun _ ha => ⟨ha.1, hon _ ha.2⟩)
      (fun _ _ _ hw => ⟨hw.1, hseam _ _ _ hw.2⟩) fun _ _ h => h
  exact knowInto_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dP k₀
    (knowInto_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d₂ k₂ k₃)

/-- THE JOIN IN THE TRUE ORDER. -/
theorem true_order {K X Y X'' Wp : Type} {E₁ E₂ E₃ : ExtSpec} (S₁ N : Sig E) (Sd : N.Seeds)
    (Ln : N.O → ℕ) {R : IOR X E₁ Y E₂} {T : IOR Y E₂ X'' E₃} {A : Rels K X E₁ (S₁.Msg × Wp)}
    {V : Rels K Y E₂ (S₁.Msg × Wp)} {Rl : Rels K Y E₂ ((S₁.Msg × N.Msg) × Wp)}
    {C : Rels K X'' E₃ ((S₁.Msg × N.Msg) × Wp)} {ε₁ : Err R.shape} {ε₂ : Err T.shape}
    (d : S₁.Wit × Wp) (h₁ : KnowAt R A V idW ε₁) (h₂ : KnowAt T Rl C idW ε₂)
    (hon : ∀ b, V.on b → Rl.on b) (hseam : ∀ b m u wp, Rl.relR b ((m, u), wp) → V.relR b (m, wp))
    (hF : Sd.Fair) (hL : ∀ a, (N.om a).ListLE (Ln a)) (hE : ∀ a, (N.om a).Evades) :
    ((R.keep S₁.Smp S₁.ext).red.seq
        ((ldSendFam N Sd (Y × S₁.Smp) (E₂.prod S₁.ext)).red.seq
          ((T.keep S₁.Smp S₁.ext).keep N.Smp N.ext).red)).KnowInto
      (S₁.over A).on (N.over (over2 S₁ C)).on (S₁.over A).relR (N.over (over2 S₁ C)).relR
      (Reduction.extSeq _ _ (fun _ _ w => w)
        (Reduction.extSeq _ _ (fun _ _ w => w.2) (fun _ _ w => w) d) d)
      (Err.app ε₁ (Err.app (s := (ldSendFam N Sd (Y × S₁.Smp) (E₂.prod S₁.ext)).shape)
        (ldSendFamErr N Sd Ln, (0, ())) ε₂)) :=
  send_step N Sd Ln d d (lift_into S₁ h₁) (over2_knowAt S₁ h₂)
    (fun _ hb => ⟨hb.1, hon _ hb.2⟩) (fun _ _ _ hw => ⟨hw.1, hseam _ _ _ _ hw.2⟩) hF hL hE

/-- The same for a ledger on early and late entries: the seam is `late_holds`. The weights `a` are
read off R's output statement: they stand before the late messages are sent. -/
theorem late_true_order {J₁ J₂ K X X' X'' Wp : Type} [Fintype J₁] [Fintype J₂]
    {E₁ E₂ E₃ : ExtSpec} (S₁ N : Sig E) (Sd : N.Seeds) (Ln : N.O → ℕ)
    {R : IOR X E₁ (X' × Ledger E (J₁ ⊕ J₂)) E₂} {T : IOR (X' × Ledger E (J₁ ⊕ J₂)) E₂ X'' E₃}
    {A : Rels K X E₁ (S₁.Msg × Wp)} {B₀ : Rels K X' E₂ (S₁.Msg × Wp)}
    {C : Rels K X'' E₃ ((S₁.Msg × N.Msg) × Wp)} {ε₁ : Err R.shape} {ε₂ : Err T.shape}
    (d : S₁.Wit × Wp) (a : X' → J₂ → Aff E J₁) (msg₁ : S₁.Msg → J₁ → E) (ent : N.Msg → J₂ → E)
    (n : ℕ) (h₁ : KnowAt R A (virtJ B₀ a msg₁ n) idW ε₁)
    (h₂ : KnowAt T (realJ B₀ a msg₁ ent n) C idW ε₂) (hF : Sd.Fair)
    (hL : ∀ i, (N.om i).ListLE (Ln i)) (hE : ∀ i, (N.om i).Evades) :
    ((R.keep S₁.Smp S₁.ext).red.seq
        ((ldSendFam N Sd ((X' × Ledger E (J₁ ⊕ J₂)) × S₁.Smp) (E₂.prod S₁.ext)).red.seq
          ((T.keep S₁.Smp S₁.ext).keep N.Smp N.ext).red)).KnowInto
      (S₁.over A).on (N.over (over2 S₁ C)).on (S₁.over A).relR (N.over (over2 S₁ C)).relR
      (Reduction.extSeq _ _ (fun _ _ w => w)
        (Reduction.extSeq _ _ (fun _ _ w => w.2) (fun _ _ w => w) d) d)
      (Err.app ε₁ (Err.app
        (s := (ldSendFam N Sd ((X' × Ledger E (J₁ ⊕ J₂)) × S₁.Smp) (E₂.prod S₁.ext)).shape)
        (ldSendFamErr N Sd Ln, (0, ())) ε₂)) :=
  true_order S₁ N Sd Ln d h₁ h₂ (fun _ h => h)
    (fun b m u wp (hw : B₀.relR (b.1.1, b.2) (m, wp) ∧ Agree (a b.1.1) (msg₁ m) (ent u) ∧
        Ledger.Holds b.1.2 (Sum.elim (msg₁ m) (ent u))) =>
      (⟨hw.1, (late_holds (a b.1.1) b.1.2 (msg₁ m) (ent u) hw.2.1).1 hw.2.2⟩ :
        B₀.relR (b.1.1, b.2) (m, wp) ∧ Ledger.Holds (pullL (a b.1.1) b.1.2) (msg₁ m)))
    hF hL hE

end Cb.Sub
