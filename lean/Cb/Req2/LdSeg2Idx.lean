-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req2/LdSeg2Idx.lean: how a reduction whose relations also read the message that the index's
oracle encodes becomes a reduction between two stages (`LdStage.mvA`), whose relations read the
prover's messages and fix the index's message by the statement.

Definitions and theorems: auxiliary lemmas that connect Cb/Ld/LdWfIdx.lean (the index-lifting
rule), Cb/Req1/LdSegRefPsc.lean (a block at the base as a move of a stage),
Cb/Ld/LdLkpFormatBlindIdx.lean.
A block at the base is a `BkA` (Cb/Ld/LdLkpTreeP.lean): a reduction with its honest prover and
numbers; `BkA.Good` (between two relations) says that it is good for each fixed tuple of messages.
`idxAt C rc A` (Cb/Ld/LdWfIdx.lean) makes relations A on tuples (U, m) relations on m. Exact: U is
the message of the further witness's prover encoded index, whose encoding is the index's oracle and
whose record is rc's (`C.Enc`). Relaxed: the oracle decodes, with the record rc, to some U.
Knowledge soundness speaks of statements whose oracle has no collision at the record's seed and
that meet A's own condition (`A.on`).

Why: the fronts of the reference segment (Cb/Req1/LdSegFrontRef.lean)
read entries off the oracle messages alone (msg : S.Msg → J → E): keys, summands and the maps of
their sumchecks cannot read the encoded index, which is a further oracle. In this protocol's
technical report (lean/CREDITS.md)
a segment's sumchecks have index-linear maps. The blocks are good at the base for any type of
tuples; the index-lifting rule turns "for each tuple (U, m)" into "for each m, with U the decoding
of the statement".

Main names (b : a `BkA` on tuples (U, m)):
  `b.idx C`: the honest side runs b's on (message of its prover encoded index, m).
  `BkA.idx_good`: b keeps the record and copies the oracles, `b.Good A B` ⇒
    `(b.idx C).Good (idxAt C rc A) (idxAt C rc' B)`.
  `BkA.idx_sameOn`: b reads the entries in Rd only ⇒ so does `b.idx C`, the entries read off
    (message of the prover encoded index, messages).
  `D.tag tg`, `mm_tag`: the letters of an item "masked messages" with one more part tg w of the
    witness in the key, which no mask touches: claim, closed form and simulator do not read it; the
    item carries over.
  `idxMaskU C S D`: the letters of a block on tuples over a signature (`idxMask`), with the message
    of the prover encoded index in the key. Why: the key of `idxMask` is what the block reads of
    (U, m), cut to its reading; two witnesses with related keys could hold different U; then
    "overwriting this block's masks changes nothing that an earlier block reads" could fail for an
    earlier block that reads other entries of the index.
  `mvI_goodM`: under the hypotheses of its statement, a masked block on tuples is, as a link of a
    stage, a masked block with the letters `idxMaskU C S D`.
  `mvI_carry`: under the hypotheses of its statement, a fact whose overwriting changes no entry
    that the block reads (exactly: its premise `hk`) is fresh behind the move.

Limits: This file says nothing on any protocol. This file says nothing on blocks that read the
index's symbols.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefPsc
import Cb.Ld.LdWfIdxProofs
import Cb.Ld.LdLkpFormatBlindIdx

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

/-- A block on tuples (message of the index, messages) as a block on messages. -/
def BkA.idx {K M X₁ X₂ Wp : Type} (C : ConfigurationWithOutOfDomainSample) (b : BkA K (C.Msg × M) X₁ X₂ C.E0 Wp) :
    BkA K M X₁ X₂ C.E0 (C.PIdx × Wp) :=
  ⟨b.R, idxH C b.H, b.P⟩

section
variable {K M X₁ X₂ Wp : Type} (C : ConfigurationWithOutOfDomainSample) (b : BkA K (C.Msg × M) X₁ X₂ C.E0 Wp)

theorem BkA.idx_good (A : Rels K X₁ C.E0 ((C.Msg × M) × Wp)) (B : Rels K X₂ C.E0 ((C.Msg × M) × Wp))
    (rc : X₁ → C.Rec) (rc' : X₂ → C.Rec) (h1 : ∀ x y τ x', b.R.out x y τ = some x' → rc' x' = rc x)
    (h2 : ∀ y τ, b.R.imp y τ = y) (h : b.Good A B) :
    (b.idx C).Good (idxAt C rc A) (idxAt C rc' B) :=
  idxLift_goodAt C K X₁ X₂ M Wp Wp b.R b.H A B rc rc' (fun _ _ _ wp => wp) b.P h1 h2 h

theorem BkA.idx_plain (h : b.Plain) : (b.idx C).Plain := by
  refine ⟨h.copies, fun w x c ρ => ?_, h.budAll, fun w x => h.free (idxIn C w) x⟩
  show (((b.H.mapW (idxIn C) fun w o => (w.1, (w.2.1, o.2))).strat w x c).run ρ).2.2 = w
  rw [Honest.mapW_run, h.keepsW]
  rfl

theorem BkA.idx_sameOn {E J : Type} {msg : C.Msg × M → J → E}
    {Rd : J → Prop} (h : b.SameOn msg Rd) :
    (b.idx C).SameOnW (fun w => msg (w.2.1.1.1, w.1)) Rd := sameOnW_idx C h

end

/-- The letters with one more part of the witness in the key. -/
def _root_.Iop.IOR.MaskData.tag {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi : Type}
    (D : MaskData R Wi) {T : Type} (tg : Wi → T) : MaskData R Wi where
  Kc  := T × D.Kc
  kc  := fun w => (tg w, D.kc w)
  Xp  := D.Xp
  pub := D.pub
  Mk  := D.Mk
  put := fun M k => (k.1, D.put M k.2)
  Cl  := fun xp k => D.Cl xp k.2
  msg := fun k => D.msg k.2
  sim := D.sim

theorem mm_tag {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}
    {H : R.Honest Wi Wo} {D : MaskData R Wi} {T : Type} (tg : Wi → T) (h : H.MM D) :
    H.MM (D.tag tg) :=
  ⟨h.noOrc, h.free, h.run, fun xp k M hk => h.stable xp k.2 M hk,
    fun k xp ρ hk => h.law k.2 xp ρ hk⟩

theorem goodM_tag {K Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}
    {H : R.Honest Wi Wo} {A : Rels K Xi Ei Wi} {B : Rels K Xo Eo Wo}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : Nums K R} {D : MaskData R Wi} {T : Type}
    (tg : Wi → T) (h : GoodM R H A B ext P D) :
    GoodM R H A B ext P (D.tag tg) :=
  ⟨h.base, mm_tag tg h.mm, h.claim⟩

/-- The letters over a signature, with the index's message in the key. -/
def idxMaskU {E : Type} (C : ConfigurationWithOutOfDomainSample) (S : Sig E) {X X' Wp : Type} {R : IOR X C.E0 X' C.E0}
    (D : IOR.MaskData R ((C.Msg × S.Msg) × Wp)) :
    IOR.MaskData (R.keep S.Smp S.ext) (S.Wit × (C.PIdx × Wp)) :=
  (idxMask C S D).tag fun w => w.2.1.1.1

section
variable {E Kc : Type} [Field E] [Fintype E] (C : ConfigurationWithOutOfDomainSample) (S : Sig E) {St St' Wp : Type}
  (A : Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)) (B : Rels Kc St' C.E0 ((C.Msg × S.Msg) × Wp))
  (rc : St → C.Rec) (rc' : St' → C.Rec) (b : BkA Kc (C.Msg × S.Msg) St St' C.E0 Wp)

/-- the stage "A on tuples, the index decoded by the statement" -/
@[reducible] def idxStage : LdStage E Kc := ⟨S, St, C.E0, C.PIdx × Wp, idxAt C rc A⟩

/-- A masked block on tuples, as a link of a stage. -/
theorem mvI_goodM (D : MaskData b.R ((C.Msg × S.Msg) × Wp))
    (h1 : ∀ x y τ x', b.R.out x y τ = some x' → rc' x' = rc x) (h2 : ∀ y τ, b.R.imp y τ = y)
    (h : b.Good A B) (hm : b.H.MM D) (hc : ∀ x y w, A.rel x y w → D.Cl (D.pub x) (D.kc w)) :
    ((idxStage C S A rc).linkA (idxAt C rc' B) (b.idx C)).GoodM (idxMaskU C S D) :=
  ldSeg_sub_goodM E Kc (idxStage C S A rc) (idxStage C S B rc')
    ((idxStage C S A rc).linkA (idxAt C rc' B) (b.idx C)) (idxMaskU C S D)
    (goodM_tag _
      (idxLift_goodM E C S Kc St St' Wp Wp b.R b.H A B rc rc'
        (fun _ _ _ wp => wp) b.P D h1 h2 h hm hc))

/-- Under the hypotheses of its statement, a fact whose overwriting changes no entry that the block
reads (exactly: the premise `hk` below, which speaks of all pairs of witnesses whose readings by f
differ by the overwriting (`f.kc w' = f.put m (f.kc w)`)) is fresh behind the move. -/
theorem mvI_carry {J : Type} (hp : b.Plain) {msg : C.Msg × S.Msg → J → E} {Rd : J → Prop}
    (hs : b.SameOn msg Rd) (base : MaskFact (idxStage C S A rc).J.W → Prop)
    (f : MaskFact (idxStage C S A rc).J.W)
    (hk : ∀ w w' m, f.kc w' = f.put m (f.kc w) →
      ∀ j, Rd j → msg (w'.2.1.1.1, S.msgs w'.1) j = msg (w.2.1.1.1, S.msgs w.1) j) (hb : base f) :
    ((idxStage C S A rc).mvA (idxAt C rc' B) (b.idx C)).chain.FreshGiven base f :=
  (Chain.freshGiven_one _ _ _).2
    (Or.inr ⟨f.Kc, f.kc, f.put, hb,
        blind_of_sameOnW S (BkA.idx_plain C b hp) (BkA.idx_sameOn C b hs) f.kc f.Mk f.put hk⟩)

end
end Cb
