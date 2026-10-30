-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupPackFmt.lean: this file is for toys (a toy: a small example instance). A whole segment
from a bundle has the format of a preamble if its body has, the bridge's evader evades and the
number tl of locations is at most t; and zero knowledge asks of it what it asks of the body, beside
its hypotheses.

In standard terms: book-keeping for sequential composition: under the hypotheses of
`gPack_seg1_fmt`, the composed reduction of Cb/Ld/LdGroupPack.lean has, between its first and its
last joint, the property (`Fmt`) that the theorems on a request's whole chain ask of each of its
parts.

One definition, statements as theorems, proofs: an assembly. Generic.

Main names:
  `pk.qIn .. q₂`: the demand before the closing: the sources of at most t common long positions of
    the group, and of what q₂ allows afterwards of the further oracles and of the messages that are
    kept and not held. The batching and the step (parts of `pk.seg1`: `GPack.seg1`,
    Cb/Ld/LdGroupPack.lean) do not change it.
  `gPack_seg1_fmt`: `body.Fmt φ (.. pk.qIn ..)`, the bridge's evader evades, tl ≤ t ⇒
    `(pk.seg1 ..).Fmt φ` (after the locations: q₂, and at most t₂ long positions of each new
    message), for any place i of an index among the further oracles, any rc, px.
  `gPack_qIn_le`: that demand in numbers (Cb/Ld/LdGroupNewFmt.lean: `bSrc`); see its statement.
  `gPack_seg1_zk`: `body.Zk base` ⇒ `(pk.seg1 ..).Zk base`.
In both statements on `pk.seg1` the body's moves are sendings, sub-protocols or steps (`hT`, an
argument of `pk.seg1`).

Limits: this file does not say that a body has the format, or which masks are fresh after the
segment (Cb/Req1/LdSegWholeAfter.lean, Cb/Req1/LdSegCarryClose.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupPack
import Cb.Req1.LdSegRefLkpPreProofs
import Cb.Req1.LdSegWholeZk

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {mem kp : S.O → Prop}
  [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ}
  {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ} (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B) (Zb : Evader E (pk.G.Row Unit))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {a : LdStage E Kc}
  (body : LdProg a (pk.cl1 Sb sl Z Zb A₀).bat.src)
  (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step) (dw : S.Wit × Wp)
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp)
  (tl : ℕ) {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St₀ → Rc) (px : Wp → Pw)
  (q₂ : Finset
      (E₀.prod (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.ext).Pos → Prop)

/-- the demand before the closing: the sources of at most t common long positions of the group, and
of what q₂ allows -/
abbrev GPack.qIn : Finset (E₀.prod S.ext).Pos → Prop :=
  pk.Hd.qSrc (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ q₂ t

open Classical in
/-- For a body whose moves are sendings, sub-protocols or steps (`hT`): the segment has the format,
if its body has it up to the demand before the closing (`hb`), the bridge's evader evades (`hZb`)
and tl ≤ t (`ht`). -/
theorem gPack_seg1_fmt (φ : JFmt Kc E0 Rc Pw a.J)
    (hb : body.Fmt φ
      ((pk.cl1 Sb sl Z Zb A₀).bat.src.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂)))
    (hZb : Zb.OK) (ht : tl ≤ t) :
    (pk.seg1 Sb sl Z Zb A₀ body hT dw w0 tl).Fmt φ
      ((pk.close (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ w0 tl).loc.tgt.fmt
        i (fun st => rc st.2) px
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum
          pk.V.N.N₀ q₂ fun _ => t₂)) := by
  obtain ⟨φb, φb₁, φc, φs, e1, e2, h3, h4, h5⟩ :=
    stdNew_seg_fmt pk.V (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ i rc px q₂ pk.hc dw
      d t Lst mC mS mW L w0 L₂ t₂ tl pk.ok pk.hyp hZb pk.list pk.fits pk.new ht
  obtain rfl := (LdProg.fmt_nil _ _ _).1 e1
  obtain rfl := (LdProg.fmt_nil _ _ _).1 e2
  refine ⟨_, _, φc, φs, hb, ?_, h3, h4, h5⟩
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨(pk.cl1 Sb sl Z Zb A₀).bat.tgt.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂),
      (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩,
      ?_⟩
  · exact ldFmt_bat E Kc E0 Rc Pw (pk.cl1 Sb sl Z Zb A₀).bat i rc px _
  · exact ldStepF_fmt S _ _ _ i _ _ px _ fun _ => rfl

open Classical in
/-- The demand before the closing, in numbers: if q₂ allows q₀ of the further oracles and at most b₂
a long positions of each message that is kept and not held, then before the closing: q₀, and of
each oracle message at most t if it is a member, plus b₂ if it is kept and not held. -/
theorem gPack_qIn_le (q₀ : Finset E₀.Pos → Prop)
    (b₂ : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.O → ℕ)
    (h2 : ∀ U₂,
      q₂ U₂ → (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qFam q₀ b₂ U₂)
    (W : Finset (E₀.prod S.ext).Pos) (hW : pk.qIn Sb sl Z Zb A₀ q₂ W) :
    S.qFam q₀ (pk.Hd.bSrc (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ t b₂) W :=
  ldGroup_qSrc_le _ _ Zb A₀ q₂ t q₀ b₂ h2 W hW

/-- For a body whose moves are sendings, sub-protocols or steps (`hT`): zero knowledge asks of the
segment what it asks of the body, beside its hypotheses. -/
theorem gPack_seg1_zk (base : MaskFact a.J.W → Prop) (hb : body.Zk base) :
    (pk.seg1 Sb sl Z Zb A₀ body hT dw w0 tl).Zk base :=
  ldSegWholeZk_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ base hb

end
end Cb
