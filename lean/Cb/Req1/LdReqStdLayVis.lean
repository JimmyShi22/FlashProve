-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStdLayVis.lean: the calculus of masks of a reference request at sendings that are
standard: "laid down" in the form that can cross a closing; and "laid after the first sending" in
both forms.

Statements (each a `Prop` in `Cb.Spec`) and proofs: wiring; no text is rendered.
The reference request is the term `ldReqRef`; S is a reference segment (`LdRefS`):
Cb/Req1/LdReqRef.lean. A sending is a `d : LdSendD a` (Cb/Req1/LdSegKit.lean).
`d.StdAt F Y dat rst bk₀ w0` (Cb/Req1/LdReqStdLay.lean) says that d equals the term `LdSendD.std`
(Cb/Obj/LdObjectSenders.lean) at a layout `Y : d.N.StdL F` (Cb/Ld/LdSendStdL.lean); `d.IsStd F`
(Cb/Req1/LdReqProtoStd.lean) asks more. Wide facts: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean);
`Honest.Fresh`: Ior/KnowCollRulesMask.lean; `S.New`: Cb/Req1/LdReqRefLay.lean.
It continues Cb/Req1/LdReqStdLay.lean (the form "masks in any members, the reading forgets all pads
and all encoding randomness of the new family").
The other form (Cb/Ld/LdSendStdVis.lean): the masks lie in one member o; the reading shows all
entries but o's pads and the encoding randomness of all members but o. A fact with this reading can
cross a closing whose group holds the other new members whole: the case of the one message that
holds the own masks of the batchings of tensor rows on the encoded index.

Main names:
  `Spec.ldReqStdLay_freshVis`: `d.StdAt ..`, `pl : I → Y.Fr o` injective, `Y.OK d.t` ⇒ d's link is
    `Fresh` for that wide fact (old part arbitrary).
  `Spec.ldReqStdLay_newVis`: `S.Qc.snd.StdAt ..`, pl injective, `Y.OK S.Qc.tN` ⇒ `S.New` of that
    fact at `S.Qc.snd`, with one condition on the cut: `S.Qc.cutN` is the same at new messages that
    agree at all entries that the reading shows and that are not own.
  `Spec.ldReqStdLay_baseMany`, `Spec.ldReqStdLay_baseVis`: `d.StdAt ..`, pl injective, `Y.OK d.t` ⇒
    behind the first sending, no further first move: `ldReqBase d (.nil _) g`
    (Cb/Req1/LdReqRefNil.lean) for g the wide fact of either form.

Limits: this file says nothing on masks of one block in several members, in a form that crosses.
That the conditions can be met is not shown here; users of _newVis: none.
-/
import Cb.Req1.LdReqStdLay
import Cb.Ld.LdSendStdVis
import Cb.Req1.LdReqRefNil

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldReqStdLay_freshVis : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E)
      (rst : a.Wp → d.Wp') (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp)
      (o : d.N.O) (I : Type) [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    d.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK d.t →
    d.link.H.Fresh a.J.rels.rel d.link.P.bud
      (d.tgt.wideFact (a.S.sumP d.N RdOld (Y.rdBut o)) (a.S.sumO d.N RrOld (Y.rrBut o))
        (a.S.sumP d.N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valO o pl M)).kc
      (I → E) (d.tgt.wideFact (a.S.sumP d.N RdOld (Y.rdBut o)) (a.S.sumO d.N RrOld (Y.rrBut o))
        (a.S.sumP d.N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valO o pl M)).put

def ldReqStdLay_newVis : Prop :=
  ∀ (Ix : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc Ix a) (Y : S.Qc.N.StdL F)
      (dat : S.K.R.c1.fold.tgt.S.Wit × S.K.R.c1.fold.tgt.Wp → ∀ i, Y.Dt i → E)
      (rst : S.K.R.c1.fold.tgt.Wp → S.Qc.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → S.Qc.Wp' → S.K.R.c1.fold.tgt.Wp)
      (w0 : S.K.R.c1.fold.tgt.S.Wit × S.K.R.c1.fold.tgt.Wp) (o : S.Qc.N.O) (I : Type)
      [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o)
      (RdOld : S.K.R.c1.fold.tgt.S.Ent → Prop) (RrOld : S.K.R.c1.fold.tgt.S.O → Prop),
    S.Qc.snd.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK S.Qc.tN →
    (∀ m m' : S.Qc.N.Msg,
      (∀ n : S.Qc.N.Ent, Y.rdBut o n → ¬ Y.ownO o pl n → m' n.1 n.2 = m n.1 n.2) →
      S.Qc.cutN m' = S.Qc.cutN m) →
    S.New (S.Qc.loc.tgt.wideFact (S.K.R.c1.fold.tgt.S.sumP S.Qc.N RdOld (Y.rdBut o))
        (S.K.R.c1.fold.tgt.S.sumO S.Qc.N RrOld (Y.rrBut o))
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => S.K.R.c1.fold.tgt.S.sumV S.Qc.N (fun _ => 0) (Y.valO o pl M))

def ldReqStdLay_baseMany : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E)
      (rst : a.Wp → d.Wp') (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (I : Type)
      [Fintype I] [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    d.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK d.t →
    ldReqBase d (.nil _)
      (d.tgt.wideFact (a.S.sumP d.N RdOld Y.NoPad) (a.S.sumO d.N RrOld fun _ => False)
        (a.S.sumP d.N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valP pl M))

def ldReqStdLay_baseVis : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E)
      (rst : a.Wp → d.Wp') (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp)
      (o : d.N.O) (I : Type) [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    d.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK d.t →
    ldReqBase d (.nil _)
      (d.tgt.wideFact (a.S.sumP d.N RdOld (Y.rdBut o)) (a.S.sumO d.N RrOld (Y.rrBut o))
        (a.S.sumP d.N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valO o pl M))

end
end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldReqStdLay_freshVisAux (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
    (bk : N.Msg → Wp' → a.Wp) (D : N.Sender (a.S.Wit × a.Wp) (a.S.Wit × Wp')) (L t : N.O → ℕ)
    (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
    (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (o : N.O) (I : Type)
    [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o) (RdOld : a.S.Ent → Prop)
    (RrOld : a.S.O → Prop) (hb : bk = fun m r => bk₀ (Y.dataOf m) r)
    (hD : D = Y.snd dat (fun w => (w.1, rst w.2)) w0) (hpl : Function.Injective pl) (hY : Y.OK t) :
    (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).link.H.Fresh a.J.rels.rel
      (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).link.P.bud
      ((⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).tgt.wideFact (a.S.sumP N RdOld (Y.rdBut o))
        (a.S.sumO N RrOld (Y.rrBut o)) (a.S.sumP N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M)).kc
      (I → E) ((⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).tgt.wideFact (a.S.sumP N RdOld (Y.rdBut o))
        (a.S.sumO N RrOld (Y.rrBut o)) (a.S.sumP N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M)).put := by
  subst hb hD
  exact stdL_vis a N Sd Wp' L t Y dat rst bk₀ w0 o I pl RdOld RrOld hpl hY

theorem ldReqStdLay_freshVis : Spec.ldReqStdLay_freshVis F E Kc := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Y dat rst bk₀ w0 o I _ _ pl RdOld RrOld h hpl hY
  have h' : (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a) = LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0 :=
    h
  unfold LdSendD.std at h'
  simp only [LdSendD.mk.injEq, heq_eq_eq, true_and, and_true] at h'
  exact ldReqStdLay_freshVisAux
    F E Kc a N Sd Wp' bk D L t Y dat rst bk₀ w0 o I pl RdOld RrOld h'.1 h'.2 hpl hY

theorem ldReqStdLay_newVis : Spec.ldReqStdLay_newVis F E Kc := by
  intro Ix a S Y dat rst bk₀ w0 o I _ _ pl RdOld RrOld h hpl hY hcut
  refine ⟨ldReqStdLay_freshVis F E Kc _ S.Qc.snd Y dat rst bk₀ w0 o I pl RdOld RrOld h hpl hY,
    fun w w' M hk => ?_⟩
  have hA := (segWide_alike S.Qc.loc.tgt _ _ _ (I → E) _ w w' M hk).1
  exact hcut _ _ fun n h1 h2 => hA ⟨.inr n.1, n.2⟩ h1 h2

theorem ldReqStdLay_baseMany : Spec.ldReqStdLay_baseMany F E Kc := by
  intro a d Y dat rst bk₀ w0 I _ _ _ pl RdOld RrOld h hpl hY
  unfold ldReqBase
  rw [LdProg.After]
  exact ldReqStdLay_fresh F E Kc a d Y dat rst bk₀ w0 I pl RdOld RrOld h hpl hY

theorem ldReqStdLay_baseVis : Spec.ldReqStdLay_baseVis F E Kc := by
  intro a d Y dat rst bk₀ w0 o I _ _ pl RdOld RrOld h hpl hY
  unfold ldReqBase
  rw [LdProg.After]
  exact ldReqStdLay_freshVis F E Kc a d Y dat rst bk₀ w0 o I pl RdOld RrOld h hpl hY

end
end Cb
