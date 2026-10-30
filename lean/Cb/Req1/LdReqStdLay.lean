-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStdLay.lean: the calculus of masks of a reference request at sendings that are
standard: "does not look", the one sender's two clauses at a crossing, and "laid down by the one
sending", from the hypotheses of `d.IsStdB`, `d.StdAt` and `Y.OK`. (not all hypotheses are named
here: see `Spec.ldReqStdLay_fresh`, `Spec.ldReqStdLay_new`)

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.
The reference request is the term `ldReqRef`; S is a reference segment (`LdRefS`):
Cb/Req1/LdReqRef.lean. A sending is a `d : LdSendD a` (Cb/Req1/LdSegKit.lean). Wide facts:
`LdStage.wideFact` (Cb/Req1/LdSegCarry.lean); `Honest.Fresh`: Ior/KnowCollRulesMask.lean; `S.New`:
Cb/Req1/LdReqRefLay.lean.
Cb/Req1/LdReqStdFresh.lean has these statements at the term `LdSendD.std`. The records of the
reference request have a sending d as a parameter, with one equation that says which term it is
(Cb/Req1/LdReqProtoStd.lean: `d.IsStd F`). Here the statements are carried along that equation, in
the notation of Cb/Req1/LdReqRefLay.lean.

Main names:
  `d.StdAt F Y dat rst bk₀ w0`: the equation, its parameters named.
  `d.IsStdB F Rd Rr own`: `d.IsStd F`'s clauses and: the data map does not look
    (`DatBlind a dat Rd Rr own`).
  `Spec.ldReqStdLay_noLook`: `d.IsStdB F Rd Rr own` ⇒ `d.IsStd F ∧ d.NoLook Rd Rr own`.
  `Spec.ldReqStdLay_one`: `d.IsStdB F Rd Rr own` ⇒ `d.D.Laws` (the move's extractor) ∧ "alike ⇒ the
    same messages for all coins, the same further witness handed on". `Spec.ldReqStdLay_cross`: at
    `S.Qc.snd` and the sets of `Spec.ldReqRefLay_cross` these are its two clauses on `S.Qc.Sn`.
  `Spec.ldReqStdLay_fresh`: `d.StdAt ..`, `Y.OK d.t`, pl injective ⇒ d's link is `Fresh` for the
    wide fact with own entries the free entries at pl (the reading forgets all pads and all encoding
    randomness of the new family; old part arbitrary).
  `Spec.ldReqStdLay_new`: `S.New g` for that fact g at `S.Qc.snd`, from: the equation, `Y.OK`, pl
    injective, and one condition on the cut: `S.Qc.cutN` is the same at new messages that agree at
    all entries that are no pads and not own.

Limits: Nothing new is proved in this file: its definitions and statements are put together from
those of other files. They are about data structures of this library. This file says nothing on
the form in which a fact can cross a later closing (masks in one
member: Cb/Ld/LdSendStdVis.lean). That the conditions can be met is not shown here. Users of
`Spec.ldReqStdLay_cross` and `Spec.ldReqStdLay_noLook`: Cb/Req1/LdReqRefLayStd.lean (generic; no
toy).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqStdFresh
import Cb.Req1.LdReqProtoStd
import Cb.Req1.LdReqRefLay

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable (F : Type) {E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Which term d is. -/
def LdSendD.StdAt {a : LdStage E Kc} (d : LdSendD a) (Y : d.N.StdL F)
    (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
    (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) : Prop :=
  d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0

/-- The sending is the standard one, and its data map does not look. -/
def LdSendD.IsStdB {a : LdStage E Kc} (d : LdSendD a) (Rd : a.S.Ent → Prop)
    (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) : Prop :=
  ∃ (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp),
    d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 ∧
    Y.OK d.t ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧
    (∀ i, (d.N.om i).C.Laws) ∧
    d.Sd.Fair ∧
    (∀ i, (d.N.om i).ListLE (d.L i)) ∧
    (∀ i, (d.N.om i).Evades) ∧
    DatBlind a dat Rd Rr own

end

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldReqStdLay_noLook : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop),
    d.IsStdB F Rd Rr own → d.IsStd F ∧ d.NoLook Rd Rr own

def ldReqStdLay_one : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop),
    d.IsStdB F Rd Rr own →
    d.D.Laws (a.S.backN d.N d.bk) ∧
    ∀ w w' : a.W, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
      (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, d.D.put w' k = d.D.put w k) ∧ (d.D.rest w').2 = (d.D.rest w).2

def ldReqStdLay_fresh : Prop :=
  ∀ (a : LdStage E Kc) (d : LdSendD a) (Y : d.N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E)
      (rst : a.Wp → d.Wp') (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (I : Type)
      [Fintype I] [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    d.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK d.t →
    d.link.H.Fresh a.J.rels.rel d.link.P.bud
      (d.tgt.wideFact (a.S.sumP d.N RdOld Y.NoPad) (a.S.sumO d.N RrOld fun _ => False)
        (a.S.sumP d.N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valP pl M)).kc
      (I → E) (d.tgt.wideFact (a.S.sumP d.N RdOld Y.NoPad) (a.S.sumO d.N RrOld fun _ => False)
        (a.S.sumP d.N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV d.N (fun _ => 0) (Y.valP pl M)).put

/-- The two clauses of the crossing on the one sender. -/
def ldReqStdLay_cross : Prop :=
  ∀ (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a)
      (W : LdRefW S.A) (own : S.A.Xa.Q.D.S.Ent → Prop),
    S.Qc.snd.IsStdB F (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2))
      (fun o => W.Rr2 o.1.1)
      (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own))) →
    S.Qc.Sn.Laws (S.K.R.c1.fold.tgt.S.backN S.Qc.N S.Qc.snd.bk) ∧
    ∀ w w' : S.K.R.c1.fold.tgt.W,
      S.K.R.c1.fold.tgt.S.Alike
        (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2))
        (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))
        (S.K.R.c1.fold.tgt.S.msgs w.1) (S.K.R.c1.fold.tgt.S.msgs w'.1) →
      (∀ o : S.K.R.c1.fold.tgt.S.O, W.Rr2 o.1.1 → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, S.Qc.Sn.put w' k = S.Qc.Sn.put w k) ∧ (S.Qc.Sn.rest w').2 = (S.Qc.Sn.rest w).2

/-- Laid down by the one sending. (not all hypotheses are named here: see the statement below) -/
def ldReqStdLay_new : Prop :=
  ∀ (Ix : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc Ix a) (Y : S.Qc.N.StdL F)
      (dat : S.K.R.c1.fold.tgt.S.Wit × S.K.R.c1.fold.tgt.Wp → ∀ i, Y.Dt i → E)
      (rst : S.K.R.c1.fold.tgt.Wp → S.Qc.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → S.Qc.Wp' → S.K.R.c1.fold.tgt.Wp)
      (w0 : S.K.R.c1.fold.tgt.S.Wit × S.K.R.c1.fold.tgt.Wp) (I : Type) [Fintype I]
      [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a)
      (RdOld : S.K.R.c1.fold.tgt.S.Ent → Prop) (RrOld : S.K.R.c1.fold.tgt.S.O → Prop),
    S.Qc.snd.StdAt F Y dat rst bk₀ w0 → Function.Injective pl → Y.OK S.Qc.tN →
    (∀ m m' : S.Qc.N.Msg, (∀ n : S.Qc.N.Ent, Y.NoPad n → ¬ Y.ownP pl n → m' n.1 n.2 = m n.1 n.2) →
      S.Qc.cutN m' = S.Qc.cutN m) →
    S.New (S.Qc.loc.tgt.wideFact (S.K.R.c1.fold.tgt.S.sumP S.Qc.N RdOld Y.NoPad)
        (S.K.R.c1.fold.tgt.S.sumO S.Qc.N RrOld fun _ => False)
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => S.K.R.c1.fold.tgt.S.sumV S.Qc.N (fun _ => 0) (Y.valP pl M))

end
end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldReqStdLay_noLook : Spec.ldReqStdLay_noLook F E Kc := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Rd Rr own ⟨Y, dat, rst, bk₀, w0, h, h1, h2, h3, h4, h5, h6, hd⟩
  refine ⟨⟨Y, dat, rst, bk₀, w0, h, h1, h2, h3, h4, h5, h6⟩, ?_⟩
  rw [h]
  exact stdSend_noLook F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own hd

theorem ldReqStdLay_one : Spec.ldReqStdLay_one F E Kc := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Rd Rr own ⟨Y, dat, rst, bk₀, w0, h, h1, h2, -, -, -, -, hd⟩
  rw [h]
  exact stdSend_one F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own h1 h2 hd

theorem ldReqStdLay_freshAux (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type)
    (bk : N.Msg → Wp' → a.Wp) (D : N.Sender (a.S.Wit × a.Wp) (a.S.Wit × Wp')) (L t : N.O → ℕ)
    (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
    (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (I : Type) [Fintype I]
    [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a) (RdOld : a.S.Ent → Prop)
    (RrOld : a.S.O → Prop) (hb : bk = fun m r => bk₀ (Y.dataOf m) r)
    (hD : D = Y.snd dat (fun w => (w.1, rst w.2)) w0) (hpl : Function.Injective pl) (hY : Y.OK t) :
    (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).link.H.Fresh a.J.rels.rel
      (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).link.P.bud
      ((⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).tgt.wideFact (a.S.sumP N RdOld Y.NoPad)
        (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M)).kc
      (I → E) ((⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a).tgt.wideFact (a.S.sumP N RdOld Y.NoPad)
        (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M)).put := by
  subst hb hD
  exact stdSend_many F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 I pl RdOld RrOld hpl hY

theorem ldReqStdLay_fresh : Spec.ldReqStdLay_fresh F E Kc := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Y dat rst bk₀ w0 I _ _ _ pl RdOld RrOld h hpl hY
  have h' : (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a) = LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0 :=
    h
  unfold LdSendD.std at h'
  simp only [LdSendD.mk.injEq, heq_eq_eq, true_and, and_true] at h'
  exact ldReqStdLay_freshAux
    F E Kc a N Sd Wp' bk D L t Y dat rst bk₀ w0 I pl RdOld RrOld h'.1 h'.2 hpl hY

theorem ldReqStdLay_cross : Spec.ldReqStdLay_cross F E Kc := fun _ _ S _ _ h =>
  ldReqStdLay_one F E Kc _ S.Qc.snd _ _ _ h

theorem ldReqStdLay_new : Spec.ldReqStdLay_new F E Kc := by
  intro Ix a S Y dat rst bk₀ w0 I _ _ _ pl RdOld RrOld h hpl hY hcut
  refine ⟨ldReqStdLay_fresh F E Kc _ S.Qc.snd Y dat rst bk₀ w0 I pl RdOld RrOld h hpl hY,
    fun w w' M hk => ?_⟩
  have hA := (segWide_alike S.Qc.loc.tgt _ _ _ (I → E) _ w w' M hk).1
  exact hcut _ _ fun n h1 h2 => hA ⟨.inr n.1, n.2⟩ h1 h2

end
end Cb
