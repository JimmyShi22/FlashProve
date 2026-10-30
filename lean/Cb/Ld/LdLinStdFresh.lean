-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinStdFresh.lean: under the hypotheses listed below, with standard senders, masks at any
free entries of the three families of the test for linear constraints are fresh after the whole
core: no hypothesis on a sender is left but `T.Places` and `T.YW.OK tW`, `T.YU.OK tU`, `T.YO.OK tO`,
and whatever the arguments hold as proofs.

The file is about the honest prover's three sendings in the test for linear constraints, a proximity
test with claims on the encoded index. A layout (`Sig.StdL`, Cb/Ld/LdSendStdL.lean) divides the
entries of each member's message into data entries, free entries and pad entries.
W, G_u and Ω are oracle messages, each sent in a family of its own (Cb/Ld/LdLin.lean): W holds w =
gᵀ·(index matrix); G_u holds the whole folded full message u; Ω holds ω = (index matrix)·eq(ψ*, ·).

One definition (`Sig.StdL.offAt`), statements and proofs (an assembly). Fresh: `Chain.FreshFor`
(Ior/KnowCollRulesChain.lean) for one instance, `ChainV.FreshForV` (Cb/Ld/LdLinChainVMask.lean) for
sets of slots.
Cb/Ld/LdLinChainFresh.lean (one instance) and Cb/Ld/LdLinChainVFresh.lean (sets of slots) show that,
under the hypotheses of their statements, masks which ride in the family sent with W, with G_u or
with Ω are fresh after the core, from conditions on the senders: a split of the coins with its three
laws, "the encoder hides", the later senders' laws, `Apart`.
Here the senders are the standard ones (`T.snd`, Cb/Ld/LdLinStd.lean), the masks stand at any
injective family pl of free entries of the family (in whichever members), and all these conditions
are theorems (`stdL_own`, Cb/Ld/LdSendStdOwn.lean; `stdL_all`, Cb/Ld/LdSendStdL.lean;
`ldLinStd_apart`, Cb/Ld/LdLinStd.lean); what is asked: a nonempty ι, `Function.Injective pl`, in
`Spec.ldLinStdV_freshU` values of `P.X2` and `P.E1.Str`, in `Spec.ldLinStdV_freshO` of `P.X4` and
`P.E4.Str`, `T.Places` and the three layouts' conditions (the format's law, the layout, the sample
is private under the pad, the encoder hides t positions). Nothing else but whatever the arguments
hold as proofs.
The reading of the family that holds the masks: all entries of its messages that are no pads
(`Y.rdNoPad`, for a layout Y; Cb/Ld/LdSendStdOwn.lean); the overwriting: the entries at pl
(`Y.putAt pl`).

Main names (all under what is asked above):
  `Spec.ldLinStdC_freshW`, `Spec.ldLinStdC_freshU`, `Spec.ldLinStdC_freshO`: one instance: the
    readings of Cb/Ld/LdLinChainFresh.lean at this rd (`Y.rdNoPad`).
  `Spec.ldLinStdV_freshW`: sets of slots, a slot's masks in W's family.
  `Spec.ldLinStdV_freshU`, `Spec.ldLinStdV_freshO`: sets of slots, shared masks in G_u's, in Ω's
    family. A slot reads of that family's messages the entries that are no pads and not at pl
    (`offAt`).

Notation: `T.Places` (Cb/Ld/LdLinStd.lean): the places of the test are data entries of the named
members; the slots: j : `Fin N`, for the N : ℕ of `Spec.ldLinStdV_freshW`, `Spec.ldLinStdV_freshU`
and `Spec.ldLinStdV_freshO` (`BTr`, Iop/Batch.lean).

Limits: this file says nothing on a closing's own links. That layouts with these conditions exist is
not said here (Cb/Ld/LdSendStdMFree.lean: `stdMFamF_ok`, which has the `OK` of one layout from
`(M a).OK (L a) (t a)` for every member a).
(1) and (2) in the head of Cb/Ld/LdLinChainVFresh.lean hold here too: "given all that is shown to a
set of slots together" is the form stated here for sets of slots; this protocol's technical report
(lean/CREDITS.md) has a form of its lemma on masks sent in advance for sets of instances; whether it
is the same is not held here; and the readings forget the encoding randomness of the whole family,
which is narrower than that lemma's hypothesis (Cb/Ld/LdSendFreshVis.lean has the wider theorem; it
is not used here).
"Mask coordinates are pairwise disjoint, and none is a pad" holds by type and by
`Function.Injective pl`: pl is an injective family of free entries, and a free entry is neither a
pad nor a data entry.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinStd
import Cb.Ld.LdSendStdOwn
import Cb.Ld.LdLinChainVFresh

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- what is read not at pl -/
def Sig.StdL.offAt {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {N : Sig E} (Y : N.StdL F) {I W' : Type} (pl : I → Σ a, Y.Fr a) (k : (N.Ent → E) × W') :
    {n : N.Ent // ∀ i, n ≠ Y.entF (pl i)} → E :=
  fun n => k.1 n.1

theorem Sig.StdL.offAt_putAt {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {N : Sig E} (Y : N.StdL F) {I W' : Type} (pl : I → Σ a, Y.Fr a)
    (M : I → E) (k : (N.Ent → E) × W') :
    Y.offAt pl (Y.putAt pl M k) = Y.offAt pl k :=
  funext fun n => Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => n.2 i hi.symm

section
variable {F E ι κ J Y : Type}
  [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F)

/-- the later senders' laws and "the encoder hides", from places and layouts (`hP`; `hW`, `hU`,
`hO`) -/
theorem LdLinP.Std.sndLaws (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
    {tW : P.NW.O → ℕ} {tU : P.NU.O → ℕ} {tO : P.NO.O → ℕ} (hP : T.Places) (hW : T.YW.OK tW)
    (hU : T.YU.OK tU) (hO : T.YO.OK tO) :
    ((T.snd LW LU LO tW tU tO).dU.Laws P.backU ∧ (T.snd LW LU LO tW tU tO).dO.Laws P.backO) ∧
    (T.snd LW LU LO tW tU tO).dW.Nn.Hides (P.NW.budT tW) ∧
    (T.snd LW LU LO tW tU tO).dU.Nn.Hides (P.NU.budT tU) ∧
    (T.snd LW LU LO tW tU tO).dO.Nn.Hides (P.NO.budT tO) := by
  obtain ⟨-, -, -, -, -, dW, -⟩ :=
    stdL_all F E P.NW T.YW tW P.WA P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0) hW
  obtain ⟨-, aU, -, bU, -, dU, -⟩ :=
    stdL_all F E P.NU T.YU tU P.W2 P.W1 T.datU (fun w => w.2) (fun _ => 0, T.w1) hU
  obtain ⟨-, aO, -, bO, -, dO, -⟩ :=
    stdL_all F E P.NO T.YO tO P.W4 P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3) hO
  refine ⟨⟨bU P.backU fun w k => Prod.ext (funext fun c => ?_) rfl,
      bO P.backO fun w k => Prod.ext (funext fun c => ?_) rfl⟩,
    dW, dU, dO⟩
  · show (T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).upM
        ((T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).put w k) P.iU (P.lU c) = w.1 c
    rw [hP.lU c, aU w k P.iU (T.qU c)]
    show (T.pU P.iU (T.qU c)).elim 0 w.1 = w.1 c
    rw [hP.hU c]
    rfl
  · show (T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).upM
        ((T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).put w k) P.iO (P.lO c) = w.1 c
    rw [hP.lO c, aO w k P.iO (T.qO c)]
    show (T.pO P.iO (T.qO c)).elim 0 w.1 = w.1 c
    rw [hP.hO c]
    rfl

end

namespace Spec
section
variable (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype ι]
  [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- One instance: masks in the family of W. -/
def ldLinStdC_freshW : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (I : Type) [Fintype I]
      [DecidableEq I] (pl : I → Σ a, T.YW.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chain on0 (T.snd LW LU LO tW tU tO) εf).FreshFor
      (fun v : P.W5 => (v.1, v.2.1, T.YW.rdNoPad (P.NW.msgs v.2.2.1) v.2.2.2)) (I → E)
      (fun M k => (k.1, k.2.1, T.YW.putAt pl M k.2.2))

/-- One instance: masks in the family of G_u. -/
def ldLinStdC_freshU : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (I : Type) [Fintype I]
      [DecidableEq I] (pl : I → Σ a, T.YU.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chain on0 (T.snd LW LU LO tW tU tO) εf).FreshFor
      (fun v : P.W5 => (v.1, T.YU.rdNoPad (P.NU.msgs v.2.1) v.2.2))
      (I → E) (fun M k => (k.1, T.YU.putAt pl M k.2))

/-- One instance: masks in the family of Ω. -/
def ldLinStdC_freshO : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (I : Type) [Fintype I]
      [DecidableEq I] (pl : I → Σ a, T.YO.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chain on0 (T.snd LW LU LO tW tU tO) εf).FreshFor
      (fun v : P.W5 => T.YO.rdNoPad (P.NO.msgs v.1) v.2) (I → E) (T.YO.putAt pl)

/-- Sets of slots: a slot's masks in the family of W. -/
def ldLinStdV_freshW : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (qa : Finset P.Ea.Pos → Prop)
      (I : Type) [Fintype I] [DecidableEq I] (pl : I → Σ a, T.YW.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chainV (T.snd LW LU LO tW tU tO) qa N on0 εf).FreshForV (fun s : P.Sh6 => s)
      (fun v : P.W5 => (v.1, v.2.1, T.YW.rdNoPad (P.NW.msgs v.2.2.1) v.2.2.2)) Unit (fun _ k => k)
      (I → E) (fun M k => (k.1, k.2.1, T.YW.putAt pl M k.2.2))

/-- Sets of slots: shared masks in the family of G_u. -/
def ldLinStdV_freshU : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (qa : Finset P.Ea.Pos → Prop)
      (_ : P.X2) (_ : P.E1.Str) (I : Type) [Fintype I] [DecidableEq I] (pl : I → Σ a, T.YU.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chainV (T.snd LW LU LO tW tU tO) qa N on0 εf).FreshForV
      (fun s : P.Sh6 =>
        ((((s.1.1.1.1, s.1.1.1.2.1, T.YU.rdNoPad (P.NU.msgs s.1.1.1.2.2.2) T.w1), s.1.1.2), s.1.2),
          s.2))
      (fun v : P.W5 => (v.1, (v.2.2, T.YU.offAt pl (T.YU.rdNoPad (P.NU.msgs v.2.1) T.w1)))) (I → E)
      (fun M k => ((((k.1.1.1.1, k.1.1.1.2.1, T.YU.putAt pl M k.1.1.1.2.2), k.1.1.2), k.1.2), k.2))
      Unit (fun _ k => k)

/-- Sets of slots: shared masks in the family of Ω. -/
def ldLinStdV_freshO : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ) (LO : P.NO.O → ℕ)
      (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ)
      (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (qa : Finset P.Ea.Pos → Prop)
      (_ : P.X4) (_ : P.E4.Str) (I : Type) [Fintype I] [DecidableEq I] (pl : I → Σ a, T.YO.Fr a),
    Function.Injective pl → T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO →
    (P.chainV (T.snd LW LU LO tW tU tO) qa N on0 εf).FreshForV
      (fun s : P.Sh6 => ((s.1.1, s.1.2.1, T.YO.rdNoPad (P.NO.msgs s.1.2.2.2) T.w3), s.2))
      (fun v : P.W5 => (v.2, T.YO.offAt pl (T.YO.rdNoPad (P.NO.msgs v.1) T.w3))) (I → E)
      (fun M k => ((k.1.1, k.1.2.1, T.YO.putAt pl M k.1.2.2), k.2)) Unit (fun _ k => k)

end
end Spec

section
variable {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype ι]
  [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinStdC_freshW : Spec.ldLinStdC_freshW F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf I _ _ pl hpl hP hW hU hO
  obtain ⟨⟨lU, lO⟩, hdW, -, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinC_freshW P on0 εf (T.snd LW LU LO tW tU tO) (I → E)
    (T.YW.ownAt pl hpl T.datW (fun w => w.2) (fun _ => 0, T.w0)) _ T.YW.rdNoPad (T.YW.putAt pl)
    Prod.snd (fun _ _ => rfl) (fun _ _ => rfl)
    (stdL_own F E P.NW T.YW tW P.WA P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0) I pl hpl P.SdW hW)
    hdW lU lO (ldLinStd_apart P T LW LU LO tW tU tO)

theorem ldLinStdC_freshU : Spec.ldLinStdC_freshU F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf I _ _ pl hpl hP hW hU hO
  obtain ⟨⟨-, lO⟩, -, hdU, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinC_freshU P on0 εf (T.snd LW LU LO tW tU tO) (I → E)
    (T.YU.ownAt pl hpl T.datU (fun w => w.2) (fun _ => 0, T.w1)) _ T.YU.rdNoPad (T.YU.putAt pl)
    Prod.snd (fun _ _ => rfl) (fun _ _ => rfl)
    (stdL_own F E P.NU T.YU tU P.W2 P.W1 T.datU (fun w => w.2) (fun _ => 0, T.w1) I pl hpl P.SdU hU)
    hdU lO (ldLinStd_apart P T LW LU LO tW tU tO)

theorem ldLinStdC_freshO : Spec.ldLinStdC_freshO F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf I _ _ pl hpl hP hW hU hO
  obtain ⟨-, -, -, hdO⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinC_freshO P on0 εf (T.snd LW LU LO tW tU tO) (I → E)
    (T.YO.ownAt pl hpl T.datO (fun w => w.2) (fun _ => 0, T.w3)) _ T.YO.rdNoPad (T.YO.putAt pl)
    (stdL_own F E P.NO T.YO tO P.W4 P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3) I pl hpl P.SdO hO)
    hdO

theorem ldLinStdV_freshW : Spec.ldLinStdV_freshW F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf N qa I _ _ pl hpl hP hW hU hO
  obtain ⟨⟨lU, lO⟩, hdW, -, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinV_freshW P on0 εf N (T.snd LW LU LO tW tU tO) qa (I → E)
    (T.YW.ownAt pl hpl T.datW (fun w => w.2) (fun _ => 0, T.w0)) _ T.YW.rdNoPad (T.YW.putAt pl)
    Prod.snd (fun _ _ => rfl) (fun _ _ => rfl)
    (stdL_own F E P.NW T.YW tW P.WA P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0) I pl hpl P.SdW hW)
    hdW lU lO (ldLinStd_apart P T LW LU LO tW tU tO)

theorem ldLinStdV_freshU : Spec.ldLinStdV_freshU F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf N qa x₂ y₂ I _ _ pl hpl hP hW hU hO
  obtain ⟨⟨lU, lO⟩, -, hdU, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinV_freshU P on0 εf N (T.snd LW LU LO tW tU tO) qa x₂ y₂ (I → E)
    (T.YU.ownAt pl hpl T.datU (fun w => w.2) (fun _ => 0, T.w1)) _ _ T.YU.rdNoPad (T.YU.putAt pl)
    (T.YU.offAt pl) (T.YU.offAt_putAt pl)
    (stdL_own F E P.NU T.YU tU P.W2 P.W1 T.datU (fun w => w.2) (fun _ => 0, T.w1) I pl hpl P.SdU hU)
    hdU lU lO (ldLinStd_apart P T LW LU LO tW tU tO)

theorem ldLinStdV_freshO : Spec.ldLinStdV_freshO F E ι κ J Y := by
  intro P T LW LU LO tW tU tO on0 εf N qa x₄ y₄ I _ _ pl hpl hP hW hU hO
  obtain ⟨⟨-, lO⟩, -, -, hdO⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinV_freshO P on0 εf N (T.snd LW LU LO tW tU tO) qa x₄ y₄ (I → E)
    (T.YO.ownAt pl hpl T.datO (fun w => w.2) (fun _ => 0, T.w3)) _ _ T.YO.rdNoPad (T.YO.putAt pl)
    (T.YO.offAt pl) (T.YO.offAt_putAt pl)
    (stdL_own F E P.NO T.YO tO P.W4 P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3) I pl hpl P.SdO hO)
    hdO lO (ldLinStd_apart P T LW LU LO tW tU tO)

end
end Cb
