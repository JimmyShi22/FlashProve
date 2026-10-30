-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlSenders.lean: the honest senders of the offline phase over p = 2^64 - 2^32 + 1, in their
standard form: three clauses asked of each (fifteen in all) follow from conditions on codes,
layouts, samples and formats.

Exactly: with the standard senders, the fifteen clauses on the five senders of the offline phase
(for each: its laws, "the law of the answers does not depend on the witness", "the sent encodings
hide t positions") follow from: the codes are built from plain Reed-Solomon families with t ≤ r
uniform coefficients; layouts; padded samples; three clauses on the format.

Definitions, statements (`Cb.Spec.stdL_ok_fmt`, `Cb.Spec.padBasis_one`, `Cb.Spec.stdL_fmt_plain`;
`Cb.Gl.Spec.gl_padBasis`, `Cb.Gl.Spec.gl_stdL_ok`, `Cb.Gl.Spec.gl_off_snd`) and proofs.

Why: `Sn.Third`, `S.Third` (Cb/Obj/LdObjectThirdTests.lean) and `Z.Rest0 p` (Cb/Ld/LdWfEnd.lean)
ask, for each of the five sendings, three clauses on the honest sender: its laws, "the law of the
answers does not depend on the witness", "the encoding hides t long positions". They are asked
there, not derived. The sent oracle messages' codes are asked `GlC` at t = 0 only: the limits of
Cb/GlVal/GlThird.lean.

Main names, generic (any F ⊆ E), on Cb/Ld/LdSendStdL.lean (Y : N.StdL F: data, free entries, pads;
Y.snd; Y.OK t):
  `Y.Fmt`: three clauses on the format. enc: a word as sent, read over E, is the code's encoding;
    lay: msgOf lays data, free entries and pad at their places; zk: the format's encoder hides
    whatever the code's native encoder hides
    (`zk : ∀ a t, (N.om a).C.Zk t → (Y.En a).Hides ((N.om a).C.budT t)`).
  `Y.PadSmp`: every member's sample, on the layout's names, is the row with a pad of
    Cb/Gen/OodDecPad.lean (the multilinear extension of the entries proper at a point, plus β times
    the element of E that the pad entries stand for), the pad's weights are a basis of E over F, and
    β is never 0.
  `Spec.stdL_ok_fmt`: `Y.Fmt`, `Y.PadSmp`, (∀ a, (N.om a).C.Zk (t a)) ⇒ `Y.OK t`.
  `Spec.stdL_fmt_plain`: the plain format (`StdSig`: Cb/Ld/LdSendStd.lean; its layout `G.toL`:
    Cb/Ld/LdSendStdL.lean) has `Y.Fmt`: all three by definition.
Main names, at this field:
  `Spec.padBasis_one`: (any field) the weight 1 on one pad entry of E; `Spec.gl_padBasis`: 1, x, x²
    are a basis of E = F[x] / (x³ - 2) over F, in the form that the padded sample wants: three pad
    entries of F.
  `Spec.gl_stdL_ok`: for a layout with pads in any subfield Fp of E: `Y.Fmt`, `Y.PadSmp`,
    (∀ a, GlC (N.om a).C (d a) (t a)) ⇒ `Y.OK t`. The hiding comes from t ≤ r inside GlC
    (Cb/Gl/GlLd.lean: `glC_code`).
  `Spec.gl_off_snd`: for A : LdOffE F E whose senders are the standard ones (three equations:
    A.Sn = T.snd ..; A.Sl = A.K.P.stdS ..; A.Z.D = A.Z.W.P.stdD ..), with pads in any subfields
    F₁, F₂, F₃ for the test, the link, weights-formedness: the fifteen clauses (`snd`, `bl`, `hid`
    of `S.Third`, their like of `Sn.Third`; sender, sBlind, hides of `Z.Rest0 p`) follow from three
    things: the places (the test's: T.Places; the link's: YK.Reads ixK: every entry of (u₀, u₁) is
    read at a data place that holds it; weights-formedness': P.body reads the data of the messages
    alone, by a map bd that undoes datS); Fmt and PadSmp of the five layouts; GlC at the numbers t
    that the senders name.

Which field the pad lies in (the layouts are generic in it: "Fp" above and below). A write-up
of ours (lean/CREDITS.md) has, for each answer, as many pad entries as the degree of E over
the field of the
message's entries:
  a message over E (the messages of the test for linear constraints and of the link; every message
  that holds mask rows, so the message of weights-formedness too): one pad entry, an element of E,
  weight 1: Fp := E (`Spec.padBasis_one`);
  a message all of whose rows are over F: three pad entries, elements of F, weights 1, x, x²: Fp :=
  F (`Spec.gl_padBasis`).
  A warning. Three F-valued pad entries at places of a message over E give the honest side the same
  law (privacy holds), but on the other side the row is no evader there: a list member of a code
  over E may hold any elements of E at these places, and a vector such as (x, -1, 0) is annihilated
  at every seed. With lists of one member nothing is lost; beyond unique decoding "two messages of a
  list agree at few seeds" fails with that choice as soon as two messages that differ by such a
  vector lie in one list (where the sample's `err` is below the number of its seeds: not so with one
  coefficient alone, card B = 1 in `Sample.pad`, Cb/Gen/OodDecPad.lean). (That two such messages
  lie in one list is shown nowhere.) So: Fp := E for all five senders of the offline phase; no
  statement of this file asks it: `Spec.gl_off_snd` admits any F₁, F₂, F₃.


What the format is when F ≠ E. The plain format: a word as sent is a native word over E, every
symbol an element of E (three elements of F), also for an oracle message all of whose entries lie in
F; the encoding randomness is uniform over E. A format of words over F is not covered: its encoder's
randomness would be uniform over F, and clause zk would need the hiding of the code over F, of which
GlC (codes over E) says nothing. The write-up does send words over F, with randomness over
F, for rows over F (the index, cells, digits, bits): for such rows the plain format is three times
as long; no claim moves.

Limits: that these conditions can be met together with the other clauses of `Sn.Third`, `S.Third`
and `Z.Rest0 p` is not shown here. This file says nothing on the online phase. Masks (free entries)
are allowed for, and nothing is said of them here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlOff
import Cb.Ld.LdLinStd
import Cb.Ld.LdSendStdVec
import Cb.Obj.LdObjectSenders

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)

/-- Three clauses on the format. -/
structure Fmt : Prop where
  enc : ∀ a m r, (N.om a).upW ((Y.En a).enc m r) = (N.om a).C.enc (Y.upM a m) (Y.upR a r)
  lay : ∀ a x η n, Y.upM a (Y.msgOf a x η) ((Y.ν a).symm n) = withPad (F := F) x η n
  zk  : ∀ a t, (N.om a).C.Zk t → (Y.En a).Hides ((N.om a).C.budT t)

/-- The samples are rows with a pad. -/
def PadSmp : Prop :=
  ∀ a, ∃ (μ B : Type) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B) (_ : Nonempty B)
        (pl : Y.Dt a ⊕ Y.Fr a → μ → Bool) (w : Y.Pd a → E) (b : B → E),
      (N.om a).Z.comap (Y.ν a).symm = Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b ∧
      PadBasis F w ∧ ∀ β, b β ≠ 0

end Sig.StdL

namespace Spec

def stdL_ok_fmt : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ),
    Y.Fmt → Y.PadSmp → (∀ a, (N.om a).C.Zk (t a)) → Y.OK t

def padBasis_one : Prop := ∀ (E : Type) [Field E], PadBasis E (fun _ : Unit => (1 : E))

def stdL_fmt_plain : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (G : StdSig F E),
    G.toL.Fmt

end Spec

theorem stdL_ok_fmt : Spec.stdL_ok_fmt := by
  intro F E _ _ _ _ _ N Y t hF hS hZ
  refine ⟨hF.enc, hF.lay, fun a => ?_, fun a => hF.zk a _ (hZ a)⟩
  obtain ⟨μ, B, _, _, _, _, pl, w, b, e, hw, hb⟩ := hS a
  rw [e]
  exact fun ρ _ x => ood_private_pad F E μ _ _ B pl w b hw ρ (hb ρ.2) x

theorem padBasis_one : Spec.padBasis_one := by
  intro E _
  have h : ∀ c : Unit → E, padVal (F := E) (fun _ : Unit => (1 : E)) c = c () :=
    fun c => by simp [padVal]
  exact ⟨fun c c' hc => funext fun _ => by rw [← h c, ← h c', hc], fun y => ⟨fun _ => y, h _⟩⟩

theorem stdL_fmt_plain : Spec.stdL_fmt_plain := by
  intro F E _ _ _ _ _ G
  refine ⟨fun _ _ _ => rfl, fun a x η n => ?_, fun _ _ h => h⟩
  show withPad (F := F) x η (G.ν a ((G.ν a).symm n)) = _
  rw [Equiv.apply_symm_apply]

namespace Gl

/-- 1, x, x² -/
def padW : Fin 3 → E := ![⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩]

namespace Spec

def gl_padBasis : Prop := PadBasis F padW

def gl_stdL_ok : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp) (d t : N.O → ℕ),
    Y.Fmt → Y.PadSmp → (∀ a, GlC (N.om a).C (d a) (t a)) → Y.OK t

/-- The fifteen clauses on the five senders of the offline phase. -/
def gl_off_snd : Prop :=
  ∀ (F₁ F₂ F₃ : Type) [Field F₁] [Fintype F₁] [Algebra F₁ E] [Field F₂] [Fintype F₂] [Algebra F₂ E]
      [Field F₃] [Fintype F₃] [Algebra F₃ E] (A : LdOffE F E) (T : A.O.toC.P.Std F₁)
      (YK : A.K.P.N.StdL F₂) (ixK : ∀ a, YK.Dt a → Option (Fin A.Cf.C₀.k ⊕ Fin A.Cf.C₀.k))
      (wK : A.K.P.W1) (YS : A.Z.W.P.S.StdL F₃) (datS : A.Z.W.P.Body → ∀ a, YS.Dt a → E)
      (wS : A.Z.W.P.Body × A.Z.W.P.Wp) (bd : (∀ a, YS.Dt a → E) → A.Z.W.P.Body)
      (dW' : A.O.toC.P.NW.O → ℕ) (dU' : A.O.toC.P.NU.O → ℕ) (dO' : A.O.toC.P.NO.O → ℕ)
      (dK' : A.K.P.N.O → ℕ) (dS' : A.Z.W.P.S.O → ℕ),
    A.Sn = T.snd A.Sn.LW A.Sn.LU A.Sn.LO A.Sn.tW A.Sn.tU A.Sn.tO →
    A.Sl = A.K.P.stdS A.Sl.Sd A.Sl.L A.Sl.t YK ixK wK → A.Z.D = A.Z.W.P.stdD YS datS wS → T.Places →
    YK.Reads ixK (fun m => Sum.elim (A.K.P.uv₀ m) (A.K.P.uv₁ m)) →
    (∀ m, A.Z.W.P.body m = bd (YS.dataOf m)) → (∀ b, bd (datS b) = b) → T.YW.Fmt → T.YW.PadSmp →
    (∀ a, GlC (A.O.toC.P.NW.om a).C (dW' a) (A.Sn.tW a)) → T.YU.Fmt → T.YU.PadSmp →
    (∀ a, GlC (A.O.toC.P.NU.om a).C (dU' a) (A.Sn.tU a)) → T.YO.Fmt → T.YO.PadSmp →
    (∀ a, GlC (A.O.toC.P.NO.om a).C (dO' a) (A.Sn.tO a)) → YK.Fmt → YK.PadSmp →
    (∀ a, GlC (A.K.P.N.om a).C (dK' a) (A.Sl.t a)) → YS.Fmt → YS.PadSmp →
    (∀ a, GlC (A.Z.W.P.S.om a).C (dS' a) (A.Z.t a)) →
    (A.Sn.dW.Laws A.O.toC.P.backW ∧
      A.Sn.dW.Blind A.O.toC.P.SdW ∧
      A.Sn.dW.Nn.Hides (A.O.toC.P.NW.budT A.Sn.tW)) ∧
    (A.Sn.dU.Laws A.O.toC.P.backU ∧
      A.Sn.dU.Blind A.O.toC.P.SdU ∧
      A.Sn.dU.Nn.Hides (A.O.toC.P.NU.budT A.Sn.tU)) ∧
    (A.Sn.dO.Laws A.O.toC.P.backO ∧
      A.Sn.dO.Blind A.O.toC.P.SdO ∧
      A.Sn.dO.Nn.Hides (A.O.toC.P.NO.budT A.Sn.tO)) ∧
    (A.Sl.dS.Laws A.K.P.back ∧ A.Sl.dS.Blind A.Sl.Sd ∧ A.Sl.dS.Nn.Hides (A.K.P.N.budT A.Sl.t)) ∧
    (A.Z.D.Laws A.Z.W.P.back ∧ A.Z.D.Blind A.Z.W.P.Sd ∧ A.Z.D.Nn.Hides (A.Z.W.P.S.budT A.Z.t))

end Spec

theorem gl_padBasis : Spec.gl_padBasis := by
  have h : ∀ c : Fin 3 → F, padVal (F := F) padW c = ⟨c 0, c 1, c 2⟩ := fun c => by
    unfold padVal padW
    rw [Fin.sum_univ_three]
    apply Code.Cubic.ext <;> simp
  refine ⟨fun c c' hc => ?_, fun y => ⟨![y.c0, y.c1, y.c2], by rw [h]; rfl⟩⟩
  rw [h, h] at hc
  have h0 := congrArg Code.Cubic.c0 hc
  have h1 := congrArg Code.Cubic.c1 hc
  have h2 := congrArg Code.Cubic.c2 hc
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem gl_stdL_ok : Spec.gl_stdL_ok := fun Fp _ _ _ N Y _ t hF hS hC =>
  stdL_ok_fmt Fp E N Y t hF hS fun a => (glC_code _ _ _ _ (hC a)).2.2.2.2

theorem gl_off_snd : Spec.gl_off_snd := by
  intro F₁ F₂ F₃ _ _ _ _ _ _ _ _ _ A T YK ixK wK YS datS wS bd dW' dU' dO' dK' dS' hSn hSl hZ hPl
    hRd hbody hbd fW sW cW fU sU cU fO sO cO fK sK cK fS sS cS
  have eW : A.Sn.dW = T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0) :=
    congrArg (fun S => S.dW) hSn
  have eU : A.Sn.dU = T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1) :=
    congrArg (fun S => S.dU) hSn
  have eO : A.Sn.dO = T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3) :=
    congrArg (fun S => S.dO) hSn
  have eK : A.Sl.dS =
      YK.snd (YK.vecDat (fun w : A.K.P.W1 => Sum.elim w.1.1 w.1.2) ixK) (fun w => w.2) wK :=
    congrArg (fun S => S.dS) hSl
  obtain ⟨-, aW, -, bW, cW', dW'', -⟩ :=
    stdL_all F₁ E _ T.YW A.Sn.tW _ _ T.datW (fun w => w.2)
      (fun _ => 0, T.w0) (gl_stdL_ok F₁ _ T.YW dW' _ fW sW cW)
  obtain ⟨-, aU, -, bU, cU', dU'', -⟩ :=
    stdL_all F₁ E _ T.YU A.Sn.tU _ _ T.datU (fun w => w.2)
      (fun _ => 0, T.w1) (gl_stdL_ok F₁ _ T.YU dU' _ fU sU cU)
  obtain ⟨-, aO, -, bO, cO', dO'', -⟩ :=
    stdL_all F₁ E _ T.YO A.Sn.tO _ _ T.datO (fun w => w.2)
      (fun _ => 0, T.w3) (gl_stdL_ok F₁ _ T.YO dO' _ fO sO cO)
  have hK := stdL_vec F₂ E A.K.P.N YK A.Sl.t A.K.P.W1 A.K.P.W0 _
    (fun w : A.K.P.W1 => Sum.elim w.1.1 w.1.2) ixK (fun w => w.2) wK
    (fun m => Sum.elim (A.K.P.uv₀ m) (A.K.P.uv₁ m))
    (fun v r => ((fun k => v (Sum.inl k), fun k => v (Sum.inr k)), r))
    (gl_stdL_ok F₂ _ YK dK' _ fK sK cK) hRd fun _ => rfl
  have hS :=
    ldWf_std F₃ E _ A.Z.W.P YS A.Z.t datS wS bd (gl_stdL_ok F₃ _ YS dS' _ fS sS cS) hbody hbd
  rw [eW, eU, eO, eK, hZ]
  refine ⟨⟨bW _ fun w k => Prod.ext (funext fun c => ?_) rfl, cW' _, dW''⟩,
    ⟨bU _ fun w k => Prod.ext (funext fun c => ?_) rfl, cU' _, dU''⟩,
    ⟨bO _ fun w k => Prod.ext (funext fun c => ?_) rfl, cO' _, dO''⟩,
    ⟨hK.1, hK.2.1 _, hK.2.2.1⟩,
    hS⟩
  · show (T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0)).upM
        ((T.YW.snd T.datW (fun w => w.2) (fun _ => 0, T.w0)).put w k)
        A.O.toC.P.iW (A.O.toC.P.lW c) = w.1 c
    rw [hPl.lW c, aW w k]
    show (T.pW A.O.toC.P.iW (T.qW c)).elim 0 w.1 = w.1 c
    rw [hPl.hW c]
    rfl
  · show (T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).upM
        ((T.YU.snd T.datU (fun w => w.2) (fun _ => 0, T.w1)).put w k)
        A.O.toC.P.iU (A.O.toC.P.lU c) = w.1 c
    rw [hPl.lU c, aU w k]
    show (T.pU A.O.toC.P.iU (T.qU c)).elim 0 w.1 = w.1 c
    rw [hPl.hU c]
    rfl
  · show (T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).upM
        ((T.YO.snd T.datO (fun w => w.2) (fun _ => 0, T.w3)).put w k)
        A.O.toC.P.iO (A.O.toC.P.lO c) = w.1 c
    rw [hPl.lO c, aO w k]
    show (T.pO A.O.toC.P.iO (T.qO c)).elim 0 w.1 = w.1 c
    rw [hPl.hO c]
    rfl

end Gl
end Cb
