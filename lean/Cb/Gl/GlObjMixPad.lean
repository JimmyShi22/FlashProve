-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlObjMixPad.lean: in the hypotheses on the protocol object over p =
2^64 - 2^32 + 1, clauses on the codes of weights-formedness, of the seven sendings and of the seven
tests follow from conditions on its Reed-Solomon codes and radii and on the form of its sample maps,
under the hypothesis `Cb.BCHKS46F F` on mutual correlated agreement; here, for the session's three
sendings, the clause that two members of one list agree at few seeds is derived too; the formats'
clauses, the request's own hypotheses (`Own3`: rHyp, rZk) and the other clauses are asked as they
stand.

Definitions, statements and proofs: an assembly.

Why: Cb/Gl/GlObjMixStd.lean (`ObjGlMS`) asks, for the session's three sendings, "evades": two
members of one list of the code agree at few seeds. In a write-up of ours (lean/CREDITS.md)
that is no hypothesis:
its sample map (the point's weights on the entries proper, a non-zero factor times a basis on the
pad, the pad in the message's own field) is a zero-evader over that field. The vector form stands in
Cb/Gen/OodDecPad.lean (`Spec.ood_okOn_pad`). Here it is put in.

Main names, generic (any subfield Fp of E):
  `Y.PadSmpE`: every member's sample, on the layout's names, is the row with a pad
    (Cb/Gl/GlSenders.lean: `Y.PadSmp`: the weights a basis of E over Fp, the factor never 0), and:
    the entries proper stand at different corners of the cube; the factor b is injective; the pad's
    weights are independent over E (Function.Injective (padVal (F := E) w): with "a basis over Fp"
    that is: one pad entry an answer, Fp all of E: the write-up's case for a message over
    E).
  `Spec.padSmpE_ev`: `Y.PadSmpE` → every member evades (`OMsg.Evades`, Cb/Ld/LdSig.lean: two
    different members of one list have the same answers at no more than Z.err seeds).
Main names, at this field:
  `SndGlJP N Y Sd L t d` (its fields: see the record); `SndGlJP.to` : → `SndGlJ`
    (Cb/Gl/GlObjMix.lean): "private" (`Sample.Private`, Cb/Gen/OodDecPad.lean) and "evades" derived.
  `ObjGlMP Z S a k msg r e mca`: `ObjGlMS` with the session's three sendings at `SndGlJP`.
  `Spec.glMP_to`: `ObjGlMP` → `ObjGlMS`; `Spec.glMP_hyp`: BCHKS46F F → ObjGlMP Z S .. → `Z.Hyp p`.

So of `Z.Hyp p`'s clauses that touch a code, outside the request's own hypotheses (`Own3.rHyp`) and
what Limits lists as asked, those on the codes of weights-formedness, the seven sendings and the
seven tests (laws, distances, lists, what the sent encodings hide, "evades", agreement) are derived:
from `GlC` / `GlJ`, inequalities, the samples' form, the format's clause zk (Y.Fmt.zk,
Cb/Gl/GlSenders.lean), and, for `T.John` of the session's three towers alone, BCHKS46F F.

Limits: asked as they stand: equations, places, seeds, formats, the samples' form (session) or
"private" (the five other sendings), radii, bounds, Own3, HypPl, Rest2; also the configuration's
sample map and model (smp, model), Fits of each group, the bridges' and the switches' evaders, and
of a shaped tower `Sh.view.Laws`.
`Own3` (Cb/Obj/LdObjectDataThird.lean) holds the request's own hypotheses whole: rHyp : T.r.Hyp,
whose first clause is `LdSendD.Hyp` (Cb/Req1/LdSegKit.lean: laws, fair, list, evades, sender, blind,
hides) of the request's first sending, and rZk : T.r.ZkS.
Asked as they stand too: in each format, Y.Fmt.zk (Cb/Gl/GlSenders.lean); at each switch of a tower:
`Sample.PrivateSim` of the switch's sample.
The padded sample's number of exceptional seeds is that of Cb/Gen/OodDecPad.lean (err: a maximum of
two terms; against the number of seeds: at most (variables + 1) / |B|: `Spec.ood_frac_pad`): small
only if b has many values.
This file does not say that `ObjGlMP` can be met: no instance of the whole record. No instance that
meets the hypotheses of `glMP_hyp` is part of this library; as far as the library shows, this
theorem may hold of nothing.

What the heads of Cb/Gl/GlObjMix.lean and
Cb/Gl/GlObjMixStd.lean list as not said is not said here either.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlObjMixStd
import Cb.Gen.OodDecSend

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {Fp E : Type} [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E] {N : Sig E}

/-- Every member's sample is the row with a pad, with the three conditions under which it is a
zero-evader over E (`Spec.ood_okOn_pad`). -/
def Sig.StdL.PadSmpE (Y : N.StdL Fp) : Prop :=
  ∀ a, ∃ (μ B : Type) (_ : Fintype μ) (_ : DecidableEq μ) (_ : Fintype B) (_ : Nonempty B)
        (pl : Y.Dt a ⊕ Y.Fr a → μ → Bool) (w : Y.Pd a → E) (b : B → E),
      (N.om a).Z.comap (Y.ν a).symm = Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b ∧
      PadBasis Fp w ∧ (∀ β, b β ≠ 0) ∧
      Function.Injective pl ∧
      Function.Injective b ∧
      Function.Injective (padVal (F := E) w)

end

def Spec.padSmpE_smp : Prop :=
  ∀ (Fp E : Type) [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E]
      (N : Sig E) (Y : N.StdL Fp),
    Y.PadSmpE → Y.PadSmp

def Spec.padSmpE_ev : Prop :=
  ∀ (Fp E : Type) [Field Fp] [Fintype Fp] [Field E] [Fintype E] [Algebra Fp E]
      (N : Sig E) (Y : N.StdL Fp),
    Y.PadSmpE → ∀ a, (N.om a).Evades

theorem padSmpE_smp : Spec.padSmpE_smp := by
  intro Fp E _ _ _ _ _ N Y h a
  obtain ⟨μ, B, i1, i2, i3, i4, pl, w, b, e, hw, hb, -, -, -⟩ := h a
  exact ⟨μ, B, i1, i2, i3, i4, pl, w, b, e, hw, hb⟩

theorem padSmpE_ev : Spec.padSmpE_ev := by
  intro Fp E _ _ _ _ _ N Y h a
  obtain ⟨μ, B, _, _, _, _, pl, w, b, e, -, -, hpl, hb, hw⟩ := h a
  have h0 : (Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b).OKOn (PadInF E) :=
    ood_okOn_pad E E μ _ _ B pl w b hpl hb hw
  have h1 :=
    ood_okOn_comap E _ _ (Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b) (Y.ν a) (PadInF E) h0
  have e2 : (N.om a).Z = (Sample.pad E μ (Y.Dt a ⊕ Y.Fr a) (Y.Pd a) B pl w b).comap (Y.ν a) := by
    rw [← e]
    show (N.om a).Z =
      { D := (N.om a).Z.D, S := (N.om a).Z.S,
        mat := fun ρ s j => (N.om a).Z.mat ρ s ((Y.ν a).symm (Y.ν a j)), err := (N.om a).Z.err }
    simp only [Equiv.symm_apply_apply]
  refine sig_evades_of_okOn E (N.om a) (fun u => PadInF E fun j => u ((Y.ν a).symm j))
    ?_ fun _ _ _ _ _ _ => ⟨_, rfl⟩
  rw [e2]
  exact h1

end Cb

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- One standard sending below the Johnson radius, the sample the row with a pad. -/
structure SndGlJP {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp)
    (Sd : N.Seeds) (L t d : N.O → ℕ) : Prop where
  fmt  : Y.Fmt
  smp  : Y.PadSmpE
  code : ∀ a, GlC (N.om a).C (d a) (t a)
  inJ  : ∀ a, InJohnson (Fintype.card (N.om a).P) (d a) (N.om a).e
  isL  : ∀ a, L a = listMax (Fintype.card (N.om a).P) (d a) (N.om a).e
  fair : Sd.Fair

theorem SndGlJP.to {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] {N : Sig E} {Y : N.StdL Fp}
    {Sd : N.Seeds} {L t d : N.O → ℕ} (h : SndGlJP N Y Sd L t d) : SndGlJ N Y Sd L t d :=
  { fmt := h.fmt
    priv := (gl_stdL_ok Fp N Y d t h.fmt (padSmpE_smp Fp E N Y h.smp) h.code).priv
    code := h.code, inJ := h.inJ, isL := h.isL, fair := h.fair
    ev := padSmpE_ev Fp E N Y h.smp }

/-- The object at this field, the session's samples the row with a pad: the conditions. -/
structure ObjGlMP (Z : LdObjZM F E) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ) :
    Prop where
  /-- the sender of weights-formedness -/
  wfStd   : (⟨Z.Zw.D, Z.Zw.X⟩ : Σ D, Z.Zw.K.MaskPl D Z.Zw.Rl) =
    ⟨Z.Zw.W.P.stdD S.YS S.datS S.wS,
      Z.Zw.K.stdX Z.Zw.Rl S.YS S.datS S.wS S.nAt S.RdW S.atL S.pl S.hpl⟩
  wfAtL   : ∀ l i, S.nAt (S.atL l i) = S.YS.entF (S.pl (some l) i)
  wfAtB   : ∀ i, S.nAt (Z.Zw.W.P.wAt i) = S.YS.entF (S.pl none i)
  wfNoPad : ∀ n, S.RdW n → S.YS.NoPad n
  wfBody  : ∀ m, Z.Zw.W.P.body m = S.bd (S.YS.dataOf m)
  wfBd    : ∀ b, S.bd (S.datS b) = b
  wfFmt   : S.YS.Fmt
  wfPriv  : ∀ o, ((Z.Zw.W.P.S.om o).Z.comap (S.YS.ν o).symm).Private Fp fun _ => True
  wfCt    : ∀ o, GlC (Z.Zw.W.P.S.om o).C (Z.dS o) (Z.Zw.t o)
  wfRest2 : Z.Zw.Rest2 p
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  /-- the code of the encoded index: within a third -/
  code  : Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha    : a ≤ 32
  hk    : k < 2 ^ a
  hp    : msg + r ≤ k + 1
  h3    : 3 * Z.Zw.W.Cf.eM < 2 ^ a - k
  smp   : Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model : Z.Zw.W.Cf.ModelOK
  /-- weights-formedness: within a third -/
  wfLt  : ∀ o, 3 * (Z.Zw.W.P.S.om o).e < Z.dS o
  wfOne : ∀ o, Z.Zw.L o = 1
  /-- the offline test's three sendings -/
  plS : Z.Y.TS.Places
  sW  : SndGl3 Z.R.W.O.toC.P.NW Z.Y.TS.YW Z.R.W.O.toC.P.SdW Z.Y.LW Z.Y.tW Z.dW
  sU  : SndGl3 Z.R.W.O.toC.P.NU Z.Y.TS.YU Z.R.W.O.toC.P.SdU Z.Y.LU Z.Y.tU Z.dU
  sO  : SndGl3 Z.R.W.O.toC.P.NO Z.Y.TS.YO Z.R.W.O.toC.P.SdO Z.Y.LO Z.Y.tO Z.dO
  /-- the link's sending -/
  rdK : Z.Y.YK.Reads Z.Y.ixK fun m => Sum.elim (Z.R.K.P.uv₀ m) (Z.R.K.P.uv₁ m)
  sK  : SndGl3 Z.R.K.P.N Z.Y.YK Z.Y.SdK Z.Y.LK Z.Y.tK Z.dN
  /-- the session's three sendings: below the Johnson radius -/
  plB : Z.Y.TB.Places
  sWB : SndGlJP Z.R.on.ol.toC.P.NW Z.Y.TB.YW Z.R.on.ol.toC.P.SdW Z.Y.LWB Z.Y.tWB Z.dWB
  sUB : SndGlJP Z.R.on.ol.toC.P.NU Z.Y.TB.YU Z.R.on.ol.toC.P.SdU Z.Y.LUB Z.Y.tUB Z.dUB
  sOB : SndGlJP Z.R.on.ol.toC.P.NO Z.Y.TB.YO Z.R.on.ol.toC.P.SdO Z.Y.LOB Z.Y.tOB Z.dOB
  /-- clauses as they stand in Z.Hyp p -/
  own : Z.R.toLdObjD.Own3
  pl  : Z.R.HypPl
  /-- the link's test and the offline test's three: within a third -/
  tK  : RunGlAt Z.R.Kc.run Z.twK Z.dK
  t₁  : RunGlAt Z.R.TP₀.D₁ Z.tw₁ Z.d₁
  t₂  : RunGlAt Z.R.TP₀.D₂ Z.tw₂ Z.d₂
  t₃  : RunGlAt Z.R.X.run Z.tw₃ Z.d₃
  /-- the session's three tests: below the Johnson radius -/
  t₁B : RunGlJAt Z.R.TB₀.D₁ Z.tw₁B Z.d₁B
  t₂B : RunGlJAt Z.R.TB₀.D₂ Z.tw₂B Z.d₂B
  t₃B : RunGlJAt Z.R.XB.run Z.tw₃B Z.d₃B

namespace Spec

def glMP_to : Prop :=
  ∀ (Z : LdObjZM F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E]
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ),
    ObjGlMP Z S a k msg r e mca → ObjGlMS Z S a k msg r e mca

def glMP_hyp : Prop :=
  Cb.BCHKS46F F →
  ∀ (Z : LdObjZM F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E]
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (S : WfStdD Z.Zw Fp) (a k msg r e mca : ℕ),
    ObjGlMP Z S a k msg r e mca → Z.Hyp p

end Spec

theorem glMP_to : Spec.glMP_to := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  {
    wfStd := h.wfStd
    wfAtL := h.wfAtL
    wfAtB := h.wfAtB
    wfNoPad := h.wfNoPad
    wfBody := h.wfBody
    wfBd := h.wfBd
    wfFmt := h.wfFmt
    wfPriv := h.wfPriv
    wfCt := h.wfCt
    wfRest2 := h.wfRest2
    wfIs := h.wfIs
    sndIs := h.sndIs
    code := h.code
    ha := h.ha
    hk := h.hk
    hp := h.hp
    h3 := h.h3
    smp := h.smp
    model := h.model
    wfLt := h.wfLt
    wfOne := h.wfOne
    plS := h.plS
    sW := h.sW
    sU := h.sU
    sO := h.sO
    rdK := h.rdK
    sK := h.sK
    plB := h.plB
    sWB := h.sWB.to
    sUB := h.sUB.to
    sOB := h.sOB.to
    own := h.own
    pl := h.pl
    tK := h.tK
    t₁ := h.t₁
    t₂ := h.t₂
    t₃ := h.t₃
    t₁B := h.t₁B
    t₂B := h.t₂B
    t₃B := h.t₃B }

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glMP_hyp : Spec.glMP_hyp := fun H Z Fp _ _ _ _ S a k msg r e mca h =>
  glMS_hyp H Z Fp S a k msg r e mca (glMP_to Z Fp S a k msg r e mca h)

end Cb.Gl
