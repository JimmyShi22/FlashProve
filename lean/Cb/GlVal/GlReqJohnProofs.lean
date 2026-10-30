-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlReqJohnProofs.lean: the proofs of the statements of
Cb/GlVal/GlReqJohn.lean
(`Cb.padE_ok`; `Cb.Gl.glReqJohn_msgs`, `glReqJohn_send`, `glReqJohn_fold`, `glReqJohn_body`,
`glReqJohn_seg`, `glReqJohn_list`): an assembly of Cb/Gen/OodDecPad.lean, Cb/Gen/OodDecSend.lean
(the row with a pad), Cb/Gl/GlSenders.lean (the layout's conditions), Cb/Gl/GlLd.lean,
Cb/Gl/GlLdJ.lean (codes), Cb/Gl/GlGroupJohn.lean (a closing's fold).

Main names (statements and hypotheses: Cb/GlVal/GlReqJohn.lean):
  `padE_ok`: one member's sample: from `Y.PadE a` to `(N.om a).Z.OK`.
  `glReqJohn_msgs`: one family's oracle messages: from `MsgsGl` to `Y.OK t` and `NearJ`.
  `glReqJohn_send`: one sending: from `IsStdGl` to `IsStdJ`.
  `glReqJohn_fold`: one closing's move: under BCHKS46F F, from `IsGrpGl` to `IsGrpJ`.
  `glReqJohn_body`: from `ProtoGlA` to `ProtoJ`.
  `glReqJohn_seg`, `glReqJohn_list`: under BCHKS46F F, from `ProtoGlS`, `ProtoGlL` to `ProtoJ`.

What the statements say and do not say: the head of Cb/GlVal/GlReqJohn.lean. BCHKS46F F is a
hypothesis by name of three of them (_fold, _seg, _list), no axiom.
-/
import Cb.GlVal.GlReqJohn

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem padE_ok : Spec.padE_ok := by
  intro Fp E _ _ _ _ _ N Y a h
  obtain ⟨μ, B, _, _, _, _, pl, w, b, e, hpl, hb, hw⟩ := h
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
  rw [e2]
  exact fun v hv => h1 v (fun _ => ⟨_, rfl⟩) hv

end Cb

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR Cb.Ood

theorem glReqJohn_msgs : Spec.glReqJohn_msgs := by
  intro Fp _ _ _ N Y L t d h
  refine ⟨gl_stdL_ok Fp N Y d t h.fmt h.smp h.code, fun a => ?_⟩
  have g := glC_code _ _ _ _ (h.code a)
  rcases h.near a with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact .inl ⟨g.1, g.2.2.2.1, h1, h2⟩
  · exact .inr ⟨g.1, g.2.2.2.1, h1, h2, padE_ok Fp E N Y a h3⟩

theorem glReqJohn_send : Spec.glReqJohn_send := by
  rintro Kc a d ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, dd, e, hb, hf, hM⟩
  exact ⟨Fp, i1, i2, i3, Y, dat, rst, bk₀, w0, dd, e, (glReqJohn_msgs Fp d.N Y d.L d.t dd hM).1,
    hb, hf, (glReqJohn_msgs Fp d.N Y d.L d.t dd hM).2⟩

theorem glReqJohn_fold : Spec.glReqJohn_fold := by
  rintro H Kc D l
    ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, ⟨hv, hm1, hm2, hz, h1⟩, hH, ⟨hC, hZb, hW, hJ⟩,
      ⟨hi, hn, hp, hq⟩, hZ, hF⟩
  have hS : Sh.OK :=
    ⟨hv, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bC hC)).1, (glC_code _ _ d 0 (glJ_glC _ _ d 0 D.G.e bZ hZb)).1, fun r => by
      split
      · next b hb => exact hm1 r b hb
      · next j hj => exact hm2 r j hj, hz, h1⟩
  exact ⟨iB, iP, Sh, Hd, Z, hc, dw, d, t, bC, bZ, bW, e, hS, hH,
    glGroupJohn_par Sh H hC hZb hW hJ hi hn hp hq, hZ, hF⟩

theorem glReqJohn_body : Spec.glReqJohn_body := fun Kc _ _ _ h =>
  ⟨h.front, h.ok, h.places, h.uniq, glReqJohn_send Kc _ _ h.send1, glReqJohn_send Kc _ _ h.send3,
    h.tabQ, h.tabH, h.keys, h.tags, h.inj, h.named, h.adm, h.bits, h.reads, h.deg, h.ev⟩

theorem glReqJohn_seg : Spec.glReqJohn_seg := fun H Kc I _ _ pp h =>
  ⟨glReqJohn_body Kc I _ pp h.body, h.ev, h.named,
    glReqJohn_fold H Kc _ _ h.fold, glReqJohn_send Kc _ _ h.snd⟩

theorem glReqJohn_list : Spec.glReqJohn_list := by
  intro H Kc I a b L pp
  induction L with
  | nil => intro _; rw [LdRefL.ProtoJ]; trivial
  | snoc L S ih =>
      intro h
      rw [ProtoGlL] at h
      rw [LdRefL.ProtoJ]
      exact ⟨ih h.1, glReqJohn_seg H Kc I _ S pp h.2⟩

end Cb.Gl
