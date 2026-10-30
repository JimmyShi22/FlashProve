-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontFmt.lean: the format of the front.

Statements (in `Cb.Spec`) and proofs. Framework only; no place of a text is rendered.
The list of a preamble (`PreListR`, Hiop/RecSubs.lean; the last item: `fitOff`, `fitOn` of `HypH`,
Hiop/RecBuild.lean) asks that the encoded index is left alone, that the record and the prover
encoded index are handed on, and that the budget bears what follows (Cb/Req1/LdReqFormat.lean,
Cb/Req1/LdSegFormat.lean). Here: the whole front of the reference segment
(Cb/Req1/LdSegFrontRef.lean) has the format, from `V.Fp.Z.Back` and conditions on the readers of the
record (the functions rc, r0, r j, rz): each step's map of the explicit part keeps what is read.

Main names:
  `Spec.ldProg_app_fmt`: two lists of moves in a row: if p has the format from φ to χ and q from χ
    to ψ, `p.app q` has it from φ to ψ.
  `Spec.ldSegFrontFmt_psc`, `Spec.ldSegFrontFmt_in`: the two blocks of the table: no condition but
    "Back" of the step into a sumcheck and whatever the arguments hold as proofs.
  `Spec.ldSegFrontFmt`: under the hypotheses named above, `V.prog.Fmt`, from the entry stage to the
    stage at which the front ends: the index wherever it is among the further oracles (i), any
    reader px of the further witness, any bound q on positions (the front sends nothing and needs
    the positions that what follows needs).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFrontRef

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp

namespace Spec

def ldProg_app_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a b c : LdStage E Kc)
      (p : LdProg a b) (q : LdProg b c) (φ : JFmt Kc E0 Rc Pw a.J)
      (χ : JFmt Kc E0 Rc Pw b.J) (ψ : JFmt Kc E0 Rc Pw c.J),
    p.Fmt φ χ → q.Fmt χ ψ → (p.app q).Fmt φ ψ

def ldSegFrontFmt_psc : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (T : PscOur E) (S : Sig E)
      (E₀ : ExtSpec) (Wp : Type) (A0 : Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E)
      (i : IxAt E0 E₀) (r : T.St → Rc) (px : Wp → Pw) (q : Finset (E₀.prod S.ext).Pos → Prop),
    (frPsc Kc T S E₀ Wp A0 msg).Fmt ((frPscS Kc T S E₀ Wp A0 msg).fmt i (fun x => r x.2) px q)
      ((frPscT Kc T S E₀ Wp A0 msg).fmt i (fun o => r o.st) px q)

def ldSegFrontFmt_in : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (Z : PscIn E) (S : Sig E)
      (E₀ : ExtSpec) (Wp : Type) (R0 : Rels Kc Z.St0 E₀ (S.Msg × Wp)) (msg : S.Msg → Z.T.J → E)
      (i : IxAt E0 E₀) (r : Z.St0 → Rc) (px : Wp → Pw) (q : Finset (E₀.prod S.ext).Pos → Prop),
    Z.Back →
    (frIn Kc Z S E₀ Wp R0 msg).Fmt ((frInS Kc Z S E₀ Wp R0 msg).fmt i r px q)
      ((frPscT Kc Z.T S E₀ Wp (Z.ride R0) msg).fmt i (fun o => r (Z.old o.st)) px q)

/-- The format of the whole front. -/
def ldSegFrontFmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (z : LdStage E Kc)
      (V : LdFrontRef E Kc z) (i : IxAt E0 z.E₀) (rc : V.Fp.St → Rc) (r0 : V.Fp.Z.St0 → Rc)
      (r : ∀ j, (V.T j).St → Rc) (rz : z.St → Rc) (px : z.Wp → Pw)
      (q : Finset (z.E₀.prod z.S.ext).Pos → Prop),
    V.Fp.Z.Back → (∀ x, r0 (V.Fp.e x) = rc x.1.1) → (∀ o, r 0 (V.g0 o).2 = r0 (V.Fp.Z.old o.st)) →
    (∀ j o, r (j + 1) (V.g j o).2 = r j o.st) → (∀ o, rz (V.gz o) = r V.m o.st) →
    V.prog.Fmt (V.Fp.s0.fmt i rc px q) (z.fmt i rz px q)

end Spec

theorem ldProg_app_fmt : Spec.ldProg_app_fmt := by
  intro E Kc _ _ E0 Rc Pw a b c p q φ χ
  induction q with
  | nil =>
      intro ψ h1 h2
      rw [LdProg.app_nil, ← (LdProg.fmt_nil _ _ _).1 h2]
      exact h1
  | snoc q m ih =>
      intro ψ h1 h2
      obtain ⟨ξ, h3, h4⟩ := (LdProg.fmt_snoc q m χ ψ).1 h2
      rw [LdProg.app_snoc]
      exact (LdProg.fmt_snoc _ m φ ψ).2 ⟨ξ, ih ξ h1 h3, h4⟩

theorem ldSegFrontFmt_psc : Spec.ldSegFrontFmt_psc := by
  intro E Kc _ _ E0 Rc Pw T S E₀ Wp A0 msg i r px q
  unfold frPsc
  refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩
  exact mvA_fmt (frPscS Kc T S E₀ Wp A0 msg) _ _ (pscBk_plain T E₀ S.Msg Wp Kc msg) i
    (fun x y τ x' h => congrArg r (pscBk_pass T E₀ S.Msg Wp Kc msg x y τ x' h)) px q

theorem ldSegFrontFmt_in : Spec.ldSegFrontFmt_in := by
  intro E Kc _ _ E0 Rc Pw Z S E₀ Wp R0 msg i r px q hB
  unfold frIn
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨(frPscS Kc Z.T S E₀ Wp (Z.ride R0) msg).fmt i (fun x => r (Z.old x.2)) px q,
      (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, ?_⟩,
      ?_⟩
  · exact mvA_fmt (frInS Kc Z S E₀ Wp R0 msg) _ _ (inBk_plain Z E₀ S.Msg Wp Kc) i
      (fun x y τ x' h => congrArg r (inBk_pass Z E₀ S.Msg Wp Kc hB x y τ x' h)) px q
  · exact mvA_fmt (frPscS Kc Z.T S E₀ Wp (Z.ride R0) msg) _ _ (pscBk_plain Z.T E₀ S.Msg Wp Kc msg) i
      (fun x y τ x' h =>
        congrArg (fun s => r (Z.old s)) (pscBk_pass Z.T E₀ S.Msg Wp Kc msg x y τ x' h))
      px q

section
variable {E Kc : Type} [Field E] [Fintype E] {E0 : ExtSpec} {Rc Pw : Type}

theorem LdFrontTab.tw_fmt {z : LdStage E Kc} (B : LdFrontTab E Kc z) (i : IxAt E0 z.E₀)
    (r : ∀ j, (B.T j).St → Rc) (px : z.Wp → Pw) (q : Finset (z.E₀.prod z.S.ext).Pos → Prop)
    (hg : ∀ j o, r (j + 1) (B.g j o).2 = r j o.st) :
    ∀ k,
      (B.tw k).Fmt ((B.s 0).fmt i (fun x => r 0 x.2) px q) ((B.t k).fmt i (fun o => r k o.st) px q)
  | 0 => ldSegFrontFmt_psc E Kc E0 Rc Pw _ _ _ _ _ _ i (r 0) px q
  | k + 1 => by
      rw [LdFrontTab.tw_succ]
      refine ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _
        ((B.s (k + 1)).fmt i (fun x => r (k + 1) x.2) px q) _ ?_
        (ldSegFrontFmt_psc E Kc E0 Rc Pw _ _ _ _ _ _ i (r (k + 1)) px q)
      exact (LdProg.fmt_snoc _ _ _ _).2
        ⟨_, tw_fmt B i r px q hg k, ldStepF_fmt z.S _ _ _ i _ _ px q (hg k)⟩

end

theorem ldSegFrontFmt : Spec.ldSegFrontFmt := by
  intro E Kc _ _ E0 Rc Pw z V i rc r0 r rz px q hB he h0 hg hz
  show V.tab.prog.Fmt _ _
  unfold LdFrontTab.prog LdFrontTab.head
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨_, ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _ ((V.tab.s 0).fmt i (fun x => r 0 x.2) px q)
        _ ?_ (V.tab.tw_fmt i r px q hg V.m),
      ldStepF_fmt z.S _ _ _ i _ _ px q hz⟩
  refine (LdProg.fmt_snoc _ _ _ _).2
    ⟨_, ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ _ _ _
        (ldSegRef_pre_fmt E Kc _ _ _ V.Fp E0 Rc Pw i rc r0 px q he)
        (ldSegFrontFmt_in E Kc E0 Rc Pw _ _ _ _ _ _ i r0 px q hB),
      ldStepF_fmt z.S _ _ _ i _ _ px q h0⟩

end Cb
