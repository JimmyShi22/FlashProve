-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefFmtP.lean: the format of a reference segment, from readers of the record and demands
on positions.

Statements (each a `Prop` in `Cb.Spec`) and proofs. Framework only; no place of a text is rendered.
A format of a joint (`JFmt`, Cb/Req1/LdReqFormat.lean) fixes a place `ix` among the oracles (meant
for the index), a map `rc` off the explicit part (meant for the record), a map `px` off the witness
(meant for the prover encoded index), and a demand `q`: a predicate on finite sets of oracle
positions. A link has the format from φ to ψ (`Link.Fmt`) by four clauses: `idx`, `pass`, `hands`,
`bears`; a move, a list of moves, a segment has it (`LdMv.Fmt`, `LdProg.Fmt`, `LdSeg.Fmt`,
Cb/Req1/LdSegFormat.lean) if its links have it, with some formats between; `a.fmt i rc px q` is a
stage's format. Cb/Req1/LdReqRefZk.lean carries the format through the constructions of the
reference request and asks it of each reference segment. Cb/Req1/LdSegRefFmt.lean shows the format
of the closed body; Cb/Req1/LdSegWholeFmt.lean that of a segment with one group from its body's.
Here they are one statement.

Main names:
  `Spec.ldReqRefFmtP_seg`: `(K.seg l Qc).Fmt`, from the entry stage of the front to the stage after
    the locations: the index at any place i among the further oracles; the record read by ρ (readers
    at the front's stages, at the reads, at the tensor rows) and r₁ (at what the closing carries);
    px, px': readers of the further witness. Asked, for pp the characteristic of E (`[CharP E pp]`):
      `A.OK pp`; each map on explicit parts keeps what the reader reads (`ρ.Laws`;
      `r₁ (fz z) = ρ.rT ..`);
      the link `l` bridge-to-fold has the format up to its joint; the one sending's hypotheses; its
      sender hands on what px reads;
      the demands, backwards: q' (what follows the segment) → the locations → the demand after the
      one sending (qc on the old oracles, at most `tN a` long positions of each new member); qc → qm
      (the link's joint); the link bears qm from the demand behind the body's two sendings (q on the
      oracles at the entry, at most t, t' long positions of the reads' and of the digits' messages).
  `Spec.ldReqRefFmtP_tail`: the last segment: entry step, body, exit step: under `[CharP E pp]`,
    `T.A.OK pp`, `ρ.Laws`, `r₁ (T.fz z) = ρ.rT ..`: `T.tail.Fmt` from the two steps' formats (the
    body's follows from the four named).

Limits: this file does not say that the demands can be met together: numbers of positions against
what the encodings bear. It does not say that the steps between segments have their formats (the
model's maps must keep the record and the prover encoded index): `Spec.ldReqRefFmtP_tail` asks them
of the last segment's entry and exit steps.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefZk
import Cb.Req1.LdSegRefFmt
import Cb.Req1.LdSegWholeFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace Spec

/-- States, under the hypotheses below: a reference segment has the format. -/
def ldReqRefFmtP_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (E0 : ExtSpec) (Rc Pw : Type)
      (I : LdRefIx E) (A : LdRefD E Kc I) (K : LdRefC1 A)
      (l : Link Kc K.R.c1.fold.src.J K.R.c1.fold.mid) (Qc : LdCloseD K.R.c1.fold)
      (i : IxAt E0 I.C.E0) (ρ : LdRefR A Rc) (r₁ : K.St₁ → Rc)
      (px : I.C.PIdx × (A.W₁ × A.Gh) → Pw) (px' : Qc.Wp' → Pw)
      (q : Finset A.Xa.Q.D.s0.Ex.Pos → Prop) (qm : Finset K.R.c1.fold.mid.E.Pos → Prop)
      (qc : Finset K.R.c1.fold.tgt.Ex.Pos → Prop) (q' : Finset Qc.loc.tgt.Ex.Pos → Prop),
    A.OK pp → ρ.Laws → (∀ z, r₁ (K.fz z) = ρ.rT (A.X.stOf z).2) →
    l.Fmt (K.R.c1.fold.src.fmt i (fun st => r₁ st.2) px
        ((A.Xa.Q.D.S.sum A.Xa.Q.D.N).qSum
          A.Xa.Q.D.N' (A.Xa.Q.D.S.qSum A.Xa.Q.D.N q A.Xa.Q.D.t) A.Xa.Q.D.t'))
      (K.R.c1.fold.fmtMid i r₁ px qm) →
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ K.R.c1.fold.pE.src u) → qc U → qm V) → Qc.snd.Hyp →
    (∀ w, px' (Qc.Sn.rest w).2 = px w.2.2) →
    (∀ ρ' U, q' U → K.R.c1.fold.tgt.S.qSum Qc.N qc Qc.tN (Qc.loc.link.R.need ρ' U)) →
    (K.seg l Qc).Fmt (A.V.Fp.s0.fmt i ρ.rcV px q) (Qc.loc.tgt.fmt i (fun st => r₁ st.2) px' q')

/-- The last segment. -/
def ldReqRefFmtP_tail : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (E0 : ExtSpec) (Rc Pw : Type) (R : LdORE F E Kc) (b : LdStage E Kc) (T : LdRefT R b)
      (φ : JFmt Kc E0 Rc Pw b.J) (ψ : JFmt Kc E0 Rc Pw R.X.src.J) (i : IxAt E0 R.Cf.conf.E0)
      (ρ : LdRefR T.A Rc) (r₁ : T.St₁ → Rc) (px : R.Cf.conf.PIdx × (T.A.W₁ × T.A.Gh) → Pw)
      (q : Finset T.A.Xa.Q.D.s0.Ex.Pos → Prop),
    T.A.OK pp → ρ.Laws → (∀ z, r₁ (T.fz z) = ρ.rT (T.A.X.stOf z).2) →
    T.entry.Fmt φ (T.A.V.Fp.s0.fmt i ρ.rcV px q) →
    T.exit.Fmt
      ((T.A.X.tgt T.St₁ T.Az).fmt i (fun x => r₁ x.2) px
        ((T.A.Xa.Q.D.S.sum T.A.Xa.Q.D.N).qSum
          T.A.Xa.Q.D.N' (T.A.Xa.Q.D.S.qSum T.A.Xa.Q.D.N q T.A.Xa.Q.D.t) T.A.Xa.Q.D.t')) ψ →
    T.tail.Fmt φ ψ

end Spec

theorem ldReqRefFmtP_seg : Spec.ldReqRefFmtP_seg := fun E Kc _ _ pp _ E0 Rc Pw I A K l Qc i ρ r₁ px px' q qm qc q' hA hρ hr hl hqm hs hpx hq' =>
  ldSegWholeFmt_one E Kc E0 Rc Pw _ K.R.c1 _ K.kinds l Qc _ i r₁ px px' _ qm qc q'
    (ldSegRefAll_fmt E Kc pp E0 Rc Pw I A i ρ px q K.St₁ K.fz K.Az r₁ hA hρ hr) hl hqm hs hpx hq'

theorem ldReqRefFmtP_tail : Spec.ldReqRefFmtP_tail := by
  intro F E Kc _ _ _ _ _ pp _ E0 Rc Pw R b T φ ψ i ρ r₁ px q hA hρ hr h1 h2
  unfold LdRefT.tail
  exact (LdProg.fmt_snoc _ _ _ _).2
    ⟨_, ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ φ _ _
        ((LdProg.fmt_snoc _ _ _ _).2 ⟨φ, (LdProg.fmt_nil _ _ _).2 rfl, h1⟩)
        (ldSegRefAll_fmt E Kc pp E0 Rc Pw _ T.A i ρ px q T.St₁ T.fz T.Az r₁ hA hρ hr),
      h2⟩

end Cb
