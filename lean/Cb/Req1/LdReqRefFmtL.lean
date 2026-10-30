-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefFmtL.lean: the format of the list of reference segments, and of the whole reference
request, from readers and demands.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs. Framework only.
A format of a joint (`JFmt`, Cb/Req1/LdReqFormat.lean) fixes a place `ix` among the oracles (meant
for the index), a map `rc` off the explicit part (meant for the record), a map `px` off the witness
(meant for the prover encoded index), and a demand `q` on sets of positions. Formats of links: the
same file, whose head tells them in words (the row of `l.Fmt φ ψ`).

Main names:
  `S.FmtAt χ ψ`: for a reference segment S, a format χ at its first stage and ψ at its last: there
    are parameters (the readers ρ, r₁ of the record; px' of the further witness after the one
    sending; the demands q, qm, qc, q') with:
      the index is the further oracle of the body's stages, the prover encoded index the first part
      of their further witness (no parameters: fixed); the record that the format reads at the
      tensor rows is the one with which their statement decodes the index (`ρ.rT = A.rc`);
      the entry step has the format from χ to the format of the front's entry stage (the model's
      maps keep the record and the prover encoded index); the premises of `Spec.ldReqRefFmtP_seg`
      but `[CharP E pp]`, `A.OK pp` and `Qc.snd.Hyp`; ψ is the format after the locations.
  `L.FmtP φ ψ`: through the list.
  `Spec.ldReqRefFmtL_segs`: for pp the characteristic of E (`[CharP E pp]`):
    `L.OK pp → L.FmtP φ ψ → L.Fmt φ ψ`.
  `T.FmtAt φ q`: the same for the last segment, up to the format at which the last three moves of a
    request begin.
  `Spec.ldReqRefFmtL_req`: for pp the characteristic of E: the request's chain has the format, from
    any format φ at the first stage to the object's format at the last, from: the first sendings'
    formats; `L.OK pp`, `L.FmtP`; `T.OK pp`, `T.FmtAt`.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefFmtP

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- A reference segment has the format from χ to ψ. The index is the further oracle of the body's
stages; the prover encoded index is the first part of their further witness; the record is the one
that the tensor rows' statement decodes with. -/
def LdRefS.FmtAt {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}
    (S : LdRefS E Kc I a) (χ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx a.J)
    (ψ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx S.d.J) : Prop :=
  ∃ (ρ : LdRefR S.A I.C.Rec) (r₁ : S.K.St₁ → I.C.Rec) (px' : S.Qc.Wp' → I.C.PIdx)
      (q : Finset S.A.Xa.Q.D.s0.Ex.Pos → Prop) (qm : Finset S.K.R.c1.fold.mid.E.Pos → Prop)
      (qc : Finset S.K.R.c1.fold.tgt.Ex.Pos → Prop) (q' : Finset S.Qc.loc.tgt.Ex.Pos → Prop),
    S.entry.Fmt χ (S.A.V.Fp.s0.fmt ⟨id, id⟩ ρ.rcV Prod.fst q) ∧
    ρ.Laws ∧
    (∀ st, ρ.rT st = S.A.rc st) ∧
    (∀ z, r₁ (S.K.fz z) = ρ.rT (S.A.X.stOf z).2) ∧
    S.l.Fmt (S.K.R.c1.fold.src.fmt ⟨id, id⟩ (fun st => r₁ st.2) Prod.fst
        ((S.A.Xa.Q.D.S.sum S.A.Xa.Q.D.N).qSum
          S.A.Xa.Q.D.N' (S.A.Xa.Q.D.S.qSum S.A.Xa.Q.D.N q S.A.Xa.Q.D.t) S.A.Xa.Q.D.t'))
      (S.K.R.c1.fold.fmtMid ⟨id, id⟩ r₁ Prod.fst qm) ∧
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ S.K.R.c1.fold.pE.src u) → qc U → qm V) ∧
    (∀ w, px' (S.Qc.Sn.rest w).2 = w.2.2.1) ∧
    (∀ ρ' U, q' U → S.K.R.c1.fold.tgt.S.qSum S.Qc.N qc S.Qc.tN (S.Qc.loc.link.R.need ρ' U)) ∧
    ψ = S.Qc.loc.tgt.fmt ⟨id, id⟩ (fun st => r₁ st.2) px' q'

def LdRefL.FmtP {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}
    (φ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx a.J) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → JFmt Kc I.C.E0 I.C.Rec I.C.PIdx b.J → Prop
  | _, .nil, ψ => φ = ψ
  | _, .snoc (b := b) L S, ψ => ∃ χ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx b.J, L.FmtP φ χ ∧ S.FmtAt χ ψ

/-- The last segment has the format, from φ to the format at which the last three moves begin. -/
def LdRefT.FmtAt {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b)
    (φ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J) (q' : Finset R.z.J.E.Pos → Prop) :
    Prop :=
  ∃ (ρ : LdRefR T.A R.Cf.conf.Rec)
      (r₁ : T.St₁ → R.Cf.conf.Rec) (q : Finset T.A.Xa.Q.D.s0.Ex.Pos → Prop),
    ρ.Laws ∧
    (∀ st, ρ.rT st = T.A.rc st) ∧
    (∀ z, r₁ (T.fz z) = ρ.rT (T.A.X.stOf z).2) ∧
    T.entry.Fmt φ (T.A.V.Fp.s0.fmt ⟨id, id⟩ ρ.rcV Prod.fst q) ∧
    T.exit.Fmt
      ((T.A.X.tgt T.St₁ T.Az).fmt ⟨id, id⟩ (fun x => r₁ x.2) Prod.fst
        ((T.A.Xa.Q.D.S.sum T.A.Xa.Q.D.N).qSum
          T.A.Xa.Q.D.N' (T.A.Xa.Q.D.S.qSum T.A.Xa.Q.D.N q T.A.Xa.Q.D.t) T.A.Xa.Q.D.t'))
      (R.X.src.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) (fun x => R.rc x.2.2) Prod.fst q')

namespace Spec

def ldReqRefFmtL_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a b : LdStage E Kc)
      (L : LdRefL E Kc I a b) (φ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx a.J)
      (ψ : JFmt Kc I.C.E0 I.C.Rec I.C.PIdx b.J),
    L.OK pp → L.FmtP φ ψ → L.Fmt φ ψ

def ldReqRefFmtL_req : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (q : Finset R.z.J.E.Pos → Prop)
      (φ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a.J)
      (φ₀ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx first.tgt.J)
      (φ₁ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a₁.J)
      (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
    first.link.Fmt φ φ₀ → more.Fmt φ₀ φ₁ → L.OK pp → L.FmtP φ₁ φb → T.OK pp → T.FmtAt φb q →
    (ldReqRef R first a₁ more hm b L T).chain.Fmt φ (R.O.fmtZAt R.bEnd Prod.fst q)

end Spec

theorem ldReqRefFmtL_segs : Spec.ldReqRefFmtL_segs := by
  intro E Kc _ _ pp _ I a b L φ
  induction L with
  | nil => intro ψ _ h; rw [LdRefL.FmtP] at h; rw [LdRefL.Fmt]; exact h
  | snoc L S ih =>
      intro ψ hO h
      rw [LdRefL.OK] at hO
      rw [LdRefL.FmtP] at h
      obtain ⟨χ, h1, ρ, r₁, px', q, qm, qc, q', e1, e2, -, e3, e4, e5, e6, e7, rfl⟩ := h
      rw [LdRefL.Fmt]
      exact ⟨χ, _, ih χ hO.1 h1, e1,
        ldReqRefFmtP_seg E Kc pp _ _ _ I S.A S.K S.l S.Qc ⟨id, id⟩ ρ r₁ Prod.fst px' q qm qc q'
          hO.2.body e2 e3 e4 e5 hO.2.snd e6 e7⟩

theorem ldReqRefFmtL_req : Spec.ldReqRefFmtL_req := by
  intro F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T q φ φ₀ φ₁ φb h1 h2 hL h3
    hT ⟨ρ, r₁, q₀, e1, _, e2, e3, e4⟩
  exact ldReqRefK_reqFmt F E Kc R a first a₁ more hm b L T q φ φ₀ φ₁ φb _ _ h1 h2
    (ldReqRefFmtL_segs E Kc pp _ _ _ L φ₁ φb hL h3) e3
    (ldSegRefAll_fmt E Kc pp _ _ _ _ T.A ⟨id, id⟩ ρ Prod.fst q₀ T.St₁ T.fz T.Az r₁ hT.body e1 e2) e4

end Cb
