-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaConv.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean): the converses for a request's preamble: what is at most κ as a whole is at most κ
part by part, down to the five clauses of the reference request's record. The quoted words say e ≤ κ
· v, with e the round's error, a count of values of its verifier message (`Err`, Iop/Rbr.lean), and
v the number of all values of that message. These errors are numbers that a link lists (the data
field `Link.P.err`; `Nums.err`, Ior/Chain.lean) or that a statement writes out (among them
`ldSendFamErr ..`, `D.p.err`, `D.Z.err`): that a link is sound at the numbers that it lists is no
statement of this file; for a request's preamble, under `r.Hyp`, that tie is `Spec.ldReqStart_goodB`
(Cb/Req1/LdReqStart.lean) (that condition itself asks soundness of some of the parts one level
down: for these the tie carries soundness, it does not found it).

Theorems: the rules of Cb/Req1/LdReqBelow.lean, Cb/Req1/LdReqRefZk.lean,
Cb/Req1/LdSegBelowRef.lean, Cb/Req1/LdSegRefBelow.lean, Cb/Req1/LdReqRefFinal.lean read backwards.
Framework and definitions only; nothing is evaluated.

Why: these files carry "at most κ" from the blocks to the whole. To know that nothing is lost on
the way (that the clauses can be met at κ := the largest round error itself) one needs the way
back.

Main names:
  `Err.below_app_iff`, `chain_errBelow_iff`: equivalences: two lists of errors in a row are, as
    probabilities, at most κ if and only if both are; a chain as one link if and only if each of
    its links is.
  `ldReq_below_iff`: `r.Below κ` ↔ every round's error of `r.FP w₀`, as a probability, is at most κ.
  `ldKappaConv_rr`, `ldKappaConv_dg`, `ldKappaConv_tn`, `ldKappaConv_body`: a body (`LdBodyD`) and
    its parts (`LdRrD`, `LdDgP`, `LdTenD`), backwards.
  `ldKappaConv_all`: the closed body (`LdRefD`; `LdRefD.Nums`, Cb/Req1/LdSegRefBelow.lean):
    `(A.body St₁ fz Az).Below κ` → `A.Nums κ`.
  `ldKappaConv_segs`: the list of reference segments: `L.segs.Below κ` → `L.Nums κ`.
  `ldKappaConv_req`: `(ldReqRef R first a₁ more hm b L T).Below κ` → the five clauses bFirst,
    bMore, bSegs, bTail, bLast (`LdReqRefD`, Cb/Req1/LdReqRefFinal.lean) at κ.

Limits: this file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefFinal

set_option autoImplicit false

namespace Iop
open scoped ENNReal

theorem Err.below_app_iff :
    ∀ {s t : Shape} (ε : Err s) (ε' : Err t) (κ : ℝ≥0∞),
      Err.Below (Err.app ε ε') κ ↔ Err.Below ε κ ∧ Err.Below ε' κ
  | [], _, _, _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, (_, ε), ε', κ =>
    ⟨fun h => ⟨⟨h.1, ((Err.below_app_iff ε ε' κ).1 h.2).1⟩, ((Err.below_app_iff ε ε' κ).1 h.2).2⟩,
      fun h => ⟨h.1.1, (Err.below_app_iff ε ε' κ).2 ⟨h.1.2, h.2⟩⟩⟩

open IOR IOR.Chain in
theorem chain_errBelow_iff {K : Type} {A B : Joint K} (c : Chain K A B) (d : A.W) (κ : ℝ≥0∞) :
    Err.Below (c.link d).P.err κ ↔ c.ErrBelow κ := by
  induction c with
  | one l => rw [link_one, errBelow_one]
  | snoc c l ih =>
      rw [link_snoc, errBelow_snoc, ← ih]
      exact Err.below_app_iff (c.link d).P.err l.P.err κ

end Iop

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E] {A : Joint Kc}

theorem LdProg.below_app_iff {a b c : LdStage E Kc} (p : LdProg a b) (q : LdProg b c) (κ : ℝ≥0∞) :
    (p.app q).Below κ ↔ p.Below κ ∧ q.Below κ := by
  induction q with
  | nil => rw [LdProg.app_nil]; exact ⟨fun h => ⟨h, LdProg.below_nil _ κ⟩, fun h => h.1⟩
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.below_snoc, LdProg.below_snoc, ih, and_assoc]

theorem LdProg.asSub_below_iff {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) :
    p.asSub.Below κ ↔ p.Below κ := by
  induction p with
  | nil => rw [LdProg.asSub_nil]
  | snoc p m ih =>
      rw [LdProg.asSub_snoc, LdProg.below_snoc, LdProg.below_snoc, ih]
      exact Iff.rfl

theorem LdProg.onto_below_iff
    {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) (c₀ : Chain Kc A a.J) :
    (p.onto c₀).ErrBelow κ ↔ c₀.ErrBelow κ ∧ p.Below κ := by
  induction p with
  | nil => rw [LdProg.onto_nil]; exact ⟨fun h => ⟨h, LdProg.below_nil _ κ⟩, fun h => h.1⟩
  | snoc p m ih => rw [LdProg.onto_snoc, errBelow_append, ih, LdProg.below_snoc, and_assoc]

theorem LdSeg.onto_below_iff {a d : LdStage E Kc} (s : LdSeg a d) (κ : ℝ≥0∞) (c₀ : Chain Kc A a.J) :
    (s.onto c₀).ErrBelow κ ↔ c₀.ErrBelow κ ∧ s.Below κ := by
  unfold LdSeg.onto
  rw [LdProg.onto_below_iff, errBelow_snoc, LdProg.onto_below_iff,
    LdProg.onto_below_iff, LdProg.onto_below_iff]
  exact ⟨fun h => ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨⟨h.1, h.2.body⟩, h.2.bat⟩, h.2.fold⟩, h.2.snd⟩, h.2.loc⟩⟩

theorem LdSegs.onto_below_iff
    {a b : LdStage E Kc} (S : LdSegs a b) (κ : ℝ≥0∞) (c₀ : Chain Kc A a.J) :
    (S.onto c₀).ErrBelow κ ↔ c₀.ErrBelow κ ∧ S.Below κ := by
  induction S with
  | nil => rw [LdSegs.onto_nil, LdSegs.Below]; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | snoc S s ih => rw [LdSegs.onto_snoc, LdSeg.onto_below_iff, ih, LdSegs.below_snoc, and_assoc]

theorem LdReq.chain_below_iff {a z : LdStage E Kc} (r : LdReq a z) (κ : ℝ≥0∞) :
    r.chain.ErrBelow κ ↔ r.Below κ := by
  unfold LdReq.chain
  rw [LdProg.onto_below_iff, LdSegs.onto_below_iff, LdProg.onto_below_iff, errBelow_one]
  exact ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.first, h.more⟩, h.segs⟩, h.last⟩⟩

end

theorem ldReq_below_iff {E Kc : Type} [Field E] [Fintype E] {Xi Wi : Type}
    {E0 : ExtSpec} (A : Rels Kc Xi E0 Wi) (z : LdStage E Kc)
    (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi) (κ : ℝ≥0∞) :
    Err.Below (r.FP w₀).err κ ↔ r.Below κ :=
  (chain_errBelow_iff r.chain (ldStartW _ w₀) κ).trans (r.chain_below_iff κ)

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem ldKappaConv_rr {E₀ : ExtSpec} {Wp : Type} (D : LdRrD E Kc E₀ Wp)
    (κ : ℝ≥0∞) (h : D.prog.Below κ) :
    (ldSendFamErr D.N D.Sd D.L : ℝ≥0∞) ≤ κ * (Fintype.card D.Sd.D : ℝ≥0∞) ∧
    (D.p.err : ℝ≥0∞) ≤ κ * (Fintype.card D.p.Chal : ℝ≥0∞) ∧
    (ldSendFamErr D.N' D.Sd' D.L' : ℝ≥0∞) ≤ κ * (Fintype.card D.Sd'.D : ℝ≥0∞) := by
  obtain ⟨hs, _, _, _, _, _⟩ := ldSeg_below_named E Kc κ
  have c2 : (LdMv.send D.s1 D.d1).chain = .one D.d1.link := by rw [LdMv.chain]
  have c3 : (LdMv.sub D.s2 D.s3 (.one D.draw)).chain = .one D.draw := by rw [LdMv.chain]
  have c4 : (LdMv.send D.s3v D.d3).chain = .one D.d3.link := by rw [LdMv.chain]
  unfold LdRrD.prog LdRrD.derive at h
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc,
    c2, c3, c4, errBelow_one, errBelow_one, errBelow_one] at h
  exact ⟨(hs D.s1 D.d1).1 h.1.1.1.2, h.1.1.2.1, (hs D.s3v D.d3).1 h.2⟩

theorem ldKappaConv_dg {E₀ : ExtSpec} {Wp : Type} (Q : LdDgP E Kc E₀ Wp)
    (mult : Q.X₄ × E → Cb.LdLkp.Ms Q.T E₀ → Prop) (ent : Cb.LdLkp.Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
    (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (κ : ℝ≥0∞) (h : (Q.prog mult ent n lk).Below κ) :
    ((2 ^ (1 + Q.d) : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞) ∧ lk.ErrBelow κ := by
  have c2 : (LdMv.sub Q.u0 Q.u1 (.one Q.shift)).chain = .one Q.shift := by rw [LdMv.chain]
  have c4 : (LdMv.sub (Q.lkS mult) (Q.lkT ent n) lk).chain = lk := by rw [LdMv.chain]
  unfold LdDgP.prog LdDgP.pre LdDgP.stepA LdDgP.stepB at h
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc,
    c2, c4, errBelow_one] at h
  exact ⟨h.1.1.2.1, h.2⟩

theorem ldKappaConv_tn (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (κ : ℝ≥0∞)
    (h : (X.prog St₁ fz Az).Below κ) :
    Err.Below (X.bt.nums X.C.E0 Kc).err κ := by
  have c2 : (LdMv.sub X.m0 X.m1 (.one X.link)).chain = .one X.link := by rw [LdMv.chain]
  unfold LdTenD.prog LdTenD.stepIn LdTenD.stepOut at h
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc, c2, errBelow_one] at h
  exact h.1.2

theorem ldKappaConv_body {E₀ : ExtSpec} {Wp : Type} (Y : LdBodyD E Kc E₀ Wp) (z : LdStage E Kc)
    (tensor : LdProg Y.tgt z) (κ : ℝ≥0∞) (h : (Y.body z tensor).Below κ) :
    Y.front.Below κ ∧ Y.G.Q.D.prog.Below κ ∧
    (Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk).Below κ ∧ tensor.Below κ := by
  unfold LdBodyD.body at h
  rw [LdProg.below_app_iff, LdProg.below_snoc, LdProg.below_app_iff, LdProg.below_app_iff] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.2⟩

/-- The closed body, backwards. -/
theorem ldKappaConv_all {I : LdRefIx E} (A : LdRefD E Kc I) (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))) (κ : ℝ≥0∞)
    (h : (A.body St₁ fz Az).Below κ) : A.Nums κ := by
  obtain ⟨h1, h2, h3, h4⟩ := ldKappaConv_body A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az) κ h
  obtain ⟨r1, r2, r3⟩ := ldKappaConv_rr A.Xa.Q.D κ h2
  obtain ⟨d1, d2⟩ := ldKappaConv_dg A.Xa.Q A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk κ h3
  exact ⟨h1, r1, r2, r3, d1, (errBelow_one A.Xa.link κ).1 d2, ldKappaConv_tn A.X St₁ fz Az κ h4⟩

/-- a segment with one group, backwards -/
theorem ldKappaConv_one (a : LdStage E Kc) (D : LdCl1 E Kc) (body : LdProg a D.bat.src)
    (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step) (l : Link Kc D.fold.src.J D.fold.mid)
    (Q : LdCloseD D.fold) (κ : ℝ≥0∞) (h : (segOne D body hT l Q).Below κ) :
    body.Below κ ∧
    (D.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞) ∧
    Err.Below l.P.err κ ∧
    (ldSendFamErr Q.N Q.Sd Q.L : ℝ≥0∞) ≤ κ * (Fintype.card Q.Sd.D : ℝ≥0∞) ∧
    (((Fintype.card D.Pf - D.e - 1) ^ Q.t : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin Q.t → D.Pf) : ℝ≥0∞) := by
  obtain ⟨n1, n2, -, n4, n5, -⟩ := ldSeg_below_named E Kc κ
  have hb : D.batP.Below κ := h.bat
  have hf : (Q.foldP l).Below κ := h.fold
  have hl : Q.locP.Below κ := h.loc
  unfold LdCl1.batP at hb
  unfold LdCloseD.foldP at hf
  unfold LdCloseD.locP at hl
  rw [LdProg.below_snoc, LdProg.below_snoc] at hb
  rw [LdProg.below_snoc] at hf hl
  exact ⟨h.body,
    (n2 D.bat).1 ((errBelow_one _ κ).1 hb.1.2),
    (n5 D.fold l).1 ((errBelow_one _ κ).1 hf.2),
    (n1 D.fold.tgt Q.snd).1 h.snd,
    (n4 Q.loc).1 ((errBelow_one _ κ).1 hl.2)⟩

/-- the list of reference segments, backwards -/
theorem ldKappaConv_segs {I : LdRefIx E} {a b : LdStage E Kc} (L : LdRefL E Kc I a b) (κ : ℝ≥0∞) :
    L.segs.Below κ → L.Nums κ := by
  induction L with
  | nil => intro _; rw [LdRefL.Nums]; trivial
  | snoc L S ih =>
      intro h
      rw [LdRefL.segs, LdSegs.Below] at h
      rw [LdRefL.Nums]
      have hb : (((LdProg.nil _).snoc S.entry).app (S.K.seg S.l S.Qc).body).Below κ := h.2.body
      have hs : (S.K.seg S.l S.Qc).Below κ :=
        ⟨((LdProg.below_app_iff _ _ κ).1 hb).2, h.2.bat, h.2.fold, h.2.snd, h.2.loc⟩
      obtain ⟨s1, s2, s3, s4, s5⟩ :=
        ldKappaConv_one S.A.V.Fp.s0 S.K.R.c1
          (S.K.R.Y.body S.K.R.c1.bat.src S.K.tensor) S.K.kinds S.l S.Qc κ hs
      exact ⟨ih h.1, ldKappaConv_all S.A S.K.St₁ S.K.fz S.K.Az κ s1, s2, s3, s4, s5⟩

end

/-- The reference request, backwards: the five clauses. -/
theorem ldKappaConv_req {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
    (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) (κ : ℝ≥0∞)
    (h : (ldReqRef R first a₁ more hm b L T).Below κ) :
    (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞) ∧
    more.Below κ ∧ L.Nums κ ∧ T.A.Nums κ ∧
    Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ := by
  have hl : (T.tail.app R.lastP).asSub.Below κ := h.last
  rw [LdProg.asSub_below_iff, LdProg.below_app_iff] at hl
  obtain ⟨t1, t2⟩ := hl
  unfold LdRefT.tail at t1
  rw [LdProg.below_snoc, LdProg.below_app_iff] at t1
  unfold LdORE.lastP at t2
  rw [LdProg.below_snoc, LdProg.below_snoc, LdProg.below_snoc] at t2
  exact ⟨((ldSeg_below_named E Kc κ).1 _ first).1 h.first,
    h.more,
    ldKappaConv_segs L κ h.segs,
    ldKappaConv_all T.A T.St₁ T.fz T.Az κ t1.1.2,
    (errBelow_one _ κ).1 t2.1.2⟩

end Cb
