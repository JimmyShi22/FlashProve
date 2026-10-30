-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSegTProofs.lean: proofs for Cb/Ld/LdLkpSegT.lean (the table's side of the lookup as one
block at the base (`BkA`, Cb/Ld/LdLkpTreeP.lean)).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The four parts' own theorems (the parts are listed in the head of Cb/Ld/LdLkpSegT.lean), joined by
the rule for two blocks in a row at the base (`segT_seq`); between them the joints are shown to be
equal records.

Main names (statements and hypotheses: Cb/Ld/LdLkpSegT.lean):
  `ldLkpSegT_good`: `Q.segT`, at the base: `BkA.Good`, without hypothesis.
  `ldLkpSegT_len`: the number of rounds.

Notation:
  `BkA.Good` (Cb/Ld/LdLkpTreeP.lean): `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
    extractor;
  `cj` (Cb/Ld/LdLkpKit.lean): a riding joint, and claims on the entries;
  `R0`: a joint (`Rels`, Ior/Chain.lean);
  `pr`: a map `Q.I.X → St`: `cj` reads R0 at `pr x`;
  `Ψ`, `ΨR`: predicates `Q.I.X → (Q.I.J → E) → Prop`, in `cj`'s places for the honest and for the
    relaxed relation.

Limits: what the head of Cb/Ld/LdLkpSegT.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpSegT
import Cb.Ld.LdLkpInstProofs
import Cb.Ld.LdLkpRootProofs
import Cb.Ld.LdLkpEndProofs
import Cb.Ld.LdLkpBitProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

/-- two good blocks at the base in a row -/
theorem segT_seq {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type} {a : BkA K M X₁ X₂ Ex Wp}
    {b : BkA K M X₂ X₃ Ex Wp} {A : Rels K X₁ Ex (M × Wp)} {B : Rels K X₂ Ex (M × Wp)}
    {C : Rels K X₃ Ex (M × Wp)} (ha : a.Good A B) (hb : b.Good B C) : (a.seq b).Good A C :=
  goodAt_seq_ext K M X₁ X₂ X₃ Ex Ex Ex Wp Wp Wp a.R b.R a.H b.H A B C _ _ (fun _ _ _ wp => wp)
    a.P b.P ha hb fun _ _ _ _ _ _ _ => rfl

section
variable (E : Type) [Field E] [Fintype E]

/-- the point of the forest and the levels below l, beside any joint -/
theorem segT_forest (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → Q.I.J → E)
    (R1 : Rels Kc Q.I.X Ex (M × Wp)) (l : ℕ) :
    (Q.forest Ex Wp Kc msg l).Good
      ⟨fun st y w => R1.rel st y w ∧ Q.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ Q.R.Holds a.1 (msg w.1),
        R1.on, R1.core⟩
      (Q.D.jtAt msg (Q.R.toIn.ride R1) l) := by
  induction l with
  | zero => exact ldLkpRoot_good E Q.R Ex M Wp Kc R1 msg (ldLkpInst_stepT E Q.I) fun _ _ _ => rfl
  | succ l ih =>
    exact segT_seq ih
      (ldLkpP_level E Q.D Ex M Wp Kc msg (Q.R.toIn.ride R1) l (ldLkpInst_stepT E Q.I))

/-- the list of rows says: the bit test's output rows, the closing's output rows, the rows of the
forest -/
theorem segT_rows (Q : SegTab E) (o : Q.XB) (m : Q.I.J → E) :
    RowsHold (Q.rowsT o) m ↔
    Q.Bt.zc.next.par.OutHolds o m ∧
    Q.En.psc.par.OutHolds (Q.outE o) m ∧
    RowsHold (Q.D.rowsAt Q.I.d (Q.outE o).st) m := by
  rw [ldLkpBit_rows E Q.Bt o m, ldLkpEnd_rows E Q.En (Q.outE o) m]
  unfold RowsHold SegTab.rowsT
  simp only [List.forall_mem_cons]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩,
    fun h => ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩⟩

theorem ldLkpSegT_good : Spec.ldLkpSegT_good E := by
  intro Q Ex M Wp Kc St R0 msg pr Ψ ΨR
  -- what rides through the forest: the caller's joint, Ψ, and "all bits are bits"
  let R1 : Rels Kc Q.I.X Ex (M × Wp) :=
    cj R0 msg pr (fun x m => Ψ x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m)) fun x m =>
      ΨR x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m)
  let A0 : Rels Kc (Q.D.lv 0).T.St Ex (M × Wp) := Q.R.toIn.ride R1
  let A1 : Rels Kc (Q.D.lv Q.I.d).T.St Ex (M × Wp) := Q.D.ride msg A0 Q.I.d
  -- what rides through the bit test
  let R2 : Rels Kc Q.XE Ex (M × Wp) :=
    cj R0 msg (fun oE : Q.XE => pr (Q.D.root Q.I.d oE.st).1)
      (fun oE m =>
        (Ψ (Q.D.root Q.I.d oE.st).1 m ∧ RowsHold (Q.D.rowsAt Q.I.d oE.st) m) ∧
        Q.En.psc.par.OutHolds oE m) fun oE m =>
          (ΨR (Q.D.root Q.I.d oE.st).1 m ∧ RowsHold (Q.D.rowsAt Q.I.d oE.st) m) ∧
          Q.En.psc.par.OutHolds oE m
  have g1 := segT_forest E Q Ex M Wp Kc msg R1 Q.I.d
  have g2 : (Q.endA Ex Wp Kc msg).Good
      (Q.En.relsIn A1 fun w => msg w.1) (Q.En.psc.par.baseOut A1 fun w => msg w.1) :=
    ldLkpEnd_goodAt E Q.En Ex M Wp Kc A1 msg
  have g3 : (Q.bitA Ex Wp Kc msg).Good
      ⟨fun st y w => R2.rel st y w ∧ Q.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ Q.Bt.AllBits (msg w.1),
        R2.on, R2.core⟩
      (Q.Bt.zc.next.par.baseOut (Q.Bt.zc.toIn.ride R2) fun w => msg w.1) :=
    ldLkpBit_goodAt E Q.Bt Ex M Wp Kc R2 msg
  have hb : ∀ m, Q.Bt.AllBits m ↔ Bits Q.I.d Q.I.w (Q.I.bit m) := fun m =>
    ldLkpInst_bits E Q.I _ Q.wB Q.cB m
  obtain ⟨r1, r2, r3, r4⟩ := ldLkpP_ride E Q.D Ex M Wp Kc msg A0 Q.I.d
  have e0 : (⟨fun st y w => R1.rel st y w ∧ Q.R.Holds st (msg w.1),
        fun a w => R1.relR a w ∧ Q.R.Holds a.1 (msg w.1),
        R1.on,
        R1.core⟩ : Rels Kc Q.I.X Ex (M × Wp)) =
      cj R0 msg pr (fun x m => Ψ x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m) ∧ Q.R.Holds x m)
        fun x m => ΨR x m ∧ Bits Q.I.d Q.I.w (Q.I.bit m) ∧ Q.R.Holds x m :=
    LdLkp.rels_ext (funext fun _ =>
        funext fun _ =>
          funext fun _ =>
            propext
              ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
      (funext fun _ =>
        funext fun _ =>
          propext
            ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
      rfl rfl
  have e1 : Q.D.jtAt msg A0 Q.I.d = Q.En.relsIn A1 fun w => msg w.1 :=
    ldLkpInst_topT E Q.I Q.wE Q.cE Ex M Wp Kc msg A0
  have e2 : Q.En.psc.par.baseOut A1 (fun w => msg w.1) =
      (⟨fun st y w => R2.rel st y w ∧ Q.Bt.AllBits (msg w.1),
        fun a w => R2.relR a w ∧ Q.Bt.AllBits (msg w.1),
        R2.on,
        R2.core⟩ : Rels Kc Q.XE Ex (M × Wp)) := by
    refine LdLkp.rels_ext (funext fun o => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) (funext fun a => propext (r3 a.1.st a.2)) r4
    · show A1.rel o.st y w ∧ Q.En.psc.par.OutHolds o (msg w.1) ↔ _
      rw [r1]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
    · show A1.relR (a.1.st, a.2) w ∧ Q.En.psc.par.OutHolds a.1 (msg w.1) ↔ _
      rw [r2]
      exact ⟨fun h => ⟨⟨h.1.1.1, ⟨h.1.1.2.1, h.1.2⟩, h.2⟩, (hb _).2 h.1.1.2.2⟩,
        fun h => ⟨⟨⟨h.1.1, h.1.2.1.1, (hb _).1 h.2⟩, h.1.2.1.2⟩, h.1.2.2⟩⟩
  have e3 : Q.Bt.zc.next.par.baseOut (Q.Bt.zc.toIn.ride R2) (fun w => msg w.1) =
      cj R0 msg (fun o => pr (Q.oldT o)) (fun o m => Ψ (Q.oldT o) m ∧ RowsHold (Q.rowsT o) m)
        fun o m => ΨR (Q.oldT o) m ∧ RowsHold (Q.rowsT o) m := by
    refine LdLkp.rels_ext (funext fun o => funext fun y => funext fun w => propext ?_)
      (funext fun a => funext fun w => propext ?_) rfl rfl
    · show R2.rel (Q.outE o) y w ∧ Q.Bt.zc.next.par.OutHolds o (msg w.1) ↔
        R0.rel (pr (Q.oldT o)) y w ∧ Ψ (Q.oldT o) (msg w.1) ∧ RowsHold (Q.rowsT o) (msg w.1)
      rw [segT_rows]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
    · show R2.relR (Q.outE a.1, a.2) w ∧ Q.Bt.zc.next.par.OutHolds a.1 (msg w.1) ↔
        R0.relR (pr (Q.oldT a.1), a.2) w ∧
        ΨR (Q.oldT a.1) (msg w.1) ∧
        RowsHold (Q.rowsT a.1) (msg w.1)
      rw [segT_rows]
      exact ⟨fun h => ⟨h.1.1, h.1.2.1.1, h.2, h.1.2.2, h.1.2.1.2⟩,
        fun h => ⟨⟨h.1, ⟨h.2.1, h.2.2.2.2⟩, h.2.2.2.1⟩, h.2.2.1⟩⟩
  rw [e0, e1] at g1
  rw [e2] at g2
  rw [e3] at g3
  exact segT_seq (segT_seq g1 g2) g3

theorem segT_forest_len (Q : SegTab E) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → Q.I.J → E) (l : ℕ) :
    (Q.forest Ex Wp Kc msg l).R.shape.length = 1 + ∑ i ∈ Finset.range l, (Q.I.w + i + 3 + 1) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      have hl : (Q.D.levA Ex Wp Kc msg l).R.shape.length = Q.I.w + l + 3 + 1 := by
        have e : (Q.D.levA Ex Wp Kc msg l).R.shape =
            ((Q.D.lv l).T.par.psc Ex).shape ++ (Q.D.lineA Ex M Wp Kc l).R.shape := rfl
        rw [e, List.length_append, psc_our_len E (Q.D.lv l).T Ex, Q.D.fmt_len l]
        rfl
      have e : (Q.forest Ex Wp Kc msg (l + 1)).R.shape =
          (Q.forest Ex Wp Kc msg l).R.shape ++ (Q.D.levA Ex Wp Kc msg l).R.shape := rfl
      rw [e, List.length_append, ih, hl, Finset.sum_range_succ]
      exact Nat.add_assoc _ _ _

theorem ldLkpSegT_len : Spec.ldLkpSegT_len E := by
  intro Q Ex M Wp Kc msg
  have e : (Q.segT Ex Wp Kc msg).R.shape =
      ((Q.forest Ex Wp Kc msg Q.I.d).R.shape ++ (Q.En.psc.par.psc Ex).shape) ++
        ([IOR.drawRound Q.Bt.zc.toIn.ev.D] ++ (Q.Bt.zc.next.par.psc Ex).shape) := rfl
  rw [e, List.length_append, List.length_append, List.length_append, segT_forest_len,
    ldLkpEnd_len E Q.En Ex, psc_our_len E Q.Bt.zc.next Ex]
  show _ + (Q.I.w + Q.I.d + 3) + (1 + ((List.replicate (Q.I.w + Q.I.d) (pfCube E 2)).length + 3)) =
    _
  rw [List.length_replicate]

end
end Cb
