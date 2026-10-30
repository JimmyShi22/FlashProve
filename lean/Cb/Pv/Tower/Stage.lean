-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Stage.lean: one stage of a proximity test (in a plan of rounds: "FOLD epsilon", "FOLD
round" once for each variable, "SEND seed", "CS") as one block: the form is cut, the fold, the code
switch; the statement that it is round-by-round knowledge sound, proved under conditions on codes
and numbers that no file here shows of any setting; and the seams between the blocks of a test.

The letters are those of a step of the library's concrete tower (`LdTowC.step`,
Cb/Obj/LdObjectTower.lean): the fold Y, one form sl on its input word, the radius e, the data S of a
switch that starts where the fold ends. The blocks are those of Cb/Pv/Tower/Fold.lean and
Cb/Pv/Tower/Cs.lean: short rounds; the switch's first message bears a rider for a later block.

Main names:
  `cutOwn Y sl e`, `cutRide Y sl e`: the library's step without rounds that cuts the form in two
    (`ldSplit`, Cb/Ld/LdTower.lean); the same while the fold's mask is handed on (Cb/Pv/Rider.lean).
  `stageOwn`, `stageRide`: cut, fold, switch in a row: the fold sends its fresh mask; the mask was
    sent earlier. `stageInOwn`, `stageInRide`, `stageOut`: the joints.
  `StageOwnKnow`, `StageRideKnow`: the statements: knowledge soundness alone.
  `stageOwn_know`, `stageRide_know`: they hold under the two clauses of the library's condition on a
    step of a tower (`LdTowC.HypK`, Cb/Ent/TowerKnow.lean).
  `cut_fold_seam`, `fold_cs_seam`, `cs_stage_seam`: the joints of neighbours are the same joint, by
    definition; the last: if the switch's new code is the next fold's input code (`swInto`) and its
    rider is that fold's mask. To the last step: `cs_base_seam` (Cb/Pv/Tower/Cs.lean).
  `StageSize E`, `s.HOwn`, `s.HRide`, `s.OK`, `s.hOwn`, `s.hRide`: what is public of a stage as one
    record; the two statements at a size; the conditions; the statements hold under them.
    `s.OKLocal`: the further condition for locality.
  Beside the statements, for both forms: `_point` (finitely many leaves), `_local` (under the three
  codes' laws, and if the new code's transformation reads what it declares), `_onOut`, `_rounds`
  (k + 3), `_errList` (the fold's errors, then the switch's two), `_vals`.

Limits: those of the two files named. The first stage of a test on a group of oracle messages, with
its arrangement of rows, is not treated here, nor the seam from the batching before a test to its
first stage. A stage whose switch bears no rider is not laid. Nothing on an honest prover.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tower.Fold
import Cb.Pv.Tower.Cs
import Cb.Pv.Rider
import Ior.SeqProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob Hiop IOR

/-! ## The cut -/

section Cut
variable {E P St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P)
  (sl : Slf E St Y.Cin.J) (e : ℕ)

/-- the joint with one form on the fold's input word -/
abbrev wholeJ : LdJoint E := ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e

/-- The step without rounds that cuts the form. -/
noncomputable def cutOwn : IOR (E × St) Y.Cin.ext (Y.reform sl).Xi (Y.reform sl).Cin.ext :=
  (ldSplit (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e).R

/-- The same while the fold's mask is handed on. -/
noncomputable def cutRide : IOR (E × St) (EiRide Y) (Y.reform sl).Xi (EiRide (Y.reform sl)) :=
  (cutOwn Y sl e).keepE Y.Cw.nat

/-- the input joints of a stage -/
noncomputable abbrev stageInOwn : IOR.Rels Unit (E × St) Y.Cin.ext Y.Cin.N.Wit :=
  (wholeJ Y sl e).rels

noncomputable abbrev stageInRide : IOR.Rels Unit (E × St) (EiRide Y) Y.Cin.N.Wit :=
  (wholeJ Y sl e).rels.keepE Y.Cw.nat

theorem cutOwn_know :
    (cutOwn Y sl e).red.Know (stageInOwn Y sl e).on (stageInOwn Y sl e).relR
      (inOwn (Y.reform sl) e).relR (fun _ _ w => w) () :=
  ldEnt_split_know E P St (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e

theorem cutRide_know :
    (cutRide Y sl e).red.Know (stageInRide Y sl e).on (stageInRide Y sl e).relR
      (inRide (Y.reform sl) e).relR (fun _ _ w => w) () :=
  know_keepE Y.Cw.nat (cutOwn Y sl e) (stageInOwn Y sl e) (inOwn (Y.reform sl) e) (fun _ _ w => w)
    () (cutOwn_know Y sl e)

/-- The seam from the cut to the fold: one joint. -/
theorem cut_fold_seam :
    (ldCut (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e).rels.keepE Y.Cw.nat =
      inRide (Y.reform sl) e := rfl

end Cut

/-! ## The stage -/

section Stage
variable {E P P' Pw St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
  [Nonempty P'] (Y : SumPar E P) (sl : Slf E St Y.Cin.J) (e : ℕ)
  (fx : Fin ((Y.reform sl).n + 1) × E) (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type)
  (lf : (S.D e).Cout.NP → Pt) (lfW : Cw.NP → Pt)

omit [Fintype P'] [Nonempty P'] in
/-- The seam from the fold to the switch: one joint. -/
theorem fold_cs_seam : outJ (Y.reform sl) e = ((S.D e).jIn e).rels := rfl

/-- One stage; the fold sends its fresh mask. -/
noncomputable def stageOwn :
    IOR (E × St) Y.Cin.ext (E × (S.D e).St') ((S.D e).Cout.ext.prod Cw.nat) :=
  ((cutOwn Y sl e).seq (foldOwn (Y.reform sl) fx)).seq (csRide (S.D e) Cw Pt lf lfW)

/-- One stage; the fold's mask was sent earlier. -/
noncomputable def stageRide :
    IOR (E × St) (EiRide Y) (E × (S.D e).St') ((S.D e).Cout.ext.prod Cw.nat) :=
  ((cutRide Y sl e).seq (foldRide (Y.reform sl) fx)).seq (csRide (S.D e) Cw Pt lf lfW)

/-- the output joint of a stage: the switch's -/
noncomputable abbrev stageOut (e' : ℕ) :
    IOR.Rels Unit (E × (S.D e).St') ((S.D e).Cout.ext.prod Cw.nat) ((S.D e).jOut e').W :=
  csOut (S.D e) Cw e'

variable (d : ℕ) (Lst mC mS mW : ℕ → ℕ) (e' L : ℕ)

/-- the extractors: the three blocks' in a row -/
noncomputable def stageExtOwn :
    (E × St) × Y.Cin.ext.Str → Tr (stageOwn Y sl e fx S Cw Pt lf lfW).shape →
      ((S.D e).jOut e').W → Y.Cin.N.Wit :=
  IOR.extSeq ((cutOwn Y sl e).seq (foldOwn (Y.reform sl) fx)) (csRide (S.D e) Cw Pt lf lfW)
    (IOR.extSeq (cutOwn Y sl e) (foldOwn (Y.reform sl) fx) (fun _ _ w => w)
      (extOwn (Y.reform sl) fx d 0) 0)
    (fun _ _ w' => (S.D e).back w') 0

noncomputable def stageExtRide :
    (E × St) × (EiRide Y).Str → Tr (stageRide Y sl e fx S Cw Pt lf lfW).shape →
      ((S.D e).jOut e').W → Y.Cin.N.Wit :=
  IOR.extSeq ((cutRide Y sl e).seq (foldRide (Y.reform sl) fx)) (csRide (S.D e) Cw Pt lf lfW)
    (IOR.extSeq (cutRide Y sl e) (foldRide (Y.reform sl) fx) (fun _ _ w => w)
      (extRide (Y.reform sl) fx d 0) 0)
    (fun _ _ w' => (S.D e).back w') 0

/-- the errors: the fold's, then the switch's two -/
noncomputable def stageErrOwn : Err (stageOwn Y sl e fx S Cw Pt lf lfW).shape :=
  Err.app (Err.app (s := (cutOwn Y sl e).shape) () (errOwn (Y.reform sl) fx Lst mC mS mW))
    (csErr (S.D e) Cw Pt lf lfW e L)

noncomputable def stageErrRide : Err (stageRide Y sl e fx S Cw Pt lf lfW).shape :=
  Err.app (Err.app (s := (cutRide Y sl e).shape) () (errRide (Y.reform sl) fx Lst mC mS mW))
    (csErr (S.D e) Cw Pt lf lfW e L)

/-- Round-by-round knowledge soundness of a stage whose fold sends its mask. -/
def StageOwnKnow : Prop :=
  (stageOwn Y sl e fx S Cw Pt lf lfW).red.Know (stageInOwn Y sl e).on (stageInOwn Y sl e).relR
    (stageOut Y sl e S Cw e').relR (stageExtOwn Y sl e fx S Cw Pt lf lfW d e')
    (stageErrOwn Y sl e fx S Cw Pt lf lfW Lst mC mS mW L)

/-- Round-by-round knowledge soundness of a stage whose fold's mask was sent earlier. -/
def StageRideKnow : Prop :=
  (stageRide Y sl e fx S Cw Pt lf lfW).red.Know (stageInRide Y sl e).on (stageInRide Y sl e).relR
    (stageOut Y sl e S Cw e').relR (stageExtRide Y sl e fx S Cw Pt lf lfW d e')
    (stageErrRide Y sl e fx S Cw Pt lf lfW Lst mC mS mW L)

theorem stageOwn_know (h₁ : (Y.reform sl).HypK d e Lst mC mS mW) (h₂ : (S.D e).HypK e' L) :
    StageOwnKnow Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (cutOwn_know Y sl e)
      (foldOwn_know (Y.reform sl) fx d e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    (cs_know (S.D e) Cw Pt lf lfW e e' L h₂) fun _ _ _ _ _ => trivial

theorem stageRide_know (h₁ : (Y.reform sl).HypK d e Lst mC mS mW) (h₂ : (S.D e).HypK e' L) :
    StageRideKnow Y sl e fx S Cw Pt lf lfW d Lst mC mS mW e' L :=
  know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0
    (know_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (cutRide_know Y sl e)
      (foldRide_know (Y.reform sl) fx d e Lst mC mS mW 0 h₁) fun _ _ _ _ _ => trivial)
    (cs_know (S.D e) Cw Pt lf lfW e e' L h₂) fun _ _ _ _ _ => trivial

end Stage

/-! ## Beside the statements -/

section Beside
variable {E P P' Pw St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
  [Nonempty P'] (Y : SumPar E P) (sl : Slf E St Y.Cin.J) (e : ℕ)
  (fx : Fin ((Y.reform sl).n + 1) × E) (S : LdSwD (Y.reform sl) P') (Cw : LdCode E Pw) (Pt : Type)
  (lf : (S.D e).Cout.NP → Pt) (lfW : Cw.NP → Pt)

theorem cutOwn_local : (cutOwn Y sl e).IsLocal :=
  (ldTower_split E P St (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e 0).1.good.isLocal

omit [Fintype P'] [Nonempty P'] in
theorem stageOwn_point [Fintype Pt] [DecidableEq Pt] :
    Nonempty (stageOwn Y sl e fx S Cw Pt lf lfW).shape.IsPoint :=
  (foldOwn_point (Y.reform sl) fx).elim fun p₁ => (cs_point (S.D e) Cw Pt lf lfW).elim fun p₂ =>
    ⟨Shape.IsPoint.append (Shape.IsPoint.append (s := (cutOwn Y sl e).shape) () p₁) p₂⟩

omit [Fintype P'] [Nonempty P'] in
theorem stageRide_point [Fintype Pt] [DecidableEq Pt] :
    Nonempty (stageRide Y sl e fx S Cw Pt lf lfW).shape.IsPoint :=
  (foldRide_point (Y.reform sl) fx).elim fun p₁ => (cs_point (S.D e) Cw Pt lf lfW).elim fun p₂ =>
    ⟨Shape.IsPoint.append (Shape.IsPoint.append (s := (cutRide Y sl e).shape) () p₁) p₂⟩

omit [Fintype P'] [Nonempty P'] in
theorem stageOwn_local (hC : Y.C.Laws) (hZ : Y.Z.Laws) (hW : Y.Zw.Laws)
    (hR : (S.D e).Cout.Reads) : (stageOwn Y sl e fx S Cw Pt lf lfW).IsLocal :=
  ((cutOwn_local Y sl e).seq (foldOwn_local (Y.reform sl) fx hC hZ hW)).seq
    (cs_isLocal (S.D e) Cw Pt lf lfW hR)

omit [Fintype P'] [Nonempty P'] in
theorem stageRide_local (hC : Y.C.Laws) (hZ : Y.Z.Laws) (hW : Y.Zw.Laws)
    (hR : (S.D e).Cout.Reads) : (stageRide Y sl e fx S Cw Pt lf lfW).IsLocal :=
  (((cutOwn_local Y sl e).keepE Y.Cw.nat).seq (foldRide_local (Y.reform sl) fx hC hZ hW)).seq
    (cs_isLocal (S.D e) Cw Pt lf lfW hR)

theorem stageOwn_onOut (e' : ℕ) : ∀ a τ b, (stageInOwn Y sl e).on a →
    (stageOwn Y sl e fx S Cw Pt lf lfW).red.out a τ = some b → (stageOut Y sl e S Cw e').on b :=
  fun _ _ _ _ _ => trivial

theorem stageRide_onOut (e' : ℕ) : ∀ a τ b, (stageInRide Y sl e).on a →
    (stageRide Y sl e fx S Cw Pt lf lfW).red.out a τ = some b → (stageOut Y sl e S Cw e').on b :=
  fun _ _ _ _ _ => trivial

omit [Fintype P'] [Nonempty P'] in
theorem stageOwn_rounds : (stageOwn Y sl e fx S Cw Pt lf lfW).shape.length = Y.k + 3 := by
  show (([] ++ (foldOwn (Y.reform sl) fx).shape) ++ (csRide (S.D e) Cw Pt lf lfW).shape).length = _
  rw [List.length_append, List.nil_append, foldOwn_rounds, cs_rounds]
  rfl

omit [Fintype P'] [Nonempty P'] in
theorem stageRide_rounds : (stageRide Y sl e fx S Cw Pt lf lfW).shape.length = Y.k + 3 := by
  show (([] ++ (foldRide (Y.reform sl) fx).shape) ++ (csRide (S.D e) Cw Pt lf lfW).shape).length = _
  rw [List.length_append, List.nil_append, foldRide_rounds, cs_rounds]
  rfl

omit [Fintype P'] [Nonempty P'] in
theorem stageOwn_errList (Lst mC mS mW : ℕ → ℕ) (L : ℕ) :
    (stageErrOwn Y sl e fx S Cw Pt lf lfW Lst mC mS mW L).toList =
      ((Y.reform sl).err Lst mC mS mW).toList ++ [(S.D e).W.err1 L, (S.D e).W.err2 e L] :=
  (Err.toList_app (Err.app (s := (cutOwn Y sl e).shape) () (errOwn (Y.reform sl) fx Lst mC mS mW))
      (csErr (S.D e) Cw Pt lf lfW e L)).trans
    (congrArg₂ (· ++ ·)
      ((Err.toList_app (s := (cutOwn Y sl e).shape) () (errOwn (Y.reform sl) fx Lst mC mS mW)).trans
        (errOwn_toList (Y.reform sl) fx Lst mC mS mW))
      (cs_errList (S.D e) Cw Pt lf lfW e L))

omit [Fintype P'] [Nonempty P'] in
theorem stageRide_errList (Lst mC mS mW : ℕ → ℕ) (L : ℕ) :
    (stageErrRide Y sl e fx S Cw Pt lf lfW Lst mC mS mW L).toList =
      ((Y.reform sl).err Lst mC mS mW).toList ++ [(S.D e).W.err1 L, (S.D e).W.err2 e L] :=
  (Err.toList_app (Err.app (s := (cutRide Y sl e).shape) () (errRide (Y.reform sl) fx Lst mC mS mW))
      (csErr (S.D e) Cw Pt lf lfW e L)).trans
    (congrArg₂ (· ++ ·)
      ((Err.toList_app (s := (cutRide Y sl e).shape) ()
          (errRide (Y.reform sl) fx Lst mC mS mW)).trans
        (errRide_toList (Y.reform sl) fx Lst mC mS mW))
      (cs_errList (S.D e) Cw Pt lf lfW e L))

omit [Fintype P'] [Nonempty P'] in
theorem stageOwn_vals : (stageOwn Y sl e fx S Cw Pt lf lfW).shape.chalList =
    List.replicate (Y.k + 1) (Fintype.card Y.Ch) ++
      [Fintype.card (S.D e).Zo.D, Fintype.card ((Fin (S.D e).t → P) × (S.D e).Zb.D)] := by
  show Shape.chalList (([] ++ (foldOwn (Y.reform sl) fx).shape) ++
    (csRide (S.D e) Cw Pt lf lfW).shape) = _
  rw [Shape.chalList_append, List.nil_append, foldOwn_vals, cs_vals]
  rfl

omit [Fintype P'] [Nonempty P'] in
theorem stageRide_vals : (stageRide Y sl e fx S Cw Pt lf lfW).shape.chalList =
    List.replicate (Y.k + 1) (Fintype.card Y.Ch) ++
      [Fintype.card (S.D e).Zo.D, Fintype.card ((Fin (S.D e).t → P) × (S.D e).Zb.D)] := by
  show Shape.chalList (([] ++ (foldRide (Y.reform sl) fx).shape) ++
    (csRide (S.D e) Cw Pt lf lfW).shape) = _
  rw [Shape.chalList_append, List.nil_append, foldRide_vals, cs_vals]
  rfl

end Beside

/-! ## The seam from a stage to the next -/

section Seam
variable {E P P' : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
  (Y₁ : SumPar E P) [Fintype Y₁.Cout.Aa] (Y₂ : SumPar E P') (Qo : Type) [Fintype Qo]
  [DecidableEq Qo] (place : (Y₁.Cout.J ⊕ Y₁.Cout.Q) ⊕ Qo ≃ Y₂.Cin.J)
  (Zo : Ood.Sample E ((Y₁.Cout.J ⊕ Y₁.Cout.Q) ⊕ Qo)) (ts : ℕ)
  (Zb : Evader E (LdRow Zo.S ts Y₁.Cout.Aa))

/-- A switch after the fold Y₁ whose new code is the input code of the fold Y₂. -/
@[reducible] def swInto : LdSwD Y₁ P' := ⟨Y₂.Cin, Qo, place, Zo, ts, Zb⟩

/-- The seam from a stage to the next: the switch's output joint, its rider the next fold's mask,
is the next stage's input joint, at the switch's new form and new radius. -/
theorem cs_stage_seam (e e' : ℕ) :
    csOut ((swInto Y₁ Y₂ Qo place Zo ts Zb).D e) Y₂.Cw e' =
      stageInRide Y₂ ((swInto Y₁ Y₂ Qo place Zo ts Zb).D e).sl' e' := rfl

end Seam

/-! ## The statement at a size -/

/-- What is public of a stage: the letters of a step of the library's concrete tower; which
coefficient is left out; the rider's code and the leaves (finitely many); the numbers of the
statement. -/
structure StageSize (E : Type) [Field E] [Fintype E] where
  P : Type
  P' : Type
  Pw : Type
  St : Type
  [finP : Fintype P]
  [neP : Nonempty P]
  [finP' : Fintype P']
  [neP' : Nonempty P']
  Y : SumPar E P
  sl : Slf E St Y.Cin.J
  e : ℕ
  fx : Fin ((Y.reform sl).n + 1) × E
  S : LdSwD (Y.reform sl) P'
  Cw : LdCode E Pw
  Pt : Type
  [finPt : Fintype Pt]
  [decPt : DecidableEq Pt]
  lf : (S.D e).Cout.NP → Pt
  lfW : Cw.NP → Pt
  d : ℕ
  Lst : ℕ → ℕ
  mC : ℕ → ℕ
  mS : ℕ → ℕ
  mW : ℕ → ℕ
  e' : ℕ
  L : ℕ

attribute [instance] StageSize.finP StageSize.neP StageSize.finP' StageSize.neP' StageSize.finPt
  StageSize.decPt

section Size
variable {E : Type} [Field E] [Fintype E] (s : StageSize E)

/-- The statement that a stage whose fold sends its mask, at the size s, is knowledge sound. -/
def StageSize.HOwn : Prop :=
  StageOwnKnow s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.Lst s.mC s.mS s.mW s.e' s.L

/-- The statement that a stage whose fold's mask was sent earlier, at the size s, is knowledge
sound. -/
def StageSize.HRide : Prop :=
  StageRideKnow s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.Lst s.mC s.mS s.mW s.e' s.L

/-- Conditions, as in the library's theorems on fold and switch, on public data alone. -/
def StageSize.OK : Prop :=
  (s.Y.reform s.sl).HypK s.d s.e s.Lst s.mC s.mS s.mW ∧ (s.S.D s.e).HypK s.e' s.L

/-- The further condition for locality: the new code's transformation reads what it declares. -/
def StageSize.OKLocal : Prop := (s.S.D s.e).Cout.Reads

theorem StageSize.hOwn (h : s.OK) : s.HOwn :=
  stageOwn_know s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.Lst s.mC s.mS s.mW s.e' s.L h.1 h.2

theorem StageSize.hRide (h : s.OK) : s.HRide :=
  stageRide_know s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.Lst s.mC s.mS s.mW s.e' s.L h.1
    h.2

end Size

#print axioms StageSize.hOwn
#print axioms StageSize.hRide
#print axioms stageOwn_local
#print axioms stageRide_local

end Cb.Pv.Tower
