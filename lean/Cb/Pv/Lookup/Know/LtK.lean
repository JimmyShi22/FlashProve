-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/LtK.lean.
The parts of a lookup, each over a sumcheck that is a letter: knowledge soundness alone.

PscLtK gives for each sumcheck's parameters a verifier with its errors, in two forms: with the round
of shown values, and without it. What is asked of it (FullK, CoreK) is knowledge soundness between
the sumcheck's own two joints.

States: the tie, the head, a level of a tree, a tree, the keys' side, a draw followed by a sumcheck,
the test on bits and the closing as blocks over the letter, each with its knowledge soundness
between the library's joints
  (tieK_step, tieK_chain, headK_know, ldLkpK_level', ldLkpK_tree', segKK_know, pscInK_know,
    bitPK_know, endMK_know). PscLtK.lib: the library's own sumcheck as a value of the letter;
    lib_fullK, lib_coreK, lib_ourK: it meets FullK and CoreK under the library's three conditions
    (VarsOK, DegOK, ValInj, Cb/Ld/LdPsc.lean).
Premises: each statement asks FullK or CoreK of the letter at the sumchecks that its block runs. No
statement has a premise on an honest prover.
Limits: a statement for every letter says nothing on what a verifier accepts. endMK_know only
renames the closing's input joint (endM_joint, Cb/Pv/Lookup/Blocks/EndM.lean): its conclusion is its
premise at that joint.
Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Lookup.Blocks.HeadF
import Cb.Pv.Lookup.Blocks.EndM
import Cb.Pv.Lookup.Blocks.E3Bit
import Cb.Ld.LdLkpSegK
import Cb.Ld.LdLkpTreePProofs
import Cb.Ld.LdLineAt
import Cb.Pv.Lookup.Know.KnowAt

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Kn TWhole

noncomputable section

/-- The sumcheck as a letter, the verifier's side alone, in its two forms. -/
structure PscLtK (E : Type) [Field E] [Fintype E] (Ex : ExtSpec) where
  full : (Y : PscPar E) → BkK (E × Y.St) Y.Out Ex
  core : (Y : PscPar E) → BkK (E × Y.St) Y.Mid Ex

namespace PscLtK
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (SK : PscLtK E Ex) (M Wp Kc : Type)

def FullK (Y : PscPar E) (msg : M → Y.J → E) : Prop :=
  ∀ A0 : Rels Kc Y.St Ex (M × Wp),
    (SK.full Y).Know (Y.baseIn A0 fun w => msg w.1) (Y.baseOut A0 fun w => msg w.1)

def CoreK (Y : PscPar E) (msg : M → Y.J → E) : Prop :=
  ∀ A0 : Rels Kc Y.St Ex (M × Wp),
    (SK.core Y).Know (Y.baseIn A0 fun w => msg w.1) (Y.baseMid A0 fun w => msg w.1)

theorem our_know (T : PscOur E) (msg : M → T.J → E) (h : SK.FullK M Wp Kc T.par msg)
    (A0 : Rels Kc T.St Ex (M × Wp)) :
    (SK.full T.par).Know (T.baseIn A0 fun w => msg w.1) (T.par.baseOut A0 fun w => msg w.1) := by
  have e : T.SumHolds = T.par.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m).symm
  unfold PscOur.baseIn
  rw [e]
  exact h A0

end PscLtK

/-- The library's two verifiers, with their errors. -/
def PscLtK.lib (E : Type) [Field E] [Fintype E] (Ex : ExtSpec) : PscLtK E Ex :=
  ⟨fun Y => ⟨Y.psc Ex, Y.err Ex⟩, fun Y => ⟨Y.core Ex, Y.errC Ex⟩⟩

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

theorem PscLtK.lib_fullK (M Wp Kc : Type) (Y : PscPar E) (msg : M → Y.J → E) (h1 : Y.VarsOK)
    (h2 : Y.DegOK) (h3 : Y.ValInj) : (PscLtK.lib E Ex).FullK M Wp Kc Y msg := fun A0 =>
  ((goodAt_iff _ _ _ _ _ _).1 (psc_goodAt E Y Ex M Wp Kc A0 msg h1 h2 h3)).1

theorem PscLtK.lib_coreK (M Wp Kc : Type) (Y : PscPar E) (msg : M → Y.J → E) (h1 : Y.VarsOK)
    (h2 : Y.DegOK) (h3 : Y.ValInj) : (PscLtK.lib E Ex).CoreK M Wp Kc Y msg := fun A0 =>
  ((goodAt_iff _ _ _ _ _ _).1 (psc_core_goodAt E Y Ex M Wp Kc A0 msg h1 h2 h3)).1

theorem PscLtK.lib_ourK (M Wp Kc : Type) (T : PscOur E) (msg : M → T.J → E) (hV : T.VarsOK)
    (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj) : (PscLtK.lib E Ex).FullK M Wp Kc T.par msg :=
  PscLtK.lib_fullK M Wp Kc T.par msg ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY)
    ((psc_our_ok E T).2 hI)

/-! ### the blocks -/

namespace TieF
variable (D : TieF E) (SK : PscLtK E Ex)

def stepK (l : ℕ) : BkK (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex :=
  (SK.full (D.lv l).T.par).postM (D.nxt l)

def tieK (n : ℕ) : BkK (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex :=
  BkK.chain (fun l => E × (D.lv l).T.St) (D.stepK SK) n

def LtK {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) : Prop :=
  ∀ l ≤ n, SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l)

end TieF

def LkHeadF.headK (H : LkHeadF E) (SK : PscLtK E Ex) : BkK H.St (E × (H.tie.lv (H.n + 1)).T.St) Ex
    :=
  (drawK E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1)).seq
    ((H.tie.tieK SK H.n).preM fun x => ((0 : E), x))

namespace TreeP
variable (D : TreeP E) (SK : PscLtK E Ex)

variable (Ex) in
def lineK (l : ℕ) : BkK (D.lv l).T.par.Out (E × (D.lv (l + 1)).T.St) Ex :=
  drawK (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err

def levK (l : ℕ) : BkK (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex :=
  (SK.full (D.lv l).T.par).seq (D.lineK Ex l)

def treeK (n : ℕ) : BkK (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex :=
  BkK.chain (fun l => E × (D.lv l).T.St) (D.levK SK) n

def LtK {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) : Prop :=
  ∀ l ≤ n, SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l)

end TreeP

def segKK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (SK : PscLtK E Ex) :
    BkK I.X (E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) Ex :=
  ((I.setV (v' + 1)).DK.treeK SK v').preM (enterK (I.setV (v' + 1)) tK)

def chainK (Z : PscIn E) (SK : PscLtK E Ex) : BkK Z.St0 Z.T.par.Out Ex :=
  (drawK Z.ev.D Z.nxX Ex Z.ev.err).seq (SK.full Z.T.par)

end
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

section
variable (E : Type) [Field E] [Fintype E]

def tieK_step : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ),
    SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l) → D.StepTo l →
    (D.stepK SK l).Know (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1))

def tieK_chain : Prop :=
  ∀ (D : TieF E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (n : ℕ),
    D.LtK SK Wp Kc msg n → D.StepTo n → (D.tieK SK n).Know (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1))

/-- The head. -/
def headK_know : Prop :=
  ∀ (p : ℕ) [CharP E p] (H : LkHeadF E) (Mu : H.St → (H.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc H.St Ex (M × Wp))
      (msg : M → H.J → E),
    H.tie.LtK SK Wp Kc msg H.n → H.lkb.Adm p → padsOK H.v H.d H.pads = true →
    (H.headK SK).Know (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg (fun x => ((H.tie.lv (H.n + 1)).base x.2).1)
        (fun x m =>
          ((H.RestF ((H.tie.lv (H.n + 1)).base x.2) m ∧ Mu ((H.tie.lv (H.n + 1)).base x.2).1 m) ∧
            H.tie.Done H.n x.2 m) ∧
          H.tie.claim (H.n + 1) x m) fun x m =>
            (H.RestF ((H.tie.lv (H.n + 1)).base x.2) m ∧ H.tie.Done H.n x.2 m) ∧
            H.tie.claim (H.n + 1) x m)

def ldLkpK_level' : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex) (msg : M → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (l : ℕ),
    SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l) → D.Step →
    (D.levK SK l).Know (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1))

def ldLkpK_tree' : Prop :=
  ∀ (D : TreeP E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex) (msg : M → D.J → E)
      (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (n : ℕ),
    D.LtK SK Wp Kc msg n → D.Step → (D.treeK SK n).Know (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1))

/-- The keys' side. -/
def segKK_know : Prop :=
  ∀ (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Ex : ExtSpec)
      (Kc St M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → I.J → E)
      (pr : I.X → St) (Ψ ΨR : I.X → (I.J → E) → Prop),
    (I.setV (v' + 1)).DK.LtK SK Wp Kc msg v' →
    (segKK I v' tK SK).Know
      (cj R0 msg pr
        (fun x m =>
          Ψ x m ∧ keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x)
        fun x m =>
          ΨR x m ∧ keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x)
      (cj R0 msg (fun x => pr (oldK I v' x))
        (fun x m =>
          (Ψ (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m) fun x m =>
            (ΨR (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
            ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m)

def pscInK_know : Prop :=
  ∀ (Z : PscIn E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex)
      (R0 : Rels Kc Z.St0 Ex (M × Wp)) (msg : M → Z.T.J → E),
    SK.FullK M Wp Kc Z.T.par msg → Z.Link → Z.Back → Z.ev.OK →
    (chainK Z SK).Know (Z.relsIn R0 msg) (Z.T.par.baseOut (Z.ride R0) fun w => msg w.1)

def bitPK_know : Prop :=
  ∀ (B : LkBitP E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex)
      (R0 : Rels Kc B.St Ex (M × Wp)) (msg : M → B.J → E),
    SK.FullK M Wp Kc B.zc.next.par msg →
    (chainK B.zc.toIn SK).Know
      ⟨fun st y w => R0.rel st y w ∧ B.AllBits (msg w.1),
        fun a w => R0.relR a w ∧ B.AllBits (msg w.1), R0.on, R0.core⟩
      (B.zc.next.par.baseOut (B.zc.toIn.ride R0) fun w => msg w.1)

def endMK_know : Prop :=
  ∀ (B : LkEndM E) (Ex : ExtSpec) (M Wp Kc : Type) (SK : PscLtK E Ex)
      (A0 : Rels Kc B.X Ex (M × Wp)) (msg : M → B.J → E),
    SK.CoreK M Wp Kc B.par msg →
    (SK.core B.par).Know (B.relsIn A0 fun w => msg w.1) (B.par.baseMid A0 fun w => msg w.1)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole Finset

section
variable (E : Type) [Field E] [Fintype E]

theorem tieK_step : Spec.tieK_step E := by
  intro D Ex M Wp Kc SK msg A0 l hL hS
  have g1 := SK.our_know M Wp Kc (D.lv l).T (D.msgAt M msg l) hL (D.ride msg A0 l)
  rw [tieF_jt E D Ex M Wp Kc msg A0 l hS] at g1
  refine know_postM (B' := D.jtAt msg A0 (l + 1)) (D.nxt l) g1 (fun _ _ h => h) ?_
  intro o y w _ h
  refine ⟨h.1.1, h.1.2.1, fun a => ?_⟩
  rcases D.cover l a with rfl | ha
  · exact (tieF_next E D l o (msg w.1)).2 h.2
  · exact h.1.2.2 a ha

theorem tieK_chain : Spec.tieK_chain E := by
  intro D Ex M Wp Kc SK msg A0 n hL hS
  exact know_chain (fun l => E × (D.lv l).T.St) (D.stepK SK) (D.jtAt msg A0) n fun l hl =>
    tieK_step E D Ex M Wp Kc SK msg A0 l (hL l hl) fun st m j hj =>
      hS st m j (Nat.lt_of_lt_of_le hj hl)

theorem headK_know : Spec.headK_know E := by
  intro p _ H Mu Ex Kc M Wp SK R0 msg hL hA hP
  have g1 : (drawK E (Prod.mk : H.St → E → H.St × E) Ex (2 ^ H.v - 1)).Know
      (cj R0 msg id (H.lkb.inP Mu) H.lkb.inR)
      (cj R0 msg Prod.fst (fun x m => H.midF x m ∧ Mu x.1 m) H.midF) := by
    refine Kn.knowAt_draw Kc M H.St (H.St × E) Ex Wp E Prod.mk _ _ (2 ^ H.v - 1)
      (fun _ _ _ h => h) ?_
    intro st y m _
    refine (cnt_mono fun β hβ => ?_).trans (headF_cnt E p H st (msg m) hA hP)
    obtain ⟨wp, h1, h2⟩ := hβ
    exact ⟨h1.2, fun h => h2 ⟨h1.1, h⟩⟩
  have hstep : H.tie.StepTo H.n := fun st m j hj =>
    (ldLkpTie_hU E (H.n + 2) (H.PT st m) (by omega)).1 (j + 1) (by omega)
  have g2 := tieK_chain E H.tie Ex M Wp Kc SK msg
    (cj R0 msg Prod.fst (fun x m => H.RestF x m ∧ Mu x.1 m) H.RestF) H.n hL hstep
  rw [tieFR_cj E H.tie Ex Kc H.St M Wp R0 msg Prod.fst
      (fun x m => H.RestF x m ∧ Mu x.1 m) H.RestF H.n] at g2
  have hq : ∀ (x : H.St × E) (m : H.J → E),
      H.tie.Q x m 1 ^ 2 * H.PT x m 0 =
        ∏ j ∈ range (H.n + 2), tabProd H.d (H.tab x.1) (H.bit m) x.2 j ^ 2 ^ j :=
    fun x m =>
      ((ldLkpTie_hU E (H.n + 2) (H.PT x m) (by omega)).1 0 (by omega)).symm.trans
        (ldLkpTie_hU E (H.n + 2) (H.PT x m) (by omega)).2.2
  refine know_seq g1 (know_preM (fun x : H.St × E => ((0 : E), x)) (fun _ _ h => h) ?_ g2)
  intro x y w _ h
  obtain ⟨⟨hR, hb, hn⟩, hc⟩ := h
  have hc' : keyProd H.v (H.key x.1 (msg w.1)) x.2 -
      H.fac x * (H.tie.Q x (msg w.1) 1 ^ 2 * H.PT x (msg w.1) 0) = 0 := hc
  rw [hq] at hc'
  exact ⟨hR, hb, hn, sub_eq_zero.mp hc'⟩

theorem ldLkpK_level' : Spec.ldLkpK_level' E := by
  intro D Ex M Wp Kc SK msg A0 l hL hS
  have g1 := SK.our_know M Wp Kc (D.lv l).T (D.msgAt M msg l) hL (D.ride msg A0 l)
  have g2 := ldLineC_goodAt E (D.cube l) Ex M Wp Kc (D.afterU msg l (D.ride msg A0 l))
    msg (ldLkpP_halves E D hS l)
  have hiff : ∀ (o : (D.lv l).T.par.Out) (mm : (D.lv l).T.J → E) (P : Prop),
      (P ∧ (D.lv l).T.par.OutHolds o mm) ↔
      ((P ∧ (D.lv l).T.par.UHolds o mm) ∧
        ∀ b, (D.lv l).T.par.EHolds o mm ((D.lv l).two b)) := fun o mm P =>
    ⟨fun h => ⟨⟨h.1, h.2.1⟩, fun b => h.2.2 _⟩, fun h => ⟨h.1.1, h.1.2, fun a => by
      obtain ⟨b, rfl⟩ := D.two_surj l a
      exact h.2 b⟩⟩
  refine know_seq ?_ ((goodAt_iff _ _ _ _ _ _).1 g2).1
  have e : (D.lv l).T.par.baseOut (D.ride msg A0 l) (fun w : M × Wp => D.msgAt M msg l w.1) =
      ⟨fun o y w =>
          (D.afterU msg l (D.ride msg A0 l)).rel o y w ∧
          ∀ b, (D.cube l).P.par.EHolds o ((D.cube l).toLine.em (msg w.1)) ((D.cube l).a b),
        fun a w =>
          (D.afterU msg l (D.ride msg A0 l)).relR a w ∧
          ∀ b, (D.cube l).P.par.EHolds a.1 ((D.cube l).toLine.em (msg w.1)) ((D.cube l).a b),
        (D.afterU msg l (D.ride msg A0 l)).on,
        (D.afterU msg l (D.ride msg A0 l)).core⟩ :=
    rels_ext (funext fun o => funext fun y => funext fun w => propext (hiff o _ _))
      (funext fun a => funext fun w => propext (hiff a.1 _ _)) rfl rfl
  rw [e] at g1
  exact g1

theorem ldLkpK_tree' : Spec.ldLkpK_tree' E := by
  intro D Ex M Wp Kc SK msg A0 n hL hS
  exact know_chain (fun l => E × (D.lv l).T.St) (D.levK SK) (D.jtAt msg A0) n
    fun l hl => ldLkpK_level' E D Ex M Wp Kc SK msg A0 l (hL l hl) hS

theorem segKK_know : Spec.segKK_know E := by
  intro I v' tK Ex Kc St M Wp SK R0 msg pr Ψ ΨR hL
  have g := ldLkpK_tree' E (I.setV (v' + 1)).DK Ex M Wp Kc SK msg
    (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m)
    v' hL (ldLkpInst_stepK E (I.setV (v' + 1)))
  have htop : ∀ (x : E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) (m : I.J → E),
      ((I.setV (v' + 1)).DK.lv (v' + 1)).T.SumHolds
        x (fun j => m (((I.setV (v' + 1)).DK.lv (v' + 1)).toJ j)) ↔
      ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m := fun x m => by
    have h := ldLkpInst_topK E (I.setV (v' + 1)) x m
    have hb : ((I.setV (v' + 1)).DK.lv (v' + 1)).base x.2 = oldK I v' x :=
      ldLkpSegK_base E (I.setV (v' + 1)).DK (v' + 1) x.2
    have h' : ((I.setV (v' + 1)).DK.lv (v' + 1)).T.SumHolds
          x (fun j => m (((I.setV (v' + 1)).DK.lv (v' + 1)).toJ j)) ↔
        ((I.setV (v' + 1)).topCl x).Holds
          (v' + 1) (I.key (I.st (((I.setV (v' + 1)).DK.lv (v' + 1)).base x.2)) m) m := h
    rw [hb] at h'
    exact h'
  have e0 := ldLkpK_tree E (I.setV (v' + 1)).DK Ex Kc St M Wp R0 msg (fun s => pr s.1)
    (fun s m => Ψ s.1 m) (fun s m => ΨR s.1 m) 0
  have e1 : (I.setV (v' + 1)).DK.jtAt
        msg (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m) (v' + 1) =
      cj R0 msg (fun x => pr (oldK I v' x))
        (fun x m =>
          (Ψ (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m)
        (fun x m =>
          (ΨR (oldK I v' x) m ∧ RowsHold (rowsK I v' x) m) ∧
          ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m) :=
    (ldLkpK_tree E (I.setV (v' + 1)).DK Ex Kc St M Wp R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m)
        (fun s m => ΨR s.1 m) (v' + 1)).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x m => and_congr_right fun _ => htop x m)
        (fun x m => and_congr_right fun _ => htop x m))
  rw [e0, e1] at g
  have hsum : ∀ (x : I.X) (m : I.J → E),
      ((I.setV (v' + 1)).DK.lv 0).T.SumHolds
        (enterK (I.setV (v' + 1)) tK x) (fun j => m (((I.setV (v' + 1)).DK.lv 0).toJ j)) ↔
      keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) + ∑ j, I.fK x j * m j = tK x := fun x m => by
    rw [ldLkpP_sum E (I.setV (v' + 1)).DK (ldLkpInst_stepK E (I.setV (v' + 1))) 0
        (enterK (I.setV (v' + 1)) tK x) m]
    have hu : (I.setV (v' + 1)).DK.U
          (((I.setV (v' + 1)).DK.lv 0).base (enterK (I.setV (v' + 1)) tK x).2) m 0 =
        fun _ => keyProd (v' + 1) (I.key (I.st x) m) (I.lam x) :=
      funext fun θ => ldLkpInst_rootK E (I.setV (v' + 1)) x m θ
    rw [hu, Alg.mle_const]
    exact Iff.rfl
  refine know_preM (enterK (I.setV (v' + 1)) tK) (fun _ _ h => h) ?_ g
  exact fun x y w _ h => ⟨h.1, h.2.1.1, (hsum x _).mp h.2.2⟩

theorem pscInK_know : Spec.pscInK_know E := fun Z Ex M Wp Kc SK R0 msg hL hLk hB hOK =>
  know_seq (B := Z.relsOut R0 msg) ((goodAt_iff _ _ _ _ _ _).1 (pscIn_goodAt E Z Ex M Wp Kc R0 msg
      hLk hB hOK)).1
    (SK.our_know M Wp Kc Z.T msg hL (Z.ride R0))

theorem bitPK_know : Spec.bitPK_know E := by
  intro B Ex M Wp Kc SK R0 msg hL
  have e : B.zc.toIn.AllHold = B.zc.ZeroHolds :=
    funext fun st => funext fun m => propext (ldZeroP_all E B.zc st m)
  have h := pscInK_know E B.zc.toIn Ex M Wp Kc SK R0 msg hL (ldZeroP_link E B.zc)
    (ldZeroP_back E B.zc) (ldZeroP_ok E B.zc (ldZero_ok_one E))
  unfold PscIn.relsIn at h
  rw [e, B.zero_eq E] at h
  exact h

theorem endMK_know : Spec.endMK_know E := by
  intro B Ex M Wp Kc SK A0 msg hL
  rw [endM_joint E]
  exact hL A0

end
end Cb
