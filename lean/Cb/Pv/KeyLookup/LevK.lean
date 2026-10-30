-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevK.lean: the levels of a product tree with orders, the tree over leaves by number
and the m key sides, as blocks without an honest side, with the sumcheck as a letter.

 No honest side is named in this file but inside one proof, that of `lev_know`, which takes Know out
 of a theorem of the library's that names one (the line step).

  `lineK`, `levK`, `treeK`  a line step; a level; the levels 0 .. n of a tree with orders.
  `LtS D SK Wp Kc msg n`  what is asked of the letter: `SK.FullK` at the sumchecks of the levels l ≤
                n.
  `lt_lib`      the library's own verifier meets it.
  `lev_know`, `tree_know`  under `LtS` and `D.Step`: Know from the tree's joint at l to that at l +
                1;
                from 0 to n + 1.
  `ProdT.segK`, `segK_know`  the tree over leaves by number: Know between `seg_good`'s two joints.
  `segKKS`, `segKKS_know`   a key side at an instance with orders.
  `sidesK`, `SidesLt`, `sidesK_know`, `sidesLt_lib`  m key sides in a row, by recursion: Know
                between
                `sides_good`'s two joints.
Conditions: `LtS`, `SidesLt`: on the sumcheck's letter alone.
Not claimed: anything on the exact side of a joint (Know does not read it), on completeness, on an
honest run.
The blocks without an honest side and their rules: after KnowAt. The letter, and the proofs of
`lev_know`, `tree_know`, `segKKS_know`: after Cb/Pv/Lookup/Know/LtK.lean. The library's own trees
have orders too (the field `sg` of `TreeP`, Cb/Ld/LdLkpTreeP.lean), and that file has `lineK`,
`levK`, `treeK`, `LtK`, `segKK` over them.
Not claimed: anything on completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevSides
import Cb.Pv.KeyLookup.LevTree
import Cb.Pv.Lookup.Know.LtK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob

noncomputable section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- `Know` between joints of the form cj does not see how their clauses are bracketed. -/
theorem know_congr {Kc M X₁ X₂ St' Wp J : Type} (b : BkK X₁ X₂ Ex)
    (R0 : Rels Kc St' Ex (M × Wp)) (msg : M → J → E) (q₁ : X₁ → St') (q₂ : X₂ → St')
    (Φ ΦR Φ' ΦR' : X₁ → (J → E) → Prop) (Θ ΘR Θ' ΘR' : X₂ → (J → E) → Prop)
    (h₁ : ∀ x m, Φ x m ↔ Φ' x m) (h₂ : ∀ x m, ΦR x m ↔ ΦR' x m)
    (h₃ : ∀ x m, Θ x m ↔ Θ' x m) (h₄ : ∀ x m, ΘR x m ↔ ΘR' x m)
    (g : b.Know (cj R0 msg q₁ Φ ΦR) (cj R0 msg q₂ Θ ΘR)) :
    b.Know (cj R0 msg q₁ Φ' ΦR') (cj R0 msg q₂ Θ' ΘR') := by
  rw [← ldLkpK_congr E Kc St' M Wp J X₁ Ex R0 msg q₁ Φ ΦR Φ' ΦR' h₁ h₂,
    ← ldLkpK_congr E Kc St' M Wp J X₂ Ex R0 msg q₂ Θ ΘR Θ' ΘR' h₃ h₄]
  exact g

/-! ### the levels -/
section Tree
variable (D : TreeP E) (SK : PscLtK E Ex)

variable (Ex) in
def lineK (l : ℕ) : BkK (D.lv l).T.par.Out (E × (D.lv (l + 1)).T.St) Ex :=
  drawK (D.cube l).toLine.toIn.ev.D (D.cube l).toLine.toIn.nxX Ex (D.cube l).toLine.toIn.ev.err

def levK (l : ℕ) : BkK (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex :=
  (SK.full (D.lv l).T.par).seq (lineK Ex D l)

def treeK (n : ℕ) : BkK (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex :=
  BkK.chain (fun l => E × (D.lv l).T.St) (levK D SK) n

/-- what is asked of the letter -/
def LtS {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) : Prop :=
  ∀ l ≤ n, SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l)

theorem lt_lib {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) :
    LtS D (PscLtK.lib E Ex) Wp Kc msg n := fun l _ =>
  PscLtK.lib_ourK M Wp Kc (D.lv l).T (D.msgAt M msg l) (ldLkpP_ok E D l).1 (ldLkpP_ok E D l).2.2.1
    (ldLkpP_ok E D l).2.2.2 (ldLkpP_ok E D l).2.1

theorem lev_know (M Wp Kc : Type) (msg : M → D.J → E) (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (l :
    ℕ)
    (hL : SK.FullK M Wp Kc (D.lv l).T.par (D.msgAt M msg l)) (hS : D.Step) :
    (levK D SK l).Know (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1)) := by
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
  refine know_seq ?_ ((TWhole.goodAt_iff _ _ _ _ _ _).1 g2).1
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

theorem tree_know (M Wp Kc : Type) (msg : M → D.J → E) (A0 : Rels Kc (D.lv 0).T.St Ex (M × Wp)) (n :
    ℕ)
    (hL : LtS D SK Wp Kc msg n) (hS : D.Step) :
    (treeK D SK n).Know (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1)) :=
  know_chain (fun l => E × (D.lv l).T.St) (levK D SK) (D.jtAt msg A0) n
    fun l hl => lev_know D SK M Wp Kc msg A0 l (hL l hl) hS

end Tree

/-! ### the segment over leaves by number -/
namespace ProdT
variable (T : ProdT E) (SK : PscLtK E Ex)

def segK : BkK T.X T.TopSt Ex := (treeK T.tree SK T.n').preM T.enter

theorem segK_know (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → T.J → E)
    (pr : T.X → St) (Ψ ΨR : T.X → (T.J → E) → Prop) (hL : LtS T.tree SK Wp Kc msg T.n') :
    (T.segK SK).Know
      (cj R0 msg pr (fun x m => Ψ x m ∧ T.InHolds x m) fun x m => ΨR x m ∧ T.InHolds x m)
      (cj R0 msg (fun x => pr (T.old x))
        (fun x m => (Ψ (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m)
        fun x m => (ΨR (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m) := by
  have g := tree_know T.tree SK M Wp Kc msg
    (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m) T.n' hL T.step
  have e0 := ldLkpK_tree E T.tree Ex Kc St M Wp R0 msg (fun s => pr s.1)
    (fun s m => Ψ s.1 m) (fun s m => ΨR s.1 m) 0
  have e1 : T.tree.jtAt msg (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m)
        (T.n' + 1) =
      cj R0 msg (fun x => pr (T.old x))
        (fun x m => (Ψ (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m)
        (fun x m => (ΨR (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m) :=
    (ldLkpK_tree E T.tree Ex Kc St M Wp R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m)
        (fun s m => ΨR s.1 m) (T.n' + 1)).trans
      (ldLkpK_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (fun x m => and_congr (and_congr_right fun _ => (rowsHold_rev _ _).symm) (T.top_iff x m))
        (fun x m => and_congr (and_congr_right fun _ => (rowsHold_rev _ _).symm) (T.top_iff x m)))
  rw [e0, e1] at g
  refine know_preM T.enter (fun _ _ h => h) ?_ g
  intro x y w _ h
  exact ⟨h.1, h.2.1.1, (T.in_iff x _).mp h.2.2⟩

end ProdT

/-! ### a key side -/

def segKKS (I : LkInst E) (v' : ℕ) (tK : I.X → E) (SK : PscLtK E Ex) :
    BkK I.X (E × ((I.setV (v' + 1)).DK.lv (v' + 1)).T.St) Ex :=
  (treeK (I.setV (v' + 1)).DK SK v').preM (enterK (I.setV (v' + 1)) tK)

theorem segKKS_know (I : LkInst E) (v' : ℕ) (tK : I.X → E) (Kc St M Wp : Type) (SK : PscLtK E Ex)
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → I.J → E) (pr : I.X → St) (Ψ ΨR : I.X → (I.J → E) →
        Prop)
    (hL : LtS (I.setV (v' + 1)).DK SK Wp Kc msg v') :
    (segKKS I v' tK SK).Know
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
            ((I.setV (v' + 1)).topCl x).Holds (v' + 1) (I.key (I.st (oldK I v' x)) m) m) := by
  have g := tree_know (I.setV (v' + 1)).DK SK M Wp Kc msg
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
  intro x y w _ h
  exact ⟨h.1, h.2.1.1, (hsum x _).mp h.2.2⟩

/-! ### m key sides -/
variable {B : KeyBase E}

namespace KeyPart
variable (p : KeyPart B) (X : Type) (pr : X → B.X0) (SK : PscLtK E Ex)

def sideK : BkK X (p.SideSt X pr) Ex := segKKS (p.inst X pr) p.v' (fun x => p.tK (pr x)) SK

theorem sideK_know (Kc St' M Wp : Type) (R0 : Rels Kc St' Ex (M × Wp)) (msg : M → B.J → E)
    (q : X → St') (Ψ ΨR : X → (B.J → E) → Prop) (hL : LtS (p.tree X pr) SK Wp Kc msg p.v') :
    (p.sideK X pr SK).Know
      (cj R0 msg q (fun x m => Ψ x m ∧ p.RootHolds (pr x) m) fun x m => ΨR x m ∧ p.RootHolds (pr x)
          m)
      (cj R0 msg (fun x => q (p.old X pr x)) (fun x m => Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m)
        fun x m => ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) :=
  know_congr (p.sideK X pr SK) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    (fun _ _ => ⟨fun h => ⟨h.1.1, (rowsHold_rev _ _).2 h.1.2, h.2⟩,
      fun h => ⟨⟨h.1, (rowsHold_rev _ _).1 h.2.1⟩, h.2.2⟩⟩)
    (fun _ _ => ⟨fun h => ⟨h.1.1, (rowsHold_rev _ _).2 h.1.2, h.2⟩,
      fun h => ⟨⟨h.1, (rowsHold_rev _ _).1 h.2.1⟩, h.2.2⟩⟩)
    (segKKS_know (p.inst X pr) p.v' (fun x => p.tK (pr x)) Kc St' M Wp SK R0 msg q Ψ ΨR hL)

end KeyPart

/-- The key sides of the parts p :: ps, one after the other: the verifier's side and its errors. -/
def sidesK (SK : PscLtK E Ex) : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X →
    B.X0) →
    BkK X (SidesSt p ps X pr) Ex
  | p, [], X, pr => p.sideK X pr SK
  | p, r :: ps, X, pr => (p.sideK X pr SK).seq (sidesK SK r ps (p.SideSt X pr) (p.prN X pr))

/-- what is asked of the letter: at every level of every part's tree -/
def SidesLt (SK : PscLtK E Ex) {M : Type} (Wp Kc : Type) (msg : M → B.J → E) :
    (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) → Prop
  | p, [], X, pr => LtS (p.tree X pr) SK Wp Kc msg p.v'
  | p, r :: ps, X, pr =>
    LtS (p.tree X pr) SK Wp Kc msg p.v' ∧ SidesLt SK Wp Kc msg r ps (p.SideSt X pr) (p.prN X pr)

theorem sidesLt_lib {M : Type} (Wp Kc : Type) (msg : M → B.J → E) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
      SidesLt (PscLtK.lib E Ex) Wp Kc msg p ps X pr
  | [], p, X, pr => lt_lib (p.tree X pr) Wp Kc msg p.v'
  | r :: ps, p, X, pr =>
    ⟨lt_lib (p.tree X pr) Wp Kc msg p.v', sidesLt_lib Wp Kc msg ps r (p.SideSt X pr) (p.prN X pr)⟩

/-- m key sides in a row: Know. -/
theorem sidesK_know (SK : PscLtK E Ex) (Kc St' M Wp : Type) (R0 : Rels Kc St' Ex (M × Wp))
    (msg : M → B.J → E) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0) (q : X → St')
      (Ψ ΨR : X → (B.J → E) → Prop), SidesLt SK Wp Kc msg p ps X pr →
      (sidesK SK p ps X pr).Know
        (cj R0 msg q (fun x m => Ψ x m ∧ rootsHold (p :: ps) (pr x) m)
          fun x m => ΨR x m ∧ rootsHold (p :: ps) (pr x) m)
        (cj R0 msg (fun x => q (sidesOld p ps X pr x))
          (fun x m => Ψ (sidesOld p ps X pr x) m ∧ sidesOut p ps X pr x m)
          fun x m => ΨR (sidesOld p ps X pr x) m ∧ sidesOut p ps X pr x m)
  | [], p, X, pr, q, Ψ, ΨR, hL =>
    know_congr (p.sideK X pr SK) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
      (fun _ _ => ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩)
      (fun _ _ => ⟨fun h => ⟨h.1, h.2, trivial⟩, fun h => ⟨h.1, h.2.1⟩⟩)
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (p.sideK_know X pr SK Kc St' M Wp R0 msg q Ψ ΨR hL)
  | r :: ps, p, X, pr, q, Ψ, ΨR, hL => by
    have g1 : (p.sideK X pr SK).Know
        (cj R0 msg q (fun x m => Ψ x m ∧ rootsHold (p :: r :: ps) (pr x) m)
          fun x m => ΨR x m ∧ rootsHold (p :: r :: ps) (pr x) m)
        (cj R0 msg (fun x => q (p.old X pr x))
          (fun x m => (Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
          fun x m => (ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m) :=
      know_congr (p.sideK X pr SK) R0 msg q (fun x => q (p.old X pr x)) _ _ _ _ _ _ _ _
        (fun _ _ => ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩)
        (fun _ _ => ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩)
        (fun _ _ => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)
        (fun _ _ => ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩)
        (p.sideK_know X pr SK Kc St' M Wp R0 msg q (fun x m => Ψ x m ∧ rootsHold (r :: ps) (pr x) m)
          (fun x m => ΨR x m ∧ rootsHold (r :: ps) (pr x) m) hL.1)
    have g2 : (sidesK SK r ps (p.SideSt X pr) (p.prN X pr)).Know
        (cj R0 msg (fun x => q (p.old X pr x))
          (fun x m => (Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
          fun x m => (ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) ∧ rootsHold (r :: ps) (p.prN X pr
              x) m)
        (cj R0 msg (fun x => q (sidesOld p (r :: ps) X pr x))
          (fun x m => Ψ (sidesOld p (r :: ps) X pr x) m ∧ sidesOut p (r :: ps) X pr x m)
          fun x m => ΨR (sidesOld p (r :: ps) X pr x) m ∧ sidesOut p (r :: ps) X pr x m) :=
      know_congr (sidesK SK r ps (p.SideSt X pr) (p.prN X pr)) R0 msg
        (fun x => q (p.old X pr x)) (fun x => q (sidesOld p (r :: ps) X pr x)) _ _ _ _ _ _ _ _
        (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => and_assoc) (fun _ _ => and_assoc)
        (sidesK_know SK Kc St' M Wp R0 msg ps r (p.SideSt X pr) (p.prN X pr) (fun x => q (p.old X pr
            x))
          (fun x m => Ψ (p.old X pr x) m ∧ p.OutHolds X pr x m)
          (fun x m => ΨR (p.old X pr x) m ∧ p.OutHolds X pr x m) hL.2)
    exact know_seq g1 g2

end
end Lk6

#print axioms Lk6.tree_know
#print axioms Lk6.ProdT.segK_know
#print axioms Lk6.segKKS_know
#print axioms Lk6.sidesK_know
#print axioms Lk6.sidesLt_lib
