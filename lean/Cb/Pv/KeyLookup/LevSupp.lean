-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevSupp.lean: if every place of the key levels and of the table's levels lies in a
set G of entries, the two blocks keep «every form in the flat state is 0 outside G» (`Dat.SuppX`).

  `treeS_slS`, `treeS_rowU`, `treeS_rowsAt`  of a tree with orders: the incoming form of a level and
                the levels' rows are 0 outside G, if the places wAt, cAt lie in G and the form with
                which level 0 was entered, read at the state's own root, is 0 outside G.
  `KeyPart.side_supp`, `sides_supp`  a key side; m key sides: rows and claims' mask forms.
  `LevPl.In G`  all four families of places lie in G.
  `Dat.keys_supp`, `Dat.table_supp`  `Inv` of the two blocks' reductions from `SuppX G` to `SuppX
                G`;
                `_lib`: at the library's sumcheck.
Conditions: `L.In G`; on the letter `SidesForm`, `FormS` (the sumcheck hands its state on: so the
state of entry is known to be the caller's).
`treeS_*`: after Cb.Ld.LdLkpSuppProofs (tree_wAt, tree_cAt, tree_slS, tree_rowU, tree_rowsAt), with
the condition on the first form asked at the root of the state and not at all states.

-/
import Cb.Pv.KeyLookup.LevForm
import Cb.Pv.KeyLookup.AsmSupp
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

section Tree
variable (D : TreeP E) (G : D.J → Prop)

theorem treeS_wAt (hw : ∀ l i, G (D.wAt l i)) : ∀ l i, G ((D.lv l).toJ ((D.lv l).T.wAt i))
  | 0, i => hw 0 i
  | l + 1, i => hw (l + 1) i

theorem treeS_cAt (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l b, G ((D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b)))
  | 0, b => hc 0 b
  | l + 1, b => hc (l + 1) b

theorem treeS_slS (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l s, SuppIn G (D.inc0 (D.root l s).1 (D.root l s).2) →
      SuppIn (fun j => G ((D.lv l).toJ j)) ((D.lv l).T.slS s)
  | 0, _, h0 => h0
  | l + 1, s, _ => fun j hj => by
      classical
      show (D.lv l).T.lst s.1.st ((D.lv l).T.par.hp s.1.st s.1.pt) *
          ((if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) then 1 - s.2 else 0) +
            if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) then s.2 else 0) = 0
      have h1 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) := fun e =>
        hj (e ▸ treeS_cAt D G hc l false)
      have h2 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) := fun e =>
        hj (e ▸ treeS_cAt D G hc l true)
      rw [if_neg h1, if_neg h2]
      simp

theorem treeS_rowU (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b)) (l : ℕ)
    (o : (D.lv l).T.par.Out) (h0 : SuppIn G (D.inc0 (D.root l o.st).1 (D.root l o.st).2)) :
    SuppIn G (D.rowU l o).cf :=
  supp_pushJ _ _ G
    (supp_slU (D.lv l).T.par (D.emB l) _ o _ (treeS_wAt D G hw l) (treeS_slS D G hc l o.st h0))

theorem treeS_rowsAt (hw : ∀ l i, G (D.wAt l i)) (hc : ∀ l b, G (D.cAt l b)) :
    ∀ l s, SuppIn G (D.inc0 (D.root l s).1 (D.root l s).2) → RowsSupp G (D.rowsAt l s)
  | 0, _, _ => fun _ hr => absurd hr List.not_mem_nil
  | l + 1, s, h0 => fun r hr => by
      rcases List.mem_cons.1 hr with e | h
      · rw [e]; exact treeS_rowU D G hw hc l s.1 h0
      · exact treeS_rowsAt hw hc l s.1.st h0 r h

end Tree

theorem ProdT.seg_supp (T : ProdT E) (G : T.J → Prop) (hw : ∀ l i, G (T.wAt l i)) (hc : ∀ l b, G
    (T.cAt l b))
    (x : T.TopSt) (h0 : SuppIn G (T.f0 (T.old x))) : RowsSupp G (T.rows x) ∧ SuppIn G (T.form x) :=
  ⟨fun r hr => treeS_rowsAt T.tree G hw hc (T.n' + 1) x.2 h0 r (List.mem_reverse.1 hr),
    supp_pushJ _ _ G (treeS_slS T.tree G hc (T.n' + 1) x.2 h0)⟩

variable {B : KeyBase E}

/-- the part's places lie in G, and the form of the claim on its root, read at x0, is 0 outside G -/
def KeyPart.InG (p : KeyPart B) (G : B.J → Prop) (x0 : B.X0) : Prop :=
  (∀ l i, G (p.wK l i)) ∧ (∀ l b, G (p.cK l b)) ∧ SuppIn G (p.fK x0)

theorem KeyPart.side_supp (p : KeyPart B) (X : Type) (pr : X → B.X0) (G : B.J → Prop) (x : p.SideSt
    X pr)
    (h : p.InG G (p.prN X pr x)) : RowsSupp G (p.rows X pr x) ∧ SuppIn G (p.cl X pr x).mf :=
  ⟨fun r hr => treeS_rowsAt (p.tree X pr) G h.1 h.2.1 (p.v' + 1) x.2 h.2.2 r (List.mem_reverse.1
      hr),
    fun j hj => by
    have h1 := supp_pushJ _ _ G (treeS_slS (p.tree X pr) G h.2.1 (p.v' + 1) x.2 h.2.2) j hj
    exact neg_eq_zero.2 h1⟩

theorem sides_supp (G : B.J → Prop) : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X →
    B.X0)
    (x : SidesSt p ps X pr), (∀ r ∈ p :: ps, r.InG G (pr (sidesOld p ps X pr x))) →
    RowsSupp G (sidesRows p ps X pr x) ∧ ∀ c ∈ sidesCl p ps X pr x, SuppIn G c.mf
  | [], p, X, pr, x, h => by
    have h1 := p.side_supp X pr G x (h p (List.mem_singleton.2 rfl))
    exact ⟨h1.1, fun c hc => by rw [List.mem_singleton.1 hc]; exact h1.2⟩
  | r :: ps, p, X, pr, x, h => by
    have h1 := p.side_supp X pr G (sidesOld r ps (p.SideSt X pr) (p.prN X pr) x)
      (h p (List.mem_cons_self ..))
    have h2 := sides_supp G ps r (p.SideSt X pr) (p.prN X pr) x
      fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨fun w hw => ?_, fun c hc => ?_⟩
    · rcases List.mem_append.1 hw with hw | hw
      · exact h1.1 w hw
      · exact h2.1 w hw
    · rcases List.mem_cons.1 hc with e | hc
      · rw [e]; exact h1.2
      · exact h2.2 c hc

/-- All places of the two stretches lie in G. -/
structure LevPl.In {A : Dat E} (L : LevPl A) (G : A.J → Prop) : Prop where
  wK : ∀ i l k, G (L.wK i l k)
  cK : ∀ i l b, G (L.cK i l b)
  wT : ∀ l k, G (L.wT l k)
  cT : ∀ l b, G (L.cT l b)

namespace Dat
variable (A : Dat E) (L : LevPl A) (SK : PscLtK E Ex) (G : A.J → Prop)

theorem mem_parts (r : KeyPart A.kb) (hr : r ∈ A.part L 0 :: A.tailP L) : ∃ i, r = A.part L i := by
  rcases List.mem_cons.1 hr with e | h
  · exact ⟨0, e⟩
  · obtain ⟨i, _, e⟩ := List.mem_map.1 h
    exact ⟨i + 1, e.symm⟩

theorem backK_supp (hL : L.In G) (z : A.KSt L) (h : A.SuppX G (A.oldK L z)) : A.SuppX G (A.backK L
    z) := by
  have hs := sides_supp (B := A.kb) G (A.tailP L) (A.part L 0) A.XS id z fun r hr => by
    obtain ⟨i, rfl⟩ := A.mem_parts L r hr
    exact ⟨hL.wK i, hL.cK i, h.roots i⟩
  refine ⟨h.all, h.run, h.roots, h.planes, h.top, fun i => ?_, fun r hr => ?_⟩
  · show SuppIn G ((sidesCl (A.part L 0) (A.tailP L) A.XS id z).getD i ⟨0, 0, 0⟩).mf
    by_cases hi : i < (sidesCl (A.part L 0) (A.tailP L) A.XS id z).length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hs.2 _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact fun _ _ => rfl
  · rcases List.mem_append.1 hr with hr | hr
    · exact h.rows r hr
    · exact hs.1 r hr

theorem keys_supp (hL : L.In G) (hF : SidesForm (B := A.kb) SK (A.part L 0) (A.tailP L) A.XS id) :
    Inv (A.keysK L SK).R (A.SuppX G) (A.SuppX G) := by
  have hp := sides_passes (B := A.kb) SK (A.tailP L) (A.part L 0) A.XS id hF
  have h1 : Inv (sidesK (B := A.kb) SK (A.part L 0) (A.tailP L) A.XS id).R (A.SuppX G)
      (fun z => A.SuppX G (A.oldK L z)) := fun x y τ z hz hP => by
    have e : A.oldK L z = x := hp x y τ z hz
    show A.SuppX G (A.oldK L z)
    rw [e]
    exact hP
  refine h1.post _ _ fun z x' e hz => ?_
  obtain rfl := Option.some.inj e
  exact A.backK_supp L G hL z hz

theorem backT_supp (hL : L.In G) (z : (A.tabT L).TopSt) (h : A.SuppX G ((A.tabT L).old z)) :
    A.SuppX G (A.backT L z) := by
  have hs := (A.tabT L).seg_supp G hL.wT hL.cT z h.top
  refine ⟨h.all, h.run, h.roots, h.planes, hs.2, h.cls, fun r hr => ?_⟩
  rcases List.mem_append.1 hr with hr | hr
  · exact h.rows r hr
  · exact hs.1 r hr

theorem table_supp (hL : L.In G) (hF : FormS (A.tabT L).tree SK (A.tabT L).n') :
    Inv (A.tableK L SK).R (A.SuppX G) (A.SuppX G) := by
  have hp := (A.tabT L).seg_passes SK hF
  have h1 : Inv ((A.tabT L).segK SK).R (A.SuppX G) (fun z => A.SuppX G ((A.tabT L).old z)) :=
    fun x y τ z hz hP => by
      have e : (A.tabT L).old z = x := hp x y τ z hz
      show A.SuppX G ((A.tabT L).old z)
      rw [e]
      exact hP
  refine h1.post _ _ fun z x' e hz => ?_
  obtain rfl := Option.some.inj e
  exact A.backT_supp L G hL z hz

theorem keys_supp_lib (hL : L.In G) : Inv (A.keysK L (PscLtK.lib E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.keys_supp L _ G hL (sidesForm_lib (B := A.kb) (A.tailP L) (A.part L 0) A.XS id)

theorem table_supp_lib (hL : L.In G) : Inv (A.tableK L (PscLtK.lib E Ex)).R (A.SuppX G) (A.SuppX
    G) :=
  A.table_supp L _ G hL (form_lib (A.tabT L).tree (A.tabT L).n')

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_supp_lib
#print axioms Lk6.Dat.table_supp_lib
