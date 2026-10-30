-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevTree.lean: a product tree over leaves given by their numbers, entered at a point,
with an order a level.

segA carries the
  library's honest side as data; seg_good states of it the library's GoodAt WHOLE (acc, keeps,
  prBad, cover, prCov, same beside know); no masked clause is stated.

  `ProdT`       states X; names J of the entries; g variables at level 0; n' + 1 levels; `leaf x m
                c`:
                leaf number c (bit t of c is variable t; the g variables of level 0 are the low
                ones); the point pt0 and the masked claim (form f0, target t0) with which level 0 is
                entered; the places of the levels' own mask entries; `sg l`: round j of level l
                binds
                variable sg l j.
  `ProdT.tree`, `step`  the tree with orders at these letters; each entry is the product of the two
                above it.
  `ProdT.segA`  the levels 0, .., n' in a row, entered by a step without rounds.
  `seg_good`    for every riding R0, Ψ, ΨR: from «Ψ, and the extension of level 0's table at pt0,
                masked, is t0» to «Ψ at the state of entry, the levels' rows hold, and the extension
                of
                the leaves' table at the point reached, masked, is the target reached»: `BkA.Good`.
  `seg_know`    its clause on knowledge soundness alone. `seg_rounds`: the sum over l ≤ n' of
                g + l + 4.
Conditions: none. There is at least one level: a tree of no level is no block here.
Not claimed: what the leaves are; how level 0 got its point and claim.
The frame of `seg_good`'s proof: after E3SegK.

-/
import Cb.Pv.KeyLookup.LevSides
import Cb.Pv.KeyLookup.LevOrd
import Cb.Ld.LdLkpFormat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Iop IOR Hiop Prob

noncomputable section

/-- A product tree over leaves given by their numbers. -/
structure ProdT (E : Type) [Field E] [Fintype E] where
  X : Type
  J : Type
  [finJ : Fintype J]
  /-- level 0 has g variables; there are n' + 1 levels -/
  g : ℕ
  n' : ℕ
  leaf : X → (J → E) → ℕ → E
  /-- the point, and the masked claim, with which level 0 is entered -/
  pt0 : X → Fin (g + 0) → E
  f0 : X → J → E
  t0 : X → E
  wAt : (l : ℕ) → PIdx (List.replicate (g + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cAt : ℕ → Bool → J
  /-- round j of level l binds variable sg l j -/
  sg : (l : ℕ) → Equiv.Perm (Fin (g + l))

attribute [instance] ProdT.finJ

namespace ProdT
variable {E : Type} [Field E] [Fintype E] (T : ProdT E)

def tree : TreeP E where
  St0 := T.X
  J := T.J
  g := T.g
  U := fun x m l => cubeLvl T.g (T.n' + 1) (T.leaf x m) l
  inc0 := fun x _ => T.f0 x
  wAt := T.wAt
  cAt := T.cAt
  sg := T.sg

theorem step : T.tree.Step := fun x m l b => ldLkpNum_step E T.g (T.n' + 1) (T.leaf x m) l b

theorem tree_sg (l : ℕ) : T.tree.sg l = T.sg l := rfl

abbrev TopSt : Type := E × (T.tree.lv (T.n' + 1)).T.St

def enter (x : T.X) : E × (T.tree.lv 0).T.St := (T.t0 x, (x, T.pt0 x))

/-- the state of entry; the levels' rows; the point reached; the form reached -/
def old (x : T.TopSt) : T.X := (T.tree.root (T.n' + 1) x.2).1
def rows (x : T.TopSt) : List (Row E T.J) := (T.tree.rowsAt (T.n' + 1) x.2).reverse
def pnt (x : T.TopSt) : Fin (T.g + (T.n' + 1)) → E := (T.tree.lv (T.n' + 1)).pnt x.2
def form (x : T.TopSt) : T.J → E := pushJ (T.tree.lv (T.n' + 1)).toJ ((T.tree.lv (T.n' + 1)).T.slS
    x.2)

/-- the claim with which level 0 is entered -/
def InHolds (x : T.X) (m : T.J → E) : Prop :=
  Alg.mle (cubeLvl T.g (T.n' + 1) (T.leaf x m) 0) (T.pt0 x) + ∑ j, T.f0 x j * m j = T.t0 x

/-- the claim on the leaves that is reached -/
def TopHolds (x : T.TopSt) (m : T.J → E) : Prop :=
  Alg.mle (fun b : Fin (T.g + (T.n' + 1)) → Bool => T.leaf (T.old x) m (numLE b)) (T.pnt x) +
    ∑ j, T.form x j * m j = x.1

theorem in_iff (x : T.X) (m : T.J → E) :
    (T.tree.lv 0).T.SumHolds (T.enter x) (fun j => m ((T.tree.lv 0).toJ j)) ↔ T.InHolds x m :=
  ldLkpP_sum E T.tree T.step 0 (T.enter x) m

theorem top_iff (x : T.TopSt) (m : T.J → E) :
    (T.tree.lv (T.n' + 1)).T.SumHolds x (fun j => m ((T.tree.lv (T.n' + 1)).toJ j)) ↔ T.TopHolds x
        m := by
  rw [ldLkpP_sum E T.tree T.step (T.n' + 1) x m]
  have hb : (T.tree.lv (T.n' + 1)).base x.2 = T.old x := ldLkpSegK_base E T.tree (T.n' + 1) x.2
  have hU : T.tree.U ((T.tree.lv (T.n' + 1)).base x.2) m (T.n' + 1) =
      fun b : Fin (T.g + (T.n' + 1)) → Bool => T.leaf (T.old x) m (numLE b) := by
    rw [hb]
    exact funext fun b => ldLkpNum_top E T.g (T.n' + 1) (T.leaf (T.old x) m) b
  have hp := ldLkpP_push E _ _ (T.tree.lv (T.n' + 1)).toJ ((T.tree.lv (T.n' + 1)).T.slS x.2) m
  rw [hU, ← hp]
  exact Iff.rfl

/-- The levels 0, .., n' in a row. -/
def segA (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E) : BkA Kc M T.X T.TopSt Ex Wp :=
  (T.tree.treeA Ex Wp Kc msg T.n').preM T.enter

theorem seg_good (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → T.J →
    E)
    (pr : T.X → St) (Ψ ΨR : T.X → (T.J → E) → Prop) :
    (T.segA Ex M Wp Kc msg).Good
      (cj R0 msg pr (fun x m => Ψ x m ∧ T.InHolds x m) fun x m => ΨR x m ∧ T.InHolds x m)
      (cj R0 msg (fun x => pr (T.old x))
        (fun x m => (Ψ (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m)
        fun x m => (ΨR (T.old x) m ∧ RowsHold (T.rows x) m) ∧ T.TopHolds x m) := by
  have g := ldLkpP_tree E T.tree Ex M Wp Kc msg
    (cj R0 msg (fun s => pr s.1) (fun s m => Ψ s.1 m) fun s m => ΨR s.1 m) T.n' T.step
  unfold BkA.Good at g ⊢
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
  refine goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ T.enter ?_ ?_ ?_ ?_ g
  · exact fun x y w h =>
      ⟨h.1, ⟨h.2.1, fun r hr => absurd hr List.not_mem_nil⟩, (T.in_iff x _).mpr h.2.2⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · exact fun x y w _ h => ⟨h.1, h.2.1.1, (T.in_iff x _).mp h.2.2⟩

/-- Knowledge soundness alone, for each fixed tuple of messages; the identity extracts. -/
theorem seg_know (Ex : ExtSpec) (Kc St M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → T.J →
    E)
    (pr : T.X → St) (ΨR : T.X → (T.J → E) → Prop) (m : M) :
    (T.segA Ex M Wp Kc msg).R.red.Know (fun a => R0.on (pr a.1, a.2))
      (fun a wp => R0.relR (pr a.1, a.2) (m, wp) ∧ ΨR a.1 (msg m) ∧ T.InHolds a.1 (msg m))
      (fun b wp => R0.relR (pr (T.old b.1), b.2) (m, wp) ∧
        (ΨR (T.old b.1) (msg m) ∧ RowsHold (T.rows b.1) (msg m)) ∧ T.TopHolds b.1 (msg m))
      (fun _ _ wp => wp) (T.segA Ex M Wp Kc msg).P.err :=
  GoodAt.know (T.seg_good Ex Kc St M Wp R0 msg pr ΨR ΨR) m

theorem seg_rounds (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → T.J → E) :
    (T.segA Ex M Wp Kc msg).R.shape.length = ∑ l ∈ Finset.range (T.n' + 1), (T.g + l + 3 + 1) :=
  ldLkpP_rounds E T.tree Ex M Wp Kc msg T.n'

end ProdT
end
end Lk6

#print axioms Lk6.ProdT.seg_good
#print axioms Lk6.ProdT.seg_know
#print axioms Lk6.ProdT.seg_rounds
