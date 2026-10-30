-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwLev.lean.
The tie and a product tree: the flat loops on the transcript read as plain data give what `tieN` and
`lvN` read off the states that the typed blocks' value functions put out.

Theorems with their proofs, general in the records `TieF`, `TreeP`, for all typed transcripts, with
any rounds behind.
Main names:
  `tie_wt`, `tie_nx`, `tie_step`, `tie_flatT`, `tie_flat`: `TwV.tieGo` on the tie's plain data is
    `tieN` of the state put out, reversed, and what is behind (`tie_step`, `tie_flatT`: of `tieGoT`,
    Cb/Pv/Lookup/Alg/TwOrdL.lean, which hands back the next target too). `tie_tg`: the target behind
    the tie is the shown value that the last step hands on.
  `lv_wt`: what the flat step knows of a level's variables: its point in the order of the rounds, 0
    for the further variable. `lv_pt`: the point handed on.
  `lev_one`, `lev_step`, `tree_flat`: the same for `TwV.lvGo` and `lvN`; the target and the point
    handed on are the state's own. Premise ho: the orders given to `lvGo` are D.sg's values as
    lists. The loop is started at the target and the point of the state with which the tree is
    entered.
Limits: at the filling `SK₀`, `SV₀` (Cb/Pv/Lookup/Out/TwFill.lean). The states are those of the
value functions `tieV`, `levV`, `treeV` (Cb/Pv/Lookup/Out/TwOut.lean). That a block's reduction puts
them out is `tieK_tot`, `levK_tot`, `treeK_tot` there, under a premise on the block's sumchecks;
for an assembled lookup's own blocks `ltV₀` (Cb/Pv/Lookup/Out/TwFill.lean) meets it. The verifier's
side alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwFlat
import Cb.Pv.Lookup.Alg.TwOrdL
import Cb.Ld.LdLineProofs

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec)

/-! ### the tie -/

theorem tie_wt (D : TieF E) (l : ℕ) (s : (D.lv l).T.St) :
    Wt (D.lv l).T.par.fmt ((D.lv l).T.par.dat s) [0] := by
  cases l with
  | zero => exact wt_snoc_dummy 3 [] () [] rfl
  | succ l => exact wt_snoc_dummy 3 [] () [] rfl

theorem tie_nx (D : TieF E) (l : ℕ) (o : (D.lv l).T.par.Out) :
    (scOf (D.lv l).T.par (tieSh D l) o).v (nxAt l) = o.vals (D.lv l).nx := by
  cases l <;> rfl

theorem tie_step (D : TieF E) (l : ℕ) (x : E × (D.lv l).T.St) (τ : Tr (D.stepK (SK₀ E Ex)
    l).R.shape)
    (rest : Rounds E) :
    tieGoT 1 l x.1 (flStep Ex D l τ ++ rest) =
      ([scOf (D.lv l).T.par (tieSh D l) (stepV (SV₀ E Ex) D l x τ).2],
        (stepV (SV₀ E Ex) D l x τ).1, rest) := by
  have h := takeSc_flat (D.lv l).T.par (tieSh D l) x.1 x.2 [0] (tie_wt D l x.2) τ rest
  show ((takeSc (flSc (D.lv l).T.par (tieSh D l) τ ++ rest) x.1 [0] true).1 :: [],
    (takeSc (flSc (D.lv l).T.par (tieSh D l) τ ++ rest) x.1 [0] true).1.v (nxAt l),
    (takeSc (flSc (D.lv l).T.par (tieSh D l) τ ++ rest) x.1 [0] true).2) = _
  rw [h]
  exact congrArg (fun t => ([scOf (D.lv l).T.par (tieSh D l) (stepV (SV₀ E Ex) D l x τ).2], t,
      rest))
    (tie_nx D l _)

/-- The tie's steps 0, .., n: the flat loop gives `tieN` of the state put out, the oldest first, the
next target, and what is behind. -/
theorem tie_flatT (D : TieF E) : ∀ (n : ℕ) (x : E × (D.lv 0).T.St)
    (τ : Tr (D.tieK (SK₀ E Ex) n).R.shape) (rest : Rounds E),
    tieGoT (n + 1) 0 x.1 (flTie Ex D n τ ++ rest) =
      ((tieN D (n + 1) (tieV (SV₀ E Ex) D n x τ).2).reverse, (tieV (SV₀ E Ex) D n x τ).1, rest)
  | 0, x, τ, rest => tie_step Ex D 0 x τ rest
  | n + 1, x, τ, rest => by
    have ih := tie_flatT D n x (Tr.fst τ)
      (flStep Ex D (n + 1) (Tr.snd (s := (D.tieK (SK₀ E Ex) n).R.shape) τ) ++ rest)
    have hs := tie_step Ex D (n + 1) (tieV (SV₀ E Ex) D n x (Tr.fst τ))
      (Tr.snd (s := (D.tieK (SK₀ E Ex) n).R.shape) τ) rest
    have hf : flTie Ex D (n + 1) τ ++ rest = flTie Ex D n (Tr.fst τ) ++
        (flStep Ex D (n + 1) (Tr.snd (s := (D.tieK (SK₀ E Ex) n).R.shape) τ) ++ rest) :=
      List.append_assoc _ _ _
    rw [tieGoT_snoc, hf, ih, Nat.zero_add]
    show (_ ++ (tieGoT 1 (n + 1) (tieV (SV₀ E Ex) D n x (Tr.fst τ)).1 _).1,
      (tieGoT 1 (n + 1) (tieV (SV₀ E Ex) D n x (Tr.fst τ)).1 _).2) = _
    rw [hs]
    exact congrArg (fun L => (L, (tieV (SV₀ E Ex) D (n + 1) x τ).1, rest))
      (List.reverse_cons (a := scOf (D.lv (n + 1)).T.par (tieSh D (n + 1))
        (tieV (SV₀ E Ex) D (n + 1) x τ).2)).symm

theorem tie_flat (D : TieF E) (n : ℕ) (x : E × (D.lv 0).T.St) (τ : Tr (D.tieK (SK₀ E Ex) n).R.shape)
    (rest : Rounds E) :
    tieGo (n + 1) 0 x.1 (flTie Ex D n τ ++ rest) =
      ((tieN D (n + 1) (tieV (SV₀ E Ex) D n x τ).2).reverse, rest) := by
  rw [tieGo_eq, tie_flatT]

/-- on a run the target behind the tie is the shown value that the last step hands on -/
theorem tie_tg (D : TieF E) (n : ℕ) (x : E × (D.lv 0).T.St) (τ : Tr (D.tieK (SK₀ E Ex) n).R.shape) :
    (tieV (SV₀ E Ex) D n x τ).1 = (tieV (SV₀ E Ex) D n x τ).2.vals (D.lv n).nx := by
  cases n <;> rfl

/-! ### a tree -/

theorem lv_wt (D : TreeP E) (l : ℕ) (s : (D.lv l).T.St) :
    Wt (D.lv l).T.par.fmt ((D.lv l).T.par.dat s)
      (inRounds (List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ))
        (List.ofFn ((D.lv l).pnt s)) ++ [0]) := by
  rw [inRounds_ofFn]
  cases l with
  | zero => exact wt_snoc_dummy 2 _ _ _ (wt_eqs 2 (D.g + 0) (D.z0 s))
  | succ l => exact wt_snoc_dummy 2 _ _ _ (wt_eqs 2 (D.g + l + 1) ((D.cube l).ptS s))

theorem lv_pt (D : TreeP E) (l : ℕ) (o : (D.lv l).T.par.Out) (ρ : E) :
    byVar (List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ))
        (ppList (D.lv l).T.par.fmt o.pt) ++ [ρ] = List.ofFn ((D.lv (l + 1)).pnt (o, ρ)) := by
  rw [byVar_perm, lv_pnt, ofFn_snoc]
  exact congrArg (· ++ [ρ]) (congrArg List.ofFn (funext fun i => (lv_gam D l o i).symm))

variable (o : ℕ → List ℕ)

/-- One level, sumcheck and line: the flat loop gives the level's record, then target and point of
the next level's state, and what is behind. -/
theorem lev_one (D : TreeP E)
    (ho : ∀ l, o l = List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ)) (l : ℕ)
    (x : E × (D.lv l).T.St) (τ : Tr (D.levK (SK₀ E Ex) l).R.shape) (rest : Rounds E) :
    lvGo o 1 l x.1 (List.ofFn ((D.lv l).pnt x.2)) (flLev Ex D l τ ++ rest) =
      ([(scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] (levV (SV₀ E Ex) D l x τ).2.1,
          (levV (SV₀ E Ex) D l x τ).2.2)],
        (levV (SV₀ E Ex) D l x τ).1, List.ofFn ((D.lv (l + 1)).pnt (levV (SV₀ E Ex) D l x τ).2),
        rest) := by
  have hw := lv_wt D l x.2
  rw [← ho l] at hw
  have h := takeSc_flat (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] x.1 x.2 _ hw
    (Tr.fst τ) (flLine Ex D l (Tr.snd (s := ((SK₀ E Ex).full (D.lv l).T.par).R.shape) τ) ++ rest)
  have hf : flLev Ex D l τ ++ rest =
      flSc (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] (Tr.fst τ) ++
        (flLine Ex D l (Tr.snd (s := ((SK₀ E Ex).full (D.lv l).T.par).R.shape) τ) ++ rest) :=
    List.append_assoc _ _ _
  rw [lvGo_succ, hf, h]
  have hp := lv_pt D l (levV (SV₀ E Ex) D l x τ).2.1 (levV (SV₀ E Ex) D l x τ).2.2
  rw [← ho l] at hp
  have ht := ldLine_tg E (D.cube l).toLine (levV (SV₀ E Ex) D l x τ).2.1
    (levV (SV₀ E Ex) D l x τ).2.2
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact ht.symm
  · exact hp

/-- If the flat loop has done c levels and stands at the state x, it does level c too. -/
theorem lev_step (D : TreeP E)
    (ho : ∀ l, o l = List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ)) (c : ℕ)
    (tg0 : E) (pt0 : List E) (rs0 : Rounds E) (x : E × (D.lv c).T.St)
    (τ : Tr (D.levK (SK₀ E Ex) c).R.shape) (rest : Rounds E)
    (h : lvGo o c 0 tg0 pt0 rs0 =
      ((lvN D c x.2).reverse, x.1, List.ofFn ((D.lv c).pnt x.2), flLev Ex D c τ ++ rest)) :
    lvGo o (c + 1) 0 tg0 pt0 rs0 =
      ((lvN D (c + 1) (levV (SV₀ E Ex) D c x τ).2).reverse, (levV (SV₀ E Ex) D c x τ).1,
        List.ofFn ((D.lv (c + 1)).pnt (levV (SV₀ E Ex) D c x τ).2), rest) := by
  rw [lvGo_snoc, h, Nat.zero_add]
  show (_ ++ (lvGo o 1 c x.1 (List.ofFn ((D.lv c).pnt x.2)) (flLev Ex D c τ ++ rest)).1,
    (lvGo o 1 c x.1 (List.ofFn ((D.lv c).pnt x.2)) (flLev Ex D c τ ++ rest)).2) = _
  rw [lev_one Ex o D ho c x τ rest]
  exact congrArg (fun L => (L, (levV (SV₀ E Ex) D c x τ).1,
      List.ofFn ((D.lv (c + 1)).pnt (levV (SV₀ E Ex) D c x τ).2), rest))
    (List.reverse_cons (a := (scOf (D.lv c).T.par [(D.lv c).two false, (D.lv c).two true]
      (levV (SV₀ E Ex) D c x τ).2.1, (levV (SV₀ E Ex) D c x τ).2.2))).symm

/-- A tree's levels 0, .., n: the flat loop gives `lvN` of the state put out, the oldest first, that
state's target and point, and what is behind. -/
theorem tree_flat (D : TreeP E)
    (ho : ∀ l, o l = List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ)) :
    ∀ (n : ℕ) (x : E × (D.lv 0).T.St) (τ : Tr (D.treeK (SK₀ E Ex) n).R.shape) (rest : Rounds E),
    lvGo o (n + 1) 0 x.1 (List.ofFn ((D.lv 0).pnt x.2)) (flTree Ex D n τ ++ rest) =
      ((lvN D (n + 1) (treeV (SV₀ E Ex) D n x τ).2).reverse, (treeV (SV₀ E Ex) D n x τ).1,
        List.ofFn ((D.lv (n + 1)).pnt (treeV (SV₀ E Ex) D n x τ).2), rest)
  | 0, x, τ, rest => lev_step Ex o D ho 0 _ _ _ x τ rest rfl
  | n + 1, x, τ, rest => by
    have hf : flTree Ex D (n + 1) τ ++ rest = flTree Ex D n (Tr.fst τ) ++
        (flLev Ex D (n + 1) (Tr.snd (s := (D.treeK (SK₀ E Ex) n).R.shape) τ) ++ rest) :=
      List.append_assoc _ _ _
    rw [hf]
    exact lev_step Ex o D ho (n + 1) _ _ _ (treeV (SV₀ E Ex) D n x (Tr.fst τ))
      (Tr.snd (s := (D.treeK (SK₀ E Ex) n).R.shape) τ) rest (tree_flat D ho n x (Tr.fst τ) _)

end
end Tw
#print axioms Tw.tie_flat
#print axioms Tw.tie_tg
#print axioms Tw.lev_one
#print axioms Tw.lev_step
#print axioms Tw.tree_flat
