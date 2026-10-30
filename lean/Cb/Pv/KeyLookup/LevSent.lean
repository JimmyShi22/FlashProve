-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevSent.lean: in each round of the key sides and of the table's tree the message in
the clear has as many values as the list `Lam` says scalars in its column «sent» (`IsS`): at the
library's sumcheck in the list's own count, at the short sumcheck `SK₀` with one coefficient less in
each round with a polynomial (`LRow.short`).

  `SentOK SK f`  of a letter: at every level of every tree with orders. `sentOK_lib`,
                `sentOK_short`.
  `isS_chain`, `tree_isS`, `sides_isS`; `Dat.keysG_isS`, `Dat.tableG_isS`;
  `Dat.keys_isS_lib`, `keys_isS_short`, `table_isS_lib`, `table_isS_short`.
Conditions: 1 ≤ m and 1 ≤ v i (i < m); 1 ≤ d.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevShort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers

/-- Λ's rows of one level of k variables -/
def levRows (q k : ℕ) : List LRow :=
  psc q (List.replicate k 3) (some (2, 2)) ++ [⟨.line, 0, q, 1⟩]

theorem tree_is (q more levels : ℕ) : tree q more levels = (List.range levels).flatMap fun l =>
    levRows q (more + l) := rfl

theorem isS_chain {Ex : ExtSpec} (q : ℕ) (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (g : ℕ →
    List LRow)
    (h : ∀ l, IsS q (b l) (g l)) : ∀ n, IsS q (BkK.chain X b n) ((List.range (n + 1)).flatMap g)
  | 0 => by
    have h0 := h 0
    simpa [BkK.chain, List.range_succ] using h0
  | n + 1 => by
    have h1 := isS_seq (isS_chain q X b g h n) (h (n + 1))
    rw [List.range_succ (n := n + 1), List.flatMap_append]
    simpa [BkK.chain] using h1

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

private theorem card_vec (n : ℕ) : Nat.card (Fin n → E) = Fintype.card E ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

private theorem plain_p (l : List (PFmt E)) :
    plainList (pRounds l) = l.map fun f => Fintype.card E ^ (f.n + 1) := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec (f.n + 1)

private theorem plain_s (l : List (PFmt E)) :
    plainList (sRounds l) = l.map fun f => Fintype.card E ^ f.n := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec f.n

private theorem card_one : Nat.card E = Fintype.card E ^ 1 := by
  rw [Nat.card_eq_fintype_card, pow_one]

theorem lev_fmt (D : TreeP E) (l : ℕ) :
    (D.lv l).T.par.fmt = List.replicate (D.g + l) (pfCube E 2) ++ [pDummy E 2] := by
  cases l <;> rfl

theorem lev_vals (D : TreeP E) (l : ℕ) : Nat.card ((D.lv l).T.par.A → E) = Fintype.card E ^ 2 := by
  cases l <;>
    (show Nat.card (Bool → E) = _
     rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool])

/-- what the column «sent» asks of the sumcheck's letter -/
def SentOK (SK : PscLtK E Ex) (f : LRow → LRow) : Prop :=
  ∀ (D : TreeP E) (l : ℕ), IsS (Fintype.card E) (levK D SK l) ((levRows (Fintype.card E) (D.g +
      l)).map f)

theorem sentOK_lib : SentOK (PscLtK.lib E Ex) id := by
  intro D l
  show Nat.card E :: plainList ((pRounds (D.lv l).T.par.fmt ++ [pRoundV E (D.lv l).T.par.A]) ++
    (lineK Ex D l).R.shape) = _
  have h : plainList ((pRounds (D.lv l).T.par.fmt ++ [pRoundV E (D.lv l).T.par.A]) ++ (lineK Ex D
      l).R.shape) =
      plainList (pRounds (D.lv l).T.par.fmt) ++ [Nat.card ((D.lv l).T.par.A → E), Nat.card Unit] :=
          by
    unfold plainList
    rw [List.map_append, List.map_append, List.append_assoc]
    rfl
  rw [h, plain_p, lev_fmt, lev_vals, card_one]
  simp [levRows, psc, pDummy]

theorem sentOK_short : SentOK (SK₀ E Ex) LRow.short := by
  intro D l
  show Nat.card E :: plainList ((sRounds (D.lv l).T.par.fmt ++ [pRoundV E (D.lv l).T.par.A]) ++
    (lineK Ex D l).R.shape) = _
  have h : plainList ((sRounds (D.lv l).T.par.fmt ++ [pRoundV E (D.lv l).T.par.A]) ++ (lineK Ex D
      l).R.shape) =
      plainList (sRounds (D.lv l).T.par.fmt) ++ [Nat.card ((D.lv l).T.par.A → E), Nat.card Unit] :=
          by
    unfold plainList
    rw [List.map_append, List.map_append, List.append_assoc]
    rfl
  rw [h, plain_s, lev_fmt, lev_vals, card_one]
  simp [levRows, psc, pDummy, LRow.short]

theorem tree_isS (SK : PscLtK E Ex) (f : LRow → LRow) (hS : SentOK SK f) (D : TreeP E) (n : ℕ) :
    IsS (Fintype.card E) (treeK D SK n) ((tree (Fintype.card E) D.g (n + 1)).map f) := by
  rw [tree_is, List.map_flatMap]
  exact isS_chain _ _ _ _ (hS D) n

variable {B : KeyBase E}

theorem sides_isS (SK : PscLtK E Ex) (f : LRow → LRow) (hS : SentOK SK f) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
      IsS (Fintype.card E) (sidesK SK p ps X pr)
        (((p :: ps).flatMap fun r => tree (Fintype.card E) 0 (r.v' + 1)).map f)
  | [], p, X, pr => by
    have h : IsS (Fintype.card E) (p.sideK X pr SK) ((tree (Fintype.card E) 0 (p.v' + 1)).map f) :=
      isS_preM _ (tree_isS SK f hS (p.tree X pr) p.v')
    simpa [sidesK] using h
  | r :: ps, p, X, pr => by
    have h : IsS (Fintype.card E) (p.sideK X pr SK) ((tree (Fintype.card E) 0 (p.v' + 1)).map f) :=
      isS_preM _ (tree_isS SK f hS (p.tree X pr) p.v')
    have h2 := isS_seq h (sides_isS SK f hS ps r (p.SideSt X pr) (p.prN X pr))
    rw [List.flatMap_cons, List.map_append]
    exact h2

namespace Dat
variable (A : Dat E) (L : LevPl A)

theorem keysG_isS (SK : PscLtK E Ex) (f : LRow → LRow) (hS : SentOK SK f) (hm : 1 ≤ A.m)
    (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsS (Fintype.card E) (A.keysK L SK) ((lamKeys (Fintype.card E) A.toPub).map f) := by
  have h := sides_isS (B := A.kb) SK f hS (A.tailP L) (A.part L 0) A.XS id
  have e : (A.part L 0 :: A.tailP L).flatMap (fun r => tree (Fintype.card E) 0 (r.v' + 1)) =
      lamKeys (Fintype.card E) A.toPub := by
    unfold lamKeys
    rw [← A.parts_bits L hm hv, List.flatMap_map]
  rw [e] at h
  exact isS_postM (A.backK L) h

theorem tableG_isS (SK : PscLtK E Ex) (f : LRow → LRow) (hS : SentOK SK f) (hd : 1 ≤ A.d) :
    IsS (Fintype.card E) (A.tableK L SK) ((lamTable (Fintype.card E) A.toPub).map f) := by
  have h : IsS (Fintype.card E) ((A.tabT L).segK SK) ((tree (Fintype.card E) A.mu (A.d - 1 + 1)).map
      f) :=
    isS_preM _ (tree_isS SK f hS (A.tabT L).tree (A.d - 1))
  rw [Nat.sub_add_cancel hd] at h
  exact isS_postM (A.backT L) h

theorem keys_isS_lib (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsS (Fintype.card E) (A.keysK L (PscLtK.lib E Ex)) ((lamKeys (Fintype.card E) A.toPub).map
        id) :=
  A.keysG_isS L _ id sentOK_lib hm hv
theorem keys_isS_short (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsS (Fintype.card E) (A.keysK L (SK₀ E Ex)) ((lamKeys (Fintype.card E) A.toPub).map
        LRow.short) :=
  A.keysG_isS L _ LRow.short sentOK_short hm hv
theorem table_isS_lib (hd : 1 ≤ A.d) :
    IsS (Fintype.card E) (A.tableK L (PscLtK.lib E Ex)) ((lamTable (Fintype.card E) A.toPub).map
        id) :=
  A.tableG_isS L _ id sentOK_lib hd
theorem table_isS_short (hd : 1 ≤ A.d) :
    IsS (Fintype.card E) (A.tableK L (SK₀ E Ex)) ((lamTable (Fintype.card E) A.toPub).map
        LRow.short) :=
  A.tableG_isS L _ LRow.short sentOK_short hd

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_isS_lib
#print axioms Lk6.Dat.keys_isS_short
#print axioms Lk6.Dat.table_isS_lib
#print axioms Lk6.Dat.table_isS_short
