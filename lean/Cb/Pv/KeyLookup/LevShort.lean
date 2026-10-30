-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevShort.lean: the key sides and the table's tree at the short sumcheck `SK₀` (in
each round with a polynomial the constant is not sent): every statement that stands at the library's
sumcheck.

 No honest side is named.

  `ListOK SK`   what the lists ask of a letter: at every sumcheck on k cube variables of degree 2
                its
                errors and numbers of values are the library's two lists. `listOK_lib`,
                `listOK_short`.
  `levG_isL`, `treeG_isL`, `sidesG_isL`, `Dat.keysG_isL`, `Dat.tableG_isL`  the lists at any letter
                with `ListOK`.
  `lt_short`, `sidesLt_short`, `form_short`, `sidesForm_short`  the conditions on the letter hold at
                `SK₀`.
  `Dat.keys_know_short`, `table_know_short`; `keys_form_short`, `table_form_short`;
  `keys_supp_short`, `table_supp_short`; `keys_isL_short`, `table_isL_short`.
Conditions: the public numbers of the statements at the library's sumcheck (1 ≤ m; 1 ≤ v i; 1 ≤ d;
`L.In G`); none on the letter.
Not claimed: how many scalars are sent (LevSent.lean).
Not claimed: anything on completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevLam
import Cb.Pv.KeyLookup.LevSupp
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- what the lists ask of the sumcheck's letter -/
def ListOK (SK : PscLtK E Ex) : Prop :=
  ∀ (T : PscOur E) (k : ℕ), T.fmt = List.replicate k (pfCube E 2) →
    (SK.full T.par).e.toList = pscErrs k 2 T.DY ∧
      (SK.full T.par).R.shape.chalList = pscVals (Fintype.card E) k

theorem listOK_lib : ListOK (PscLtK.lib E Ex) := fun T k hf => ll_psc T k 2 hf Ex Unit
theorem listOK_short : ListOK (SK₀ E Ex) := fun T k hf => SK₀_ll Ex T k 2 hf

theorem levG_isL (SK : PscLtK E Ex) (hS : ListOK SK) (D : TreeP E) (l : ℕ) :
    IsL (levK D SK l)
      (psc (Fintype.card E) (List.replicate (D.g + l) 3) (some (2, 2)) ++ [⟨.line, 0, Fintype.card
          E, 1⟩]) := by
  have h := hS (D.lv l).T (D.g + l) (tree_fmt D l).1
  rw [(tree_fmt D l).2] at h
  refine isL_seq (a := SK.full (D.lv l).T.par) (b := lineK Ex D l) ⟨?_, ?_⟩ ⟨rfl, rfl⟩
  · rw [psc_c]; exact h.1
  · rw [psc_n]; exact h.2

theorem treeG_isL (SK : PscLtK E Ex) (hS : ListOK SK) (D : TreeP E) (n : ℕ) :
    IsL (treeK D SK n) (tree (Fintype.card E) D.g (n + 1)) :=
  isL_chain _ _ _ (levG_isL SK hS D) n

theorem lt_short (D : TreeP E) {M : Type} (Wp Kc : Type) (msg : M → D.J → E) (n : ℕ) :
    LtS D (SK₀ E Ex) Wp Kc msg n := fun l _ =>
  SK₀_ourK M Wp Kc (D.lv l).T (D.msgAt M msg l) (ldLkpP_ok E D l).1 (ldLkpP_ok E D l).2.2.1
    (ldLkpP_ok E D l).2.2.2 (ldLkpP_ok E D l).2.1

theorem form_short (D : TreeP E) (n : ℕ) : FormS D (SK₀ E Ex) n := fun l _ =>
  ⟨SK₀_passes Ex (D.lv l).T.par, SK₀_copies Ex (D.lv l).T.par⟩

variable {B : KeyBase E}

theorem sidesG_isL (SK : PscLtK E Ex) (hS : ListOK SK) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
      IsL (sidesK SK p ps X pr) ((p :: ps).flatMap fun r => tree (Fintype.card E) 0 (r.v' + 1))
  | [], p, X, pr => by
    have h : IsL (p.sideK X pr SK) (tree (Fintype.card E) 0 (p.v' + 1)) :=
      isL_preM _ (treeG_isL SK hS (p.tree X pr) p.v')
    simpa [sidesK] using h
  | r :: ps, p, X, pr => by
    have h : IsL (p.sideK X pr SK) (tree (Fintype.card E) 0 (p.v' + 1)) :=
      isL_preM _ (treeG_isL SK hS (p.tree X pr) p.v')
    have h2 := isL_seq h (sidesG_isL SK hS ps r (p.SideSt X pr) (p.prN X pr))
    rw [List.flatMap_cons]
    exact h2

theorem sidesLt_short {M : Type} (Wp Kc : Type) (msg : M → B.J → E) :
    ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
      SidesLt (SK₀ E Ex) Wp Kc msg p ps X pr
  | [], p, X, pr => lt_short (p.tree X pr) Wp Kc msg p.v'
  | r :: ps, p, X, pr =>
    ⟨lt_short (p.tree X pr) Wp Kc msg p.v', sidesLt_short Wp Kc msg ps r (p.SideSt X pr) (p.prN X
        pr)⟩

theorem sidesForm_short : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
    SidesForm (SK₀ E Ex) p ps X pr
  | [], p, X, pr => form_short (p.tree X pr) p.v'
  | r :: ps, p, X, pr => ⟨form_short (p.tree X pr) p.v', sidesForm_short ps r (p.SideSt X pr) (p.prN
      X pr)⟩

namespace Dat
variable (A : Dat E) (L : LevPl A)

theorem keysG_isL (SK : PscLtK E Ex) (hS : ListOK SK) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsL (A.keysK L SK) (lamKeys (Fintype.card E) A.toPub) := by
  have h := sidesG_isL (B := A.kb) SK hS (A.tailP L) (A.part L 0) A.XS id
  have e : (A.part L 0 :: A.tailP L).flatMap (fun r => tree (Fintype.card E) 0 (r.v' + 1)) =
      lamKeys (Fintype.card E) A.toPub := by
    unfold lamKeys
    rw [← A.parts_bits L hm hv, List.flatMap_map]
  rw [e] at h
  exact isL_postM (A.backK L) h

theorem tableG_isL (SK : PscLtK E Ex) (hS : ListOK SK) (hd : 1 ≤ A.d) :
    IsL (A.tableK L SK) (lamTable (Fintype.card E) A.toPub) := by
  have h : IsL ((A.tabT L).segK SK) (tree (Fintype.card E) A.mu (A.d - 1 + 1)) :=
    isL_preM _ (treeG_isL SK hS (A.tabT L).tree (A.d - 1))
  rw [Nat.sub_add_cancel hd] at h
  exact isL_postM (A.backT L) h

theorem keys_know_short (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    (A.keysK L (SK₀ E Ex)).Know (A.jt R0 msg Mu A.Joined) (A.jt R0 msg Mu fun x μ => A.Table x μ
        0) :=
  A.keys_know L _ Kc M Wp R0 msg Mu hm hv
    (sidesLt_short (B := A.kb) Wp Kc msg (A.tailP L) (A.part L 0) A.XS id)

theorem table_know_short (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hd : 1 ≤ A.d) :
    (A.tableK L (SK₀ E Ex)).Know (A.jt R0 msg Mu fun x μ => A.Table x μ 0)
      (A.jt R0 msg Mu fun x μ => A.Table x μ A.d) :=
  A.table_know L _ Kc M Wp R0 msg Mu hd (lt_short (A.tabT L).tree Wp Kc msg (A.tabT L).n')

theorem keys_form_short : Bks.FormX (A.keysK L (SK₀ E Ex)) :=
  A.keys_form L _ (sidesForm_short (B := A.kb) (A.tailP L) (A.part L 0) A.XS id)

theorem table_form_short : Bks.FormX (A.tableK L (SK₀ E Ex)) :=
  A.table_form L _ (form_short (A.tabT L).tree (A.tabT L).n')

theorem keys_supp_short (G : A.J → Prop) (hL : L.In G) :
    Inv (A.keysK L (SK₀ E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.keys_supp L _ G hL (sidesForm_short (B := A.kb) (A.tailP L) (A.part L 0) A.XS id)

theorem table_supp_short (G : A.J → Prop) (hL : L.In G) :
    Inv (A.tableK L (SK₀ E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.table_supp L _ G hL (form_short (A.tabT L).tree (A.tabT L).n')

theorem keys_isL_short (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsL (A.keysK L (SK₀ E Ex)) (lamKeys (Fintype.card E) A.toPub) :=
  A.keysG_isL L _ listOK_short hm hv

theorem table_isL_short (hd : 1 ≤ A.d) :
    IsL (A.tableK L (SK₀ E Ex)) (lamTable (Fintype.card E) A.toPub) :=
  A.tableG_isL L _ listOK_short hd

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_know_short
#print axioms Lk6.Dat.table_know_short
#print axioms Lk6.Dat.keys_form_short
#print axioms Lk6.Dat.table_form_short
#print axioms Lk6.Dat.keys_supp_short
#print axioms Lk6.Dat.table_supp_short
#print axioms Lk6.Dat.keys_isL_short
#print axioms Lk6.Dat.table_isL_short
