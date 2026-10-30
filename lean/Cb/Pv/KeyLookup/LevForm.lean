-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevForm.lean: two properties of form of the key sides and of the table's tree over
the flat state: the field st is handed on unchanged; the oracles are only copied (`Bks.FormX`).

 No honest side is named.

  `FormS D SK n`  what is asked of the sumcheck's letter at the levels l ≤ n: it hands its state on
                and only copies. `form_lib`: the library's own does.
  `tree_passes`, `tree_copies`  the levels 0 .. n of a tree with orders.
  `SidesForm`, `sides_passes`, `sides_copies`  m key sides, by recursion.
  `Dat.keys_form`, `Dat.table_form`  `Bks.FormX` of the two blocks; `_lib`: at the library's
                sumcheck,
                without a condition.
Conditions: `FormS`, `SidesForm`: on the letter alone.
The pattern: after Cb.Ld.LdLkpFormatAsm (pass_lev, pass_tree, pass_segK).
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevFit
import Cb.Pv.KeyLookup.AsmForm
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- what is asked of the letter, at the levels l ≤ n -/
def FormS (D : TreeP E) (SK : PscLtK E Ex) (n : ℕ) : Prop :=
  ∀ l ≤ n, (SK.full (D.lv l).T.par).R.Passes Prod.snd PscPar.Out.st ∧
    (SK.full (D.lv l).T.par).R.OnlyCopies

theorem form_lib (D : TreeP E) (n : ℕ) : FormS D (PscLtK.lib E Ex) n := fun l _ =>
  ⟨psc_passes (D.lv l).T.par Ex, psc_onlyCopies (D.lv l).T.par Ex⟩

theorem lev_passes (D : TreeP E) (SK : PscLtK E Ex) (l : ℕ)
    (h : (SK.full (D.lv l).T.par).R.Passes Prod.snd PscPar.Out.st) :
    (levK D SK l).R.Passes (fun x => D.root l x.2) fun x => D.root (l + 1) x.2 :=
  (passes_map h (D.root l)).seq (Passes.draw _ _ Ex _ _ fun _ _ => rfl)

theorem tree_passes (D : TreeP E) (SK : PscLtK E Ex) : ∀ n, FormS D SK n →
    (treeK D SK n).R.Passes (fun x => D.root 0 x.2) fun x => D.root (n + 1) x.2
  | 0, h => lev_passes D SK 0 (h 0 (Nat.le_refl 0)).1
  | n + 1, h =>
    (tree_passes D SK n fun l hl => h l (Nat.le_succ_of_le hl)).seq
      (lev_passes D SK (n + 1) (h (n + 1) (Nat.le_refl _)).1)

theorem tree_copies (D : TreeP E) (SK : PscLtK E Ex) : ∀ n, FormS D SK n → (treeK D SK
    n).R.OnlyCopies
  | 0, h => (h 0 (Nat.le_refl 0)).2.seq (OnlyCopies.draw _ _ Ex)
  | n + 1, h =>
    (tree_copies D SK n fun l hl => h l (Nat.le_succ_of_le hl)).seq
      ((h (n + 1) (Nat.le_refl _)).2.seq (OnlyCopies.draw _ _ Ex))

theorem ProdT.seg_passes (T : ProdT E) (SK : PscLtK E Ex) (h : FormS T.tree SK T.n') :
    (T.segK SK).R.Passes id T.old :=
  (passes_map (tree_passes T.tree SK T.n' h) Prod.fst).pre _ _ fun x x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem ProdT.seg_copies (T : ProdT E) (SK : PscLtK E Ex) (h : FormS T.tree SK T.n') :
    (T.segK SK).R.OnlyCopies := onlyCopies_pre (tree_copies T.tree SK T.n' h) _

variable {B : KeyBase E}

theorem KeyPart.side_passes (p : KeyPart B) (X : Type) (pr : X → B.X0) (SK : PscLtK E Ex)
    (h : FormS (p.tree X pr) SK p.v') : (p.sideK X pr SK).R.Passes id (p.old X pr) :=
  (passes_map (tree_passes (p.tree X pr) SK p.v' h) Prod.fst).pre _ _ fun x x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem KeyPart.side_copies (p : KeyPart B) (X : Type) (pr : X → B.X0) (SK : PscLtK E Ex)
    (h : FormS (p.tree X pr) SK p.v') : (p.sideK X pr SK).R.OnlyCopies :=
  onlyCopies_pre (tree_copies (p.tree X pr) SK p.v' h) _

/-- what is asked of the letter: at every level of every part's tree -/
def SidesForm (SK : PscLtK E Ex) :
    (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) → Prop
  | p, [], X, pr => FormS (p.tree X pr) SK p.v'
  | p, r :: ps, X, pr => FormS (p.tree X pr) SK p.v' ∧ SidesForm SK r ps (p.SideSt X pr) (p.prN X
      pr)

theorem sidesForm_lib : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
    SidesForm (PscLtK.lib E Ex) p ps X pr
  | [], p, X, pr => form_lib (p.tree X pr) p.v'
  | r :: ps, p, X, pr => ⟨form_lib (p.tree X pr) p.v', sidesForm_lib ps r (p.SideSt X pr) (p.prN X
      pr)⟩

theorem sides_passes (SK : PscLtK E Ex) : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type)
    (pr : X → B.X0), SidesForm SK p ps X pr → (sidesK SK p ps X pr).R.Passes id (sidesOld p ps X pr)
  | [], p, X, pr, h => p.side_passes X pr SK h
  | r :: ps, p, X, pr, h =>
    (p.side_passes X pr SK h.1).seq
      (passes_map (sides_passes SK ps r (p.SideSt X pr) (p.prN X pr) h.2) (p.old X pr))

theorem sides_copies (SK : PscLtK E Ex) : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type)
    (pr : X → B.X0), SidesForm SK p ps X pr → (sidesK SK p ps X pr).R.OnlyCopies
  | [], p, X, pr, h => p.side_copies X pr SK h
  | r :: ps, p, X, pr, h =>
    (p.side_copies X pr SK h.1).seq (sides_copies SK ps r (p.SideSt X pr) (p.prN X pr) h.2)

namespace Dat
variable (A : Dat E) (L : LevPl A) (SK : PscLtK E Ex)

theorem keys_form (h : SidesForm (B := A.kb) SK (A.part L 0) (A.tailP L) A.XS id) :
    Bks.FormX (A.keysK L SK) :=
  ⟨(passes_map (sides_passes (B := A.kb) SK (A.tailP L) (A.part L 0) A.XS id h)
      (fun x : A.XS => x.st)).post _ _ fun y x' e => by
        obtain rfl := Option.some.inj e
        rfl,
    onlyCopies_post (sides_copies (B := A.kb) SK (A.tailP L) (A.part L 0) A.XS id h) _⟩

theorem table_form (h : FormS (A.tabT L).tree SK (A.tabT L).n') : Bks.FormX (A.tableK L SK) :=
  ⟨(passes_map ((A.tabT L).seg_passes SK h) (fun x : A.XS => x.st)).post _ _ fun y x' e => by
        obtain rfl := Option.some.inj e
        rfl,
    onlyCopies_post ((A.tabT L).seg_copies SK h) _⟩

theorem keys_form_lib : Bks.FormX (A.keysK L (PscLtK.lib E Ex)) :=
  A.keys_form L _ (sidesForm_lib (B := A.kb) (A.tailP L) (A.part L 0) A.XS id)

theorem table_form_lib : Bks.FormX (A.tableK L (PscLtK.lib E Ex)) :=
  A.table_form L _ (form_lib (A.tabT L).tree (A.tabT L).n')

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_form_lib
#print axioms Lk6.Dat.table_form_lib
