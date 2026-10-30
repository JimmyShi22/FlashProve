-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LevRunD.lean: at the short sumcheck `SK₀` the verifiers of the key sides and of the
table's tree put out, for all transcripts, a plain function in closed form of the flat state and of
what is sent and drawn.

Main names:
  `Lev.partStep p`   one key side, flat: from (base state, claims so far, rows so far): the levels
                     of the part's tree from the claim on its root; its end claim and rows appended.
  `Lev.sidesStep`, `Lev.fmSides`  m key sides in a row; their formats.
  `Lev.sideAbs`, `Lev.sidesAbs`  the two, tied to the blocks. `Lev.endSS_eq`: what is read behind
                  all
                     sides is the state of entry, the parts' claims and all rows.
  `Dat.keysRun L`, `Dat.tableRun L`  the two plain functions on the flat state.
  `Dat.keys_runs`, `Dat.table_runs`  `Flat.Runs` of `A.keysK L (SK₀ E Ex)`, `A.tableK L (SK₀ E Ex)`
                  at
                     these functions: for all x y τ the verifier's output is the function of x and
                     of the view of τ.
Limits: [DecidableEq E]. Nothing on an honest side. Nothing on the verifier in OnBytes/Iop/Lkp.lean.

-/
import Cb.Pv.KeyLookup.LevRunC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Lev
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers Flat

/-- What is read off a state between key sides: the base state, the claims and the rows so far. -/
abbrev SS (E J Y : Type) : Type := Y × List (MCl E J) × List (Row E J)

/-- the point of a masked claim on 2^v entries, top bit first, from the point by variable -/
def ptTop {E : Type} [Zero E] (v : ℕ) (l : List E) : ℕ → E :=
  fun n => if n < v then l.getD (v - 1 - n) 0 else 0

theorem ptTop_eq {E : Type} [Zero E] (v : ℕ) (g : Fin v → E) :
    (Blocks.nat fun i : Fin v => g i.rev) = ptTop v (List.ofFn g) := by
  funext n
  unfold Blocks.nat ptTop
  by_cases h : n < v
  · rw [dif_pos h, if_pos h]
    have e : v - 1 - n = ((⟨n, h⟩ : Fin v).rev).val := by
      rw [Fin.val_rev]
      show v - 1 - n = v - (n + 1)
      omega
    rw [e, getD_ofFn g]
  · rw [dif_neg h, if_neg h]

section
variable {E : Type} [Field E] [Fintype E] {B : KeyBase E} [DecidableEq B.J]

instance (p : KeyPart B) (X : Type) (pr : X → B.X0) : DecidableEq (p.tree X pr).J :=
  inferInstanceAs (DecidableEq B.J)

/-- the orders and places of a part as plain data -/
def partD (p : KeyPart B) : TreeD B.J 0 where
  sg := p.oK
  wv := fun l r t => p.wK l (nmV E (0 + l) r t)
  wc := fun l => p.wK l (nmC E (0 + l))
  c := p.cK

/-- with what a part's tree is entered; what is made of what it leaves -/
def partIn (p : KeyPart B) (s : SS E B.J B.X0) : SS E B.J B.X0 × Acc E B.J :=
  (s, ⟨[], p.fK s.1, p.tK s.1, []⟩)
def partOut (p : KeyPart B) (s : SS E B.J B.X0 × Acc E B.J) : SS E B.J B.X0 :=
  (s.1.1, s.1.2.1 ++ [⟨ptTop (p.v' + 1) s.2.pt, fun j => - s.2.mf j, B.lam s.1.1 - s.2.tg⟩],
    s.1.2.2 ++ s.2.rows)

/-- One key side, flat. -/
def partStep (p : KeyPart B) (s : SS E B.J B.X0) (f : List (RV E)) : SS E B.J B.X0 :=
  partOut p (treeStep (partD p) p.v' (partIn p s) f)

def fmSides : KeyPart B → List (KeyPart B) → List Fm
  | p, [] => fmT 0 p.v'
  | p, r :: ps => fmT 0 p.v' ++ fmSides r ps

/-- m key sides, flat. -/
def sidesStep : KeyPart B → List (KeyPart B) → SS E B.J B.X0 → List (RV E) → SS E B.J B.X0
  | p, [] => partStep p
  | p, r :: ps => seqRun (fmT 0 p.v').length (partStep p) (sidesStep r ps)

/-- what is read behind a side, from what was read before it -/
noncomputable def nextSS (p : KeyPart B) (X : Type) (pr : X → B.X0) (αX : X → SS E B.J B.X0)
    (z : p.SideSt X pr) : SS E B.J B.X0 :=
  ((αX (p.old X pr z)).1, (αX (p.old X pr z)).2.1 ++ [p.cl X pr z],
    (αX (p.old X pr z)).2.2 ++ p.rows X pr z)

noncomputable def endSS : (p : KeyPart B) → (ps : List (KeyPart B)) → (X : Type) → (pr : X → B.X0) →
    (X → SS E B.J B.X0) → SidesSt p ps X pr → SS E B.J B.X0
  | p, [], X, pr, αX => nextSS p X pr αX
  | p, r :: ps, X, pr, αX => endSS r ps (p.SideSt X pr) (p.prN X pr) (nextSS p X pr αX)

theorem endSS_eq : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0)
    (αX : X → SS E B.J B.X0) (z : SidesSt p ps X pr),
    endSS p ps X pr αX z = ((αX (sidesOld p ps X pr z)).1,
      (αX (sidesOld p ps X pr z)).2.1 ++ sidesCl p ps X pr z,
      (αX (sidesOld p ps X pr z)).2.2 ++ sidesRows p ps X pr z)
  | [], _, _, _, _, _ => rfl
  | r :: ps, p, X, pr, αX, z => by
    refine (endSS_eq ps r (p.SideSt X pr) (p.prN X pr) (nextSS p X pr αX) z).trans ?_
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact List.append_assoc _ _ _
    · exact List.append_assoc _ _ _

variable [DecidableEq E] {Ex : ExtSpec}

/-- One key side. -/
noncomputable def sideAbs (p : KeyPart B) (X : Type) (pr : X → B.X0) (αX : X → SS E B.J B.X0)
    (h : ∀ x, (αX x).1 = pr x) :
    Abs (p.sideK X pr (SK₀ E Ex)) (fmT 0 p.v') αX (nextSS p X pr αX) (partStep p) :=
  (((treeAbs (Ex := Ex) (p.tree X pr) (fun s => αX s.1) p.v').preM
      (enterK ((p.inst X pr).setV (p.v' + 1)) fun x => p.tK (pr x)) αX (partIn p) (fun x => by
        refine Prod.ext rfl ?_
        show (⟨_, _, _, _⟩ : Acc E B.J) = ⟨_, _, _, _⟩
        rw [h x]
        congr 1
        exact pushJ_id (J := B.J) _)).mapOut (nextSS p X pr αX) (partOut p) (fun z => by
        have hb : ((p.tree X pr).lv (p.v' + 1)).base z.2 = p.old X pr z :=
          ldLkpSegK_base E (p.tree X pr) (p.v' + 1) z.2
        refine Prod.ext rfl (Prod.ext ?_ rfl)
        refine congrArg (fun c => (αX (p.old X pr z)).2.1 ++ [c]) ?_
        show (⟨_, _, _⟩ : MCl E B.J) = ⟨_, _, _⟩
        congr 1
        · exact (ptTop_eq (0 + (p.v' + 1)) _).trans
            (congrArg (fun k => ptTop k _) (Nat.zero_add (p.v' + 1)))
        · show B.lam (pr (((p.tree X pr).lv (p.v' + 1)).base z.2)) - z.1 = _
          rw [hb, ← h]
          rfl)).stepEq fun _ _ => rfl

/-- m key sides. -/
noncomputable def sidesAbs : (ps : List (KeyPart B)) → (p : KeyPart B) → (X : Type) →
    (pr : X → B.X0) → (αX : X → SS E B.J B.X0) → (∀ x, (αX x).1 = pr x) →
    Abs (sidesK (SK₀ E Ex) p ps X pr) (fmSides p ps) αX (endSS p ps X pr αX) (sidesStep p ps)
  | [], p, X, pr, αX, h => sideAbs p X pr αX h
  | r :: ps, p, X, pr, αX, h =>
    (sideAbs p X pr αX h).seq
      (sidesAbs ps r (p.SideSt X pr) (p.prN X pr) (nextSS p X pr αX) fun z => h (p.old X pr z))

end
end Lev

namespace Dat
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers Flat Lev
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (L : LevPl A)

instance : DecidableEq A.kb.J := inferInstanceAs (DecidableEq A.J)
instance : DecidableEq (A.tabT L).tree.J := inferInstanceAs (DecidableEq A.J)

/-- back into the flat state, from what is read behind the key sides -/
def keysBack (s : SS E A.J A.XS) : A.XS :=
  { s.1 with
    cls := fun i => s.2.1.getD i ⟨0, 0, 0⟩
    rows := s.1.rows ++ s.2.2 }

/-- The key sides on the flat state. -/
def keysRun (x : A.XS) (f : List (RV E)) : A.XS :=
  A.keysBack (sidesStep (B := A.kb) (A.part L 0) (A.tailP L) (x, [], []) f)

def keysFm : List Fm := fmSides (B := A.kb) (A.part L 0) (A.tailP L)

/-- with what the table's tree is entered; back into the flat state -/
def tabIn (x : A.XS) : A.XS × Acc E A.J :=
  (x, ⟨List.ofFn fun i : Fin (A.mu + 0) => x.pt i, x.top.mf, x.top.tg, []⟩)
def tabBack (s : A.XS × Acc E A.J) : A.XS :=
  { s.1 with
    top := ⟨s.2.mf, s.2.tg⟩
    pt := fun i => if i < A.mu + (A.d - 1 + 1) then s.2.pt.getD i 0 else 0
    rows := s.1.rows ++ s.2.rows }

/-- the orders and places of the table's tree as plain data -/
def tabD : TreeD A.J A.mu where
  sg := ordTab A.mu
  wv := fun l r t => L.wT l (nmV E (A.mu + l) r t)
  wc := fun l => L.wT l (nmC E (A.mu + l))
  c := L.cT

/-- The table's tree on the flat state. -/
def tableRun (x : A.XS) (f : List (RV E)) : A.XS :=
  A.tabBack (treeStep (A.tabD L) (A.d - 1) (A.tabIn x) f)

variable [DecidableEq E] {Ex : ExtSpec}

/-- For all transcripts the key sides' verifier puts out `keysRun` of the state and the view. -/
noncomputable def keys_runs : Runs (A.keysK L (SK₀ E Ex)) (A.keysFm L) (A.keysRun L) :=
  ((((sidesAbs (Ex := Ex) (B := A.kb) (A.tailP L) (A.part L 0) A.XS id (fun x => (x, [], []))
      fun _ => rfl).postM (A.backK L) id A.keysBack (fun z => by
        rw [endSS_eq]
        rfl)).mapIn id (fun x => (x, [], [])) fun _ => rfl).stepEq fun _ _ => rfl).toRuns

/-- For all transcripts the table's tree's verifier puts out `tableRun` of the state and the view.
-/
noncomputable def table_runs : Runs (A.tableK L (SK₀ E Ex)) (fmT A.mu (A.d - 1)) (A.tableRun L) :=
  ((((treeAbs (Ex := Ex) (A.tabT L).tree (fun s => s.1) (A.d - 1)).preM (A.tabT L).enter id A.tabIn
      (fun x => by
        refine Prod.ext rfl ?_
        show (⟨_, _, _, _⟩ : Acc E A.J) = ⟨_, _, _, _⟩
        congr 1
        exact pushJ_id (J := A.J) _)).postM (A.backT L) id A.tabBack (fun z => by
        have hp : (fun i => if h : i < A.mu + (A.d - 1 + 1) then (A.tabT L).pnt z ⟨i, h⟩ else 0) =
            fun i => if i < A.mu + (A.d - 1 + 1) then (List.ofFn ((A.tabT L).pnt z)).getD i 0
              else 0 := by
          funext i
          by_cases h : i < A.mu + (A.d - 1 + 1)
          · rw [dif_pos h, if_pos h]
            exact (getD_ofFn ((A.tabT L).pnt z) ⟨i, h⟩).symm
          · rw [dif_neg h, if_neg h]
        exact congrArg (fun q => ({ (A.tabT L).old z with
          top := ⟨(A.tabT L).form z, z.1⟩
          pt := q
          rows := ((A.tabT L).old z).rows ++ A.rowsT L z } : A.XS)) hp)).stepEq
      fun _ _ => rfl).toRuns

end Dat
end Lk6

#print axioms Lk6.Dat.keys_runs
#print axioms Lk6.Dat.table_runs
