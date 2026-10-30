-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Forest/FoNat.lean.
Two laws of the flat function that lists the lookup's linear rows (`TwV.rowsOfTrace`). Lists alone.

* `r16 N t`: all rows but the row on the keys, in the function's own text. `r16_eq`: it is the list
without its last row.
* `noKey N`: the record N with "no key is an entry, every constant 0". `r16_noKey`: these rows read
neither of the two
  fields on the keys.
* `mapL`, `ledMap`, `rowMap`, `numsMap`: the places renamed along a map ι. `r16_map`: the rows are
natural in the places:
  at the renamed record they are the renamed rows. `incTop_map`, `fK_map`: the same for the form at
    the top of a tree.
* `traceOfFlat_map`, `traceOfFlat_noKey`: the trace reads no place and no field on the keys.

-/
import Cb.Pv.Lookup.Out.TwV
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Fo
open TwV

section
variable {P P' K : Type} [CommRing K]

/-- every row but the keys', in the order of rowsOfTrace, whose text this is -/
def r16 (N : Nums P K) (t : Trace K) : List (SRow P K) :=
  tieRowsR N t.lam t.tie.reverse ++
    (lvRowsR N.ledK 0 (fK N t) t.keys.reverse ++
      ((lvRowsR N.ledT N.w (incT0 N t) t.tabl.reverse ++ [rowEnd N t, rowBitU N t, rowBitE N t]) ++
        [rowNum N]))

theorem r16_eq (N : Nums P K) (t : Trace K) : r16 N t = (rowsOfTrace N t).dropLast := by
  unfold rowsOfTrace
  rw [List.dropLast_concat]
  rfl

/-! ### neither kAt nor kC is read -/

def noKey (N : Nums P K) : Nums P K := { N with kAt := fun _ => none, kC := fun _ => 0 }

theorem tieRowsR_noKey (N : Nums P K) (lam : K) : ∀ l : List (Sc K),
    tieRowsR (noKey N) lam l = tieRowsR N lam l
  | [] => rfl
  | s :: rest => by
    show rowU _ [3] s (tieInc (noKey N) rest) _ :: tieRowsR (noKey N) lam rest =
      rowU _ [3] s (tieInc N rest) _ :: tieRowsR N lam rest
    rw [tieRowsR_noKey N lam rest]
    cases rest <;> rfl

theorem r16_noKey (N : Nums P K) (t : Trace K) : r16 (noKey N) t = r16 N t := by
  unfold r16
  rw [tieRowsR_noKey]
  rfl

theorem traceOfFlat_noKey (N : Nums P K) (rs : Rounds K) :
    traceOfFlat (noKey N) rs = traceOfFlat N rs := rfl

/-! ### the places renamed -/
variable (ι : P → P')

def mapL (f : List (P × K)) : List (P' × K) := f.map fun pc => (ι pc.1, pc.2)
def ledMap (L : Led P) : Led P' := ⟨fun r t => ι (L.pw r t), ι L.c0, fun a => ι (L.sh a)⟩
def rowMap (r : SRow P K) : SRow P' K := ⟨mapL ι r.cf, r.tg⟩
def numsMap (N : Nums P K) : Nums P' K where
  v' := N.v'
  d := N.d
  w := N.w
  n := N.n
  tab := N.tab
  pads := N.pads
  oK := N.oK
  oT := N.oT
  oE := N.oE
  oB := N.oB
  kAt := fun b => (N.kAt b).map ι
  kC := N.kC
  bAt := fun u j => ι (N.bAt u j)
  ledTie := fun l => ledMap ι (N.ledTie l)
  ledK := fun l => ledMap ι (N.ledK l)
  ledT := fun l => ledMap ι (N.ledT l)
  ledE := ledMap ι N.ledE
  ledB := ledMap ι N.ledB

omit [CommRing K] in
theorem mapL_append (f g : List (P × K)) : mapL ι (f ++ g) = mapL ι f ++ mapL ι g := List.map_append

theorem scale_mapL (c : K) (f : List (P × K)) : scale c (mapL ι f) = mapL ι (scale c f) := by
  unfold scale mapL
  rw [List.map_map, List.map_map]
  rfl

theorem hideGo_mapL (pw : ℕ → ℕ → P) : ∀ (dg : List ℕ) (r : ℕ) (xs : List K),
    hideGo (fun r t => ι (pw r t)) r dg xs = mapL ι (hideGo pw r dg xs)
  | [], _, _ => by simp [hideGo, mapL]
  | _ :: _, _, [] => by simp [hideGo, mapL]
  | n :: dg, r, x :: xs => by
    show ((List.range n).map fun t => (ι (pw r t), x ^ (t + 1))) ++ hideGo _ (r + 1) dg xs =
      mapL ι (((List.range n).map fun t => (pw r t, x ^ (t + 1))) ++ hideGo pw (r + 1) dg xs)
    rw [hideGo_mapL pw dg (r + 1) xs, mapL_append]
    congr 1
    unfold mapL
    rw [List.map_map]
    rfl

theorem hide_mapL (L : Led P) (dg : List ℕ) (xs : List K) :
    hide (ledMap ι L) dg xs = mapL ι (hide L dg xs) := by
  unfold hide
  rw [mapL_append]
  exact congrArg (· ++ _) (hideGo_mapL ι L.pw dg 0 xs)

theorem rowU_map (L : Led P) (dg : List ℕ) (s : Sc K) (inc : List (P × K)) (S0 : K) :
    rowU (ledMap ι L) dg s (mapL ι inc) S0 = rowMap ι (rowU L dg s inc S0) := by
  unfold rowU rowMap
  rw [hide_mapL, scale_mapL, mapL_append]

theorem tieInc_map (N : Nums P K) : ∀ l : List (Sc K), tieInc (numsMap ι N) l = mapL ι (tieInc N l)
  | [] => rfl
  | _ :: _ => rfl

theorem tieRowsR_map (N : Nums P K) (lam : K) : ∀ l : List (Sc K),
    tieRowsR (numsMap ι N) lam l = (tieRowsR N lam l).map (rowMap ι)
  | [] => rfl
  | s :: rest => by
    show rowU (ledMap ι (N.ledTie rest.length)) [3] s (tieInc (numsMap ι N) rest)
        (tieS0 N lam rest.length s) :: tieRowsR (numsMap ι N) lam rest = _
    rw [tieInc_map, rowU_map, tieRowsR_map N lam rest]
    rfl

theorem fK_map (N : Nums P K) (t : Trace K) : fK (numsMap ι N) t = mapL ι (fK N t) := rfl

theorem formT_map (N : Nums P K) (t : Trace K) (th : ℕ) :
    formT (numsMap ι N) t th = mapL ι (formT N t th) := by
  unfold formT
  show (if th < N.n + 1 then _ else if th = N.n + 1 then _ else _) = _
  split_ifs <;> rfl

theorem incT0_map (N : Nums P K) (t : Trace K) : incT0 (numsMap ι N) t = mapL ι (incT0 N t) := by
  unfold incT0 mapL
  rw [List.map_flatMap]
  show (List.range (2 ^ N.w)).flatMap _ = _
  refine congrArg (fun f => List.flatMap f (List.range (2 ^ N.w))) (funext fun th => ?_)
  rw [formT_map, scale_mapL]
  rfl

theorem incTop_map (led : ℕ → Led P) (inc0 : List (P × K)) : ∀ l : List (Sc K × K),
    incTop (fun l => ledMap ι (led l)) (mapL ι inc0) l = mapL ι (incTop led inc0 l)
  | [] => rfl
  | _ :: _ => rfl

theorem lvRowsR_map (led : ℕ → Led P) (g : ℕ) (inc0 : List (P × K)) : ∀ l : List (Sc K × K),
    lvRowsR (fun l => ledMap ι (led l)) g (mapL ι inc0) l = (lvRowsR led g inc0 l).map (rowMap ι)
  | [] => rfl
  | s :: rest => by
    show rowU (ledMap ι (led rest.length)) _ s.1 (incTop (fun l => ledMap ι (led l)) (mapL ι inc0)
        rest)
        _ :: lvRowsR (fun l => ledMap ι (led l)) g (mapL ι inc0) rest = _
    rw [incTop_map, rowU_map, lvRowsR_map led g inc0 rest]
    rfl

theorem bitsForm_map (N : Nums P K) (pt : List K) :
    bitsForm (numsMap ι N) pt = mapL ι (bitsForm N pt) := by
  unfold bitsForm mapL
  rw [List.map_map]
  rfl

theorem rowEnd_map (N : Nums P K) (t : Trace K) : rowEnd (numsMap ι N) t = rowMap ι (rowEnd N t) :=
    by
  unfold rowEnd rowMap
  simp only [mapL_append, ← hide_mapL, ← scale_mapL, ← bitsForm_map, ← incTop_map, ← incT0_map]
  rfl

theorem rowBitU_map (N : Nums P K) (t : Trace K) :
    rowBitU (numsMap ι N) t = rowMap ι (rowBitU N t) :=
  rowU_map ι N.ledB _ t.bits [] _

theorem rowBitE_map (N : Nums P K) (t : Trace K) :
    rowBitE (numsMap ι N) t = rowMap ι (rowBitE N t) := by
  unfold rowBitE rowMap
  rw [mapL_append, ← bitsForm_map]
  rfl

theorem rowNum_map (N : Nums P K) : rowNum (numsMap ι N) = rowMap ι (rowNum N) := by
  unfold rowNum rowMap mapL
  simp only [List.map_flatMap, List.map_map]
  rfl

/-- **NATURAL IN THE PLACES.** -/
theorem r16_map (N : Nums P K) (t : Trace K) : r16 (numsMap ι N) t = (r16 N t).map (rowMap ι) := by
  unfold r16
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [tieRowsR_map, fK_map, incT0_map, rowEnd_map, rowBitU_map, rowBitE_map, rowNum_map]
  show _ ++ (lvRowsR (fun l => ledMap ι (N.ledK l)) 0 _ _ ++
    ((lvRowsR (fun l => ledMap ι (N.ledT l)) N.w _ _ ++ _) ++ _)) = _
  rw [lvRowsR_map, lvRowsR_map]

theorem traceOfFlat_map (N : Nums P K) (rs : Rounds K) :
    traceOfFlat (numsMap ι N) rs = traceOfFlat N rs := rfl

end
end Fo
