-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/SymF.lean: the library's symbol of a row over the base field (symF,
Johnson/Prover/Send/Core.lean) is the model's symbol (sym, Johnson/LinkSim/Tail.lean) at the
position's evaluation point, and a row over the extension field is three rows over the base field
at the same points.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model"; Johnson/SendSim/At/Sim.lean, "Terms". Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for every code C of the format and every position x, by algebra.
  symF_eq             symF C x m r = sym C.r C.l (ptF C.a x) m r, where ptF a x is the evaluation
                      point of the position x in the base field GF.
  symG_crd            Coordinate t of symG C x m r, the library's symbol of a row over the extension
                      field GE (Johnson/Prover/Link/Base.lean), is sym over GF, at the same point,
                      of the coordinates t of the message and of the tail.
  symF_mod, symG_mod  The position x % 2 ^ C.a gives the same symbol as x.
  symF_add            The symbol of sums is the sum of the symbols.
  symF_congr          symF depends only on the tail below C.r and on the message below C.l.
  symF_shift_pts      At a set of at most C.r points that contains the point of x: the symbol at the
                      message m + dm and the tail t is the symbol at m and the tail t + tailShift
                      (the change of the tail that compensates dm at these points,
                      Johnson/LinkSim/Tail.lean).
  symF_shift          The same at a list of positions of length at most C.r (repeats counted), under
                      any map red of positions.

How it fits. Johnson/SendSim/At/Symbols.lean uses symF_eq, symG_crd and symG_mod to prove that the
honest sender's symbols are those of the instance of the general model. That serves rowsExact and
rowsFresh through shownTie (Johnson/SendSim/At/Shown.lean). No file of Johnson/SendSim/ uses
symF_add, symF_congr, symF_shift_pts, symF_shift or symF_mod: they carry the lemmas on sym over to
symF, as symG_eq, symG_shift and symG_add (Johnson/LinkSim/AtText/Sym.lean) do for symG. The proofs
rest on sym_shift and sym_shift_list (Johnson/LinkSim/Tail.lean) and on point_mod
(Johnson/SendSim/Tie/Point.lean).
-/
import Johnson.Prover.Send.Core
import Johnson.SendSim.Tie.Sym
import Johnson.SendSim.Tie.Point
import Johnson.SendSim.Tie.Coord

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes OnBytes.Slice OnBytes.LinkSim Johnson.Prover.Send
open Johnson.Prover.Link (symG)

/-- The evaluation point of the position x in a code of length 2 ^ a, as an element of the base
field. -/
noncomputable def ptF (a x : ℕ) : GF := toF (Fmt.M1.point a x)

/-- The library's symbol symF of a row over the base field is the model's symbol sym at the
position's evaluation point. -/
theorem symF_eq (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GF) :
    symF C x m r = sym C.r C.l (ptF C.a x) m r := rfl

/-- The symbol of a sum of messages and a sum of tails is the sum of the two symbols. -/
theorem symF_add (C : Fmt.M1.Code) (x : ℕ) (m m' r r' : ℕ → GF) :
    symF C x (m + m') (r + r') = symF C x m r + symF C x m' r' := by
  rw [symF_eq, symF_eq, symF_eq]
  exact sym_add _ _ _ m m' r r'

/-- Messages that agree below C.l and tails that agree below C.r give the same symbol. -/
theorem symF_congr (C : Fmt.M1.Code) (x : ℕ) {m m' r r' : ℕ → GF}
    (hm : ∀ j, j < C.l → m j = m' j) (hr : ∀ q, q < C.r → r q = r' q) :
    symF C x m r = symF C x m' r' := by
  rw [symF_eq, symF_eq]
  exact sym_congr _ _ _ hm hr

open Classical in
/-- If pts has at most C.r points and contains the point of x, then the symbol at x of the message m
+ dm with the tail t is that of m with the tail t + tailShift C.r C.l pts dm. -/
theorem symF_shift_pts (C : Fmt.M1.Code) (pts : Finset GF) (hp : pts.card ≤ C.r)
    (m dm t : ℕ → GF) {x : ℕ} (hx : ptF C.a x ∈ pts) :
    symF C x (m + dm) t = symF C x m (t + tailShift C.r C.l pts dm) := by
  rw [symF_eq, symF_eq]
  exact sym_shift C.r C.l pts hp m dm t hx

open Classical in
/-- The same at a position red x, for x in a list Q of positions of length at most C.r (repeats
counted) and any map red of positions. -/
theorem symF_shift (C : Fmt.M1.Code) (Q : List ℕ) (red : ℕ → ℕ) (hQ : Q.length ≤ C.r)
    (m dm t : ℕ → GF) {x : ℕ} (hx : x ∈ Q) :
    symF C (red x) (m + dm) t =
      symF C (red x) m (t + tailShift C.r C.l (Q.map fun y => ptF C.a (red y)).toFinset dm) := by
  rw [symF_eq, symF_eq]
  exact sym_shift_list C.r C.l Q (fun y => ptF C.a (red y)) hQ m dm t hx

/-- The position x % 2 ^ C.a gives the same symbol symF as x. -/
theorem symF_mod (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GF) :
    symF C (x % 2 ^ C.a) m r = symF C x m r := by
  unfold symF
  rw [point_mod]

/-- The position x % 2 ^ C.a gives the same symbol symG as x. -/
theorem symG_mod (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GE) :
    symG C (x % 2 ^ C.a) m r = symG C x m r := by
  unfold symG
  rw [point_mod]

/-- Coordinate t of the symbol symG of a row over the extension field is the model's symbol over the
base field, at the same point, of the coordinates t of the message and of the tail. -/
theorem symG_crd (t : Fin 3) (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GE) :
    crd t (symG C x m r) =
      sym C.r C.l (ptF C.a x) (fun j => crd t (m j)) fun q => crd t (r q) := by
  unfold symG sym msgPart ptF
  rw [crd_add, crd_sum, crd_sum]
  simp only [crd_cast_mul]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.symG_crd
#print axioms OnBytes.SendSim.symF_eq
#print axioms OnBytes.SendSim.symF_shift_pts
#print axioms OnBytes.SendSim.symF_shift
#print axioms OnBytes.SendSim.symF_mod
#print axioms OnBytes.SendSim.symG_mod
