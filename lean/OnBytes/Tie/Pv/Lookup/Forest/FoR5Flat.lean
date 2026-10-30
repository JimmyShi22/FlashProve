-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5Flat.lean.
The layer of the table's leaves and the test on bits: the calls of a run, read as rounds of plain
data, give the flat function's two sumchecks.

OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean says which calls of the channel's routines a run of these
lines makes (`R5D.evs`) and
writes out the two sumchecks' states. Here these calls are read by a reading ρ of the byte-level
field in a commutative ring, and the flat step `TwV.takeSc` is run on them.

 * `flGo_vars`: the calls of the variables' rounds are rounds of plain data.
 * `flEv_evs`: the calls of the whole stretch: the leaves' sumcheck, the round of the fresh point,
   the bits' sumcheck with its round in the further variable and its round of values; behind them
   whatever follows. That they leave no message open is `closed_evs`
   (OnBytes/Tie/Pv/Lookup/Forest/FoR5.lean).
 * `r5_leaves`: `takeSc` on these rounds, at the leaves' public target and the coordinates of the
   table's point in the array's order, without a round of values: the factor, the challenges by
   round and the last claim are those of the state that the routine returns, read; what is left
   begins with the round of the fresh point.
 * `r5_bits`: `takeSc` on what follows that round, at the target 0 and the fresh point reversed,
   with the further variable's 0: the factor, the challenges with the further variable's last, the
   last claim and the shown value are those of the bits' state; what is left is what followed.
Premises: the rounds fit their variables (`FitsA`: in `flEv_evs` both sumchecks', in `r5_leaves` the
leaves', in `r5_bits` the bits'); in `r5_bits` the further variable's round sends 2 scalars.
The fields of the leaves' state are in OnBytes/Tie/Pv/Lookup/Forest/FoR5Ends.lean.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Run

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

private theorem flGo_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)) (l : List Ev),
    FitsA zd rs → flGo ρ [] (evVars zd rs ++ l) = flR ρ (lsOf rs) ++ flGo ρ [] l
  | [], [], _, _ => rfl
  | _ :: zd, r :: rs, l, h =>
    congrArg ((r.1.toList.map ρ.val, [ρ.val r.2]) :: ·) (flGo_vars zd rs l h.2)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem fits_of : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)), FitsA zd rs → Fits zd (lsOf rs)
  | [], [], _ => trivial
  | _ :: zd, r :: rs, h => ⟨by
      show r.1.toList.length + 1 = _
      rw [Array.length_toList, h.1], fits_of zd rs h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem fits_snoc : ∀ (zd : List (E × ℕ)) (rs : List (List E × E)) (p : E × ℕ) (r : List E × E),
    Fits zd rs → r.1.length + 1 = p.2 → Fits (zd ++ [p]) (rs ++ [r])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: zd, _ :: rs, p, r, h, h' => ⟨h.1, fits_snoc zd rs p r h.2 h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem claimAfter_snoc : ∀ (zd : List (E × ℕ)) (rs : List (List E × E)) (p : E × ℕ)
    (r : List E × E) (R : E), Fits zd rs →
    OnBytes.Psc.claimAfter (eqW (zd ++ [p])) (rs ++ [r]) R =
      OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.equality p.1 p.2).complete r.1
        (OnBytes.Psc.claimAfter (eqW zd) rs R)) r.2
  | [], [], _, (_, _), _, _ => by
    simp [eqW, OnBytes.Psc.claimAfter]
  | q :: zd, (a, g) :: rs, p, r, R, h => by
    have e : eqW (q :: zd ++ [p]) = OnBytes.Psc.Weight.equality q.1 q.2 :: eqW (zd ++ [p]) := rfl
    have e' : eqW (q :: zd) = OnBytes.Psc.Weight.equality q.1 q.2 :: eqW zd := rfl
    rw [e, e', List.cons_append, claimAfter_cons, claimAfter_cons]
    exact claimAfter_snoc zd rs p r _ h.2
  | [], _ :: _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, h => h.elim

variable (D : R5D) (m d : ℕ) (rho : Array E)

/-- The bits' rounds with the round in the further variable. -/
def R5D.rsB' : List (List E × E) := lsOf D.rsB ++ [(D.sentY.toList, D.beta)]
/-- The bits' variables with the further one. -/
def R5D.zdB' : List (E × ℕ) := zdB D.ptZ ++ [(zeroE, 3)]

/-- The calls of the stretch as rounds of plain data. -/
theorem flEv_evs (hL : FitsA (zdL m d rho) D.rsL) (hB : FitsA (zdB D.ptZ) D.rsB) (l : List Ev) :
    flEv ρ (D.evs m d rho ++ l) =
      flH ρ D.muL D.epsL (lsOf D.rsL) none ++ (([], rdA ρ D.ptZ) ::
        (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ flEv ρ l)) := by
  unfold flEv R5D.evs flH R5D.rsB'
  simp only [List.append_assoc, List.cons_append, List.nil_append, flGo, List.append_nil]
  rw [flGo_vars ρ _ _ _ hL]
  simp only [flGo, List.nil_append]
  rw [flGo_vars ρ _ _ _ hB]
  simp only [flGo, List.nil_append, flR, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, rdA]

/-- The leaves' sumcheck. -/
theorem r5_leaves (hL : FitsA (zdL m d rho) D.rsL) (C : Aff) (first : ℕ) (rest : Rounds K) :
    takeSc (flH ρ D.muL D.epsL (lsOf D.rsL) none ++ rest) (ρ.val D.tgL)
        ((zdL m d rho).map fun p => ρ.val p.1) false =
      (⟨ρ.val D.epsL, D.rsL.map fun r => ρ.val r.2, ρ.val (D.leaves m d rho C first).claim, []⟩,
        rest) := by
  have h := takeSc_eq ρ (zdL m d rho) D.muL D.epsL D.tgL (lsOf D.rsL) none rest (fits_of _ _ hL)
  simp only [Option.isSome_none, Option.getD_none, List.map_nil, lsOf, List.map_map] at h
  exact h

/-- The bits' sumcheck. -/
theorem r5_bits (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) (first : ℕ)
    (rest : Rounds K) :
    takeSc (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ rest) 0
        (((zdB D.ptZ).map fun p => ρ.val p.1) ++ [0]) true =
      (⟨ρ.val D.epsB, (D.rsB.map fun r => ρ.val r.2) ++ [ρ.val D.beta],
        ρ.val (D.bits2 m d rho first).claim, rdA ρ D.v⟩, rest) := by
  have hf : Fits D.zdB' D.rsB' :=
    fits_snoc _ _ _ _ (fits_of _ _ hB) (by
      show D.sentY.toList.length + 1 = 3
      rw [Array.length_toList, hY])
  have h := takeSc_eq ρ D.zdB' D.muB D.epsB zeroE D.rsB' (some D.v.toList) rest hf
  have hc : OnBytes.Psc.claimAfter (eqW D.zdB') D.rsB' (addE D.muB (mulE D.epsB zeroE)) =
      (D.bits2 m d rho first).claim := claimAfter_snoc _ _ _ _ _ (fits_of _ _ hB)
  rw [hc, ρ.zero] at h
  simp only [R5D.zdB', R5D.rsB', List.map_append, List.map_cons, List.map_nil, ρ.zero,
    Option.isSome_some, Option.getD_some, lsOf, List.map_map] at h
  exact h

end
end Fo
