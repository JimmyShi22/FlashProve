-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/ClosePoint.lean: at which point the end claims of the closing and of the test of the
bits read the bits: coordinate t is place k − 1 − t of the sumcheck's point, k := mu + d.

It imports the library, Bits.lean and Cb/Pv/KeyLookup/PtGet.lean (`ppGet`: place j of a point;
`hFnOf_get`); no file of the port.

A sumcheck's point (`PscPar.Mid.pt`, `Out.pt`) lists the challenges in the order of the rounds; at
the short sumcheck that is shown in CloseLaid.lean.
  `Clo.hFnMix_get`, `Clo.hLast_get`   the readers of a point read place j, and the last place.
  `A.gamE P zz`, `A.gamB P o`   the places of the point, in the order of the rounds.
  `A.ptE P zz`, `A.ptB P o`     the end points by variable: place t holds place k − 1 − t of the
                  point, k := mu + d.
  `en_reads`      the map that stays in the closing's end claim is the extension of the bits (0 at a
                  dead plane) at `ptE`.
  `A.facE`, `en_fac`   the public factor beside it is the extension of al − 1 − table at the d row
                  places of `ptE`.
  `bt_reads`      the output claim's clause on the shown value (`PscPar.EHolds`; as a row: `rowV`,
                  by `rows_iff` of Bits.lean) says: (extension of the bits at `ptB`) + (mask at cB)
                  · β = the shown value. `betaB_get`: β is place mu + d of the point.
  `rowE_tg`       the target of the closing's end row is the last value less ε.

-/
import Cb.Pv.KeyLookup.Bits
import Cb.Pv.KeyLookup.PtGet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Finset

noncomputable section

namespace Clo
variable {E : Type} [Field E] [Fintype E]

theorem hFnMix_get : ∀ (k : ℕ) (dg : Fin k → ℕ) (d : PDats (pfMix E k dg))
    (γ : PPt (pfMix E k dg)) (j : Fin k),
    hFnMix E k dg d (pH (pfMix E k dg) d γ) j = ppGet (pfMix E k dg) γ j
  | 0, _, _, _, j => j.elim0
  | k + 1, dg, d, γ, j => by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact hFnMix_get k (fun i => dg i.succ) d.2 γ.2 i

omit [Fintype E] in
theorem hLast_get : ∀ (l : List (PFmt E)) (d : PDats l) (f : PFmt E) (e : PDat E f)
    (γ : PPt (l ++ [f])),
    hLast l d f e (pH (l ++ [f]) (PDats.snoc l d f e) γ) = ppGet (l ++ [f]) γ l.length
  | [], _, _, _, _ => rfl
  | _ :: l, d, f, e, γ => hLast_get l d.2 f e γ.2

end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-! ### the closing -/

/-- The places of the closing's point, and its end point by variable. -/
def gamE (zz : (A.En P).par.Mid) : Fin (A.mu + A.d) → E := fun i => ppGet (A.En P).par.fmt zz.pt i
def ptE (zz : (A.En P).par.Mid) : Fin (A.mu + A.d) → E := fun t => A.gamE P zz t.rev

theorem en_point (zz : (A.En P).par.Mid) :
    (A.En P).fn zz.st ((A.En P).par.hp zz.st zz.pt) = A.gamE P zz :=
  funext fun i => Clo.hFnMix_get _ _ _ zz.pt i

theorem en_reads (zz : (A.En P).par.Mid) (μ : A.J → E) :
    (A.En P).par.Gb zz.st (ext0 μ) () ((A.En P).par.hp zz.st zz.pt) =
      Alg.mle (fun c => ext0 μ (A.cell c)) (A.ptE P zz) := by
  show (A.En P).Y (ext0 μ) ((A.En P).fn zz.st ((A.En P).par.hp zz.st zz.pt)) = _
  rw [A.en_point P zz, A.en_Y P μ]
  rfl

/-- The public factor at the end point. -/
def facE (zz : (A.En P).par.Mid) : E :=
  Alg.mle (fun r : Fin A.d → Bool =>
      (show A.XS from zz.st).al - 1 - A.tab (show A.XS from zz.st).st (numLE r))
    fun r => A.ptE P zz (Fin.natAdd A.mu r)

theorem en_fac (zz : (A.En P).par.Mid) (v : Empty → E) :
    (A.En P).par.S1 zz.st ((A.En P).par.hp zz.st zz.pt) v () = A.facE P zz := by
  show Alg.mle ((A.En P).cp zz.st)
    (fun r => (A.En P).fn zz.st ((A.En P).par.hp zz.st zz.pt) ((A.En P).rw r)) = _
  rw [A.en_point P zz]
  rfl

theorem rowE_tg (zz : (A.En P).par.Mid) : (A.rowE P zz).tg = zz.fin - zz.eps :=
  endM_tg E (A.En P) zz

/-! ### the bits' test -/

/-- The places of the point of the test of the bits (place mu + d: the further variable's), its end
point by variable, the further variable's place. -/
def gamB (o : (A.BT P).par.Out) : ℕ → E := fun i => ppGet (A.BT P).par.fmt o.pt i
def ptB (o : (A.BT P).par.Out) : Fin (A.mu + A.d) → E := fun t => A.gamB P o t.rev
def betaB (o : (A.BT P).par.Out) : E := (A.BT P).lst o.st ((A.BT P).par.hp o.st o.pt)

theorem bt_point (o : (A.BT P).par.Out) :
    (A.Bt P).zc.fn o.st.2.2 ((A.BT P).ini o.st ((A.BT P).par.hp o.st o.pt)) = A.ptB P o :=
  funext fun t =>
    hFnOf_get (pfCube E 2) (pDummy E 2) (pDummyD E 2) (A.mu + A.d) _ o.pt t.rev

theorem betaB_get (o : (A.BT P).par.Out) : A.betaB P o = A.gamB P o (A.mu + A.d) := by
  have h := Clo.hLast_get (A.BT P).fmt ((A.BT P).dat o.st) (pDummy E 2) (pDummyD E 2) o.pt
  have hl : (A.BT P).fmt.length = A.mu + A.d := List.length_replicate
  rw [hl] at h
  exact h

theorem bt_reads (o : (A.BT P).par.Out) (μ : A.J → E) :
    (A.BT P).par.EHolds o (ext0 μ) () ↔
      Alg.mle (fun c => ext0 μ (A.cell c)) (A.ptB P o) + μ P.cB * A.betaB P o = o.vals () := by
  have h := ldLkpBitP_row E (A.Bt P) o (ext0 μ)
  rw [A.bt_point P o] at h
  exact h

end Dat
end
end Lk6

#print axioms Lk6.Dat.en_reads
#print axioms Lk6.Dat.en_fac
#print axioms Lk6.Dat.rowE_tg
#print axioms Lk6.Dat.bt_reads
#print axioms Lk6.Dat.betaB_get
