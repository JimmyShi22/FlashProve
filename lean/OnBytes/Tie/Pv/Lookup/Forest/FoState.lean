-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoState.lean.
The state that the lookup's chain of blocks leaves, read as a flat trace, without a reading of the
keys.

The flat function `TwV.traceOfFlat` reads of a record of public numbers only n, v', d, w and the
four orders in which the
sumchecks bind their variables.

Main statements.
* `traceOfFlat_congr`: two records, over any two types of places, that agree in these eight fields
give one trace at all
  plain data.
* `NumsIs A N`: the eight fields of N are those of the assembly A (an order as a list: round j binds
coordinate o[j]).
  `numsIs_of`: the record read off A has this property, so the property is not empty.
* `state_eqN`: for every assembly A, every N with `NumsIs A N`, every state of the caller and every
typed transcript:
  the trace read off the chain's last state is the flat trace of the transcript read as plain data.
  `chn_traceN`: the same of the chain's own reduction.
* The masked claim on the keys as its three fields, read off the trace of any last state: `clK_pt`,
`clK_pnt`, `clK_wt`
  (the point and the weights it lays on the keys), `clK_mf` (the form on the mask entries), `clK_tg`
    (the target).
* `numsA A st`: the public numbers and places of A as a record in which no key is an entry.
`rows16A`: every row that
  the read-out hands on is the flat function's at that record.

Not claimed here: anything on how a key is read from the entries.

-/
import OnBytes.Tie.Pv.Lookup.Out.TwOutEq
import OnBytes.Tie.Pv.Lookup.Value.TwKeyEq

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.LdLkp.Kn TwV Tw3 Tw

/-! ### what the trace reads of the public numbers -/
section
variable {P P' K : Type} [CommRing K]

theorem tgtT_congr (N : Nums P K) (N' : Nums P' K) (hn : N.n = N'.n) (t : Trace K) (th : ℕ) :
    tgtT N t th = tgtT N' t th := by
  unfold tgtT
  rw [hn]

theorem tgT0_congr (N : Nums P K) (N' : Nums P' K) (hn : N.n = N'.n) (hw : N.w = N'.w) (t : Trace K)
    :
    tgT0 N t = tgT0 N' t := by
  unfold tgT0
  rw [hw]
  exact congrArg List.sum (List.map_congr_left fun th _ => by rw [tgtT_congr N N' hn])

theorem traceOfFlat_congr (N : Nums P K) (N' : Nums P' K) (hn : N.n = N'.n) (hv : N.v' = N'.v')
    (hd : N.d = N'.d) (hw : N.w = N'.w) (hK : N.oK = N'.oK) (hT : N.oT = N'.oT) (hE : N.oE = N'.oE)
    (hB : N.oB = N'.oB) (rs : Rounds K) : traceOfFlat N rs = traceOfFlat N' rs := by
  unfold traceOfFlat
  simp only [hn, hv, hd, hK, hT, hE, hB, tgT0_congr N N' hn hw]

end

section
variable {E : Type} [Field E] [Fintype E]

/-- N's numbers and orders are A's own. -/
structure NumsIs {P : Type} (A : LkAsmH E) (N : Nums P E) : Prop where
  n : N.n = A.n
  v' : N.v' = A.v'
  d : N.d = A.d
  w : N.w = A.w
  oK : ∀ l, N.oK l = List.ofFn fun j : Fin (0 + l) => ((A.oK l j : Fin (0 + l)) : ℕ)
  oT : ∀ l, N.oT l = List.ofFn fun j : Fin (A.w + l) => ((A.oT l j : Fin (A.w + l)) : ℕ)
  oE : N.oE = List.ofFn fun j : Fin (A.w + A.d) => ((A.oE j : Fin (A.w + A.d)) : ℕ)
  oB : N.oB = List.ofFn fun j : Fin (A.w + A.d) => ((A.oB j : Fin (A.w + A.d)) : ℕ)

theorem numsIs_of (A : LkAsmH E) (st : A.St) (kAt : ℕ → A.J ⊕ E) : NumsIs A (numsOf A st kAt) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, rfl, rfl⟩

/-- a record of A's public numbers and places that names no reading of the keys -/
noncomputable def numsA (A : LkAsmH E) (st : A.St) : Nums A.J E := numsOf A st fun _ => Sum.inr 0

variable (Ex : ExtSpec) (A : LkAsmH E)

/-- The trace read off the chain's last state is the flat trace at every record N with NumsIs A N:
no reading of the keys enters. -/
theorem state_eqN {P : Type} (N : Nums P E) (hN : NumsIs A N) (st : A.St)
    (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat N (flChn Ex A τ) :=
  (state_eq Ex A st (fun _ => Sum.inr 0) τ).trans
    (traceOfFlat_congr _ N hN.n.symm hN.v'.symm hN.d.symm hN.w.symm (funext fun l => (hN.oK l).symm)
      (funext fun l => (hN.oT l).symm) hN.oE.symm hN.oB.symm _)

theorem chn_traceN {P : Type} (N : Nums P E) (hN : NumsIs A N) (a : A.St × Ex.Str)
    (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    ∃ o : A.XB, (A.chnK (SK₀ E Ex)).R.red.out a τ = some (o, a.2) ∧
      traceOf A o = traceOfFlat N (flChn Ex A τ) :=
  ⟨_, chnK₀_out Ex A a τ, state_eqN Ex A N hN a.1 τ⟩

/-! ### the keys' claim as its three fields, off the trace -/
variable (st : A.St) (o : A.XB)

/-- the library's field pt is the keys' top point read backwards (by its definition) -/
theorem clK_pt : (A.clK (A.oldT o)).pt =
    Blocks.nat fun i : Fin (0 + (A.v' + 1)) =>
      ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).pnt (A.oldT o).2 i.rev := rfl

/-- that point, by coordinate, as the flat function's list -/
theorem clK_pnt : List.ofFn (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).pnt (A.oldT o).2) =
    pntTop (numsA A st).oK [] (traceOf A o).keys.reverse := key_pnt A _ st o

/-- the weights that the claim lays on the keys -/
theorem clK_wt (X : ℕ) (hX : X < 2 ^ (A.v' + 1)) : Blocks.eqN (A.v' + 1) 0 (A.clK (A.oldT o)).pt X =
    TwV.eqN (pntTop (numsA A st).oK [] (traceOf A o).keys.reverse) X := by
  rw [← clK_pnt A st o]
  exact eqN_list (A.v' + 1) (0 + (A.v' + 1)) (Nat.zero_add _) _ X hX

theorem clK_mf (j : A.J) : (A.clK (A.oldT o)).mf j =
    dense (scale (-1) (incTop (numsA A st).ledK (TwV.fK (numsA A st) (traceOf A o))
      (traceOf A o).keys.reverse)) j := by
  rw [dense_scale, show (traceOf A o).keys.reverse =
    lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2 from List.reverse_reverse _]
  have := @lv_inc E _ _ (A.IK.setV (A.v' + 1)).DK A.decJ _ (A.v' + 1) (A.oldT o).2
    (fK_dense A (fun _ => Sum.inr 0) st o) j
  rw [neg_one_mul]
  exact congrArg Neg.neg this

theorem clK_tg : (A.clK (A.oldT o)).tg = (traceOf A o).lam - (traceOf A o).kT := by
  show (A.b2 (A.oR (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).base (A.oldT o).2))).2 - (A.oldT o).1
      = _
  rw [ldLkpSegK_base E (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2]
  rfl

/-- every row beside the keys' claim -/
theorem rows16A : (A.rd o).2.2 =
    ((rowsOfTrace (numsA A (A.rd o).1) (traceOf A o)).dropLast).map toRow := rows16_eq A _ o

end
end Fo
