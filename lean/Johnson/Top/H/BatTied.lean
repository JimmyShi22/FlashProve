-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatTied.lean: at the round "BAT": the target with which the typed fold begins is the
reading of the target of the program's combined row, if the typed rows, laid in the program's order,
have the readings of the program's rows' targets as their targets and the powers of the reading of
the drawn element as their coefficients.

Johnson/Top/H/BatFoldTied.lean ties the target that the typed block "BAT, FOLD epsilon, k × FOLD
round" puts out to the target that the program's fold returns, under a premise on the batching (its
hx). Here that premise is brought down to the rows. The program's half lies in the library: a run of
the batching combines the rows `runRows` in their fixed order (`batVerify_inv`,
OnBytes/Slice/BlkBat.lean), and the combined row's target reads as the sum of x^i times the target
of row number i (`combine_target`, OnBytes/Iop/RowLaws.lean). The typed half is a sum over the names
of the rows, by definition. Statements and proofs.

Main names (c : a caller of the kind `kBatFoldRide` over the program's extension field):
  `sum_horner`: a sum over a list with the coefficients y^k, y^(k+1), … is y^k times `hornerSum`.
  `Ordered c a z x tg`: there is a list of ALL names of the typed rows, each once, at which the
    typed targets are the list tg and the evader's coefficient at the seed z of the name number i is
    (readE x)^i.
  `batX_horner`: then the target that the batching round puts out at z is `hornerSum (readE x) tg`.
  `batFold_tied_rows`: `batFold_tied` with its premise hx replaced: `Ordered` at the readings of the
    targets of the program's rows `runRows`, at the element x that the first pending round drew and
    the seed z read off it; and the library's condition `RowFits` on these rows.
Limits: the target alone. `Ordered` is a premise: that a caller's names of rows can be so laid (the
claim's rows and the members' sample rows in the program's order; an evader of powers) is shown of
no caller. `RowFits` is a premise (the library asks it for its proof alone). One direction.

-/
import Johnson.Top.H.BatFoldTied
import OnBytes.Slice.BlkBat
import OnBytes.Slice.BlkRead
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.BatFoldAt
open OnBytes OnBytes.Slice OnBytes.Model.Road OnBytes.Tie.Pv.Fold Iop OnBytes.Flat KObj KObj.RowCar
open VerifiableInference.OnPublicFiles Cb Cb.Pv
open OnBytes.PscRun (sentOf drawnOf)

/-- A sum over a list with the coefficients y^k, y^(k+1), …. -/
theorem sum_horner {ι K : Type} [CommRing K] (w v : ι → K) (y : K) :
    ∀ (l : List ι) (k : ℕ), (∀ i (h : i < l.length), w l[i] = y ^ (k + i)) →
      (l.map fun ν => w ν * v ν).sum = y ^ k * hornerSum y (l.map v)
  | [], k, _ => by simp [hornerSum]
  | a :: l, k, h => by
    have h0 : w a = y ^ k := h 0 (Nat.succ_pos _)
    have hl : ∀ i (hi : i < l.length), w l[i] = y ^ (k + 1 + i) := fun i hi => by
      have e := h (i + 1) (Nat.succ_lt_succ hi)
      rw [List.getElem_cons_succ] at e
      rw [e]
      congr 1
      omega
    rw [List.map_cons, List.sum_cons, sum_horner w v y l (k + 1) hl, List.map_cons, hornerSum, h0]
    ring

variable (c : BatFoldCaller GE)

/-- The typed rows, laid in a list: all names, each once; their targets; the powers. -/
def Ordered (a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp) (z : c.s.Z.D)
    (x : OnBytes.E) (tg : List GE) : Prop :=
  ∃ ord : List (c.s.G.Row c.s.B), ord.Nodup ∧ (∀ ν, ν ∈ ord) ∧
    ord.map (c.s.G.claims a.1.1 a.2).1 = tg ∧
    ∀ i (h : i < ord.length), c.s.Z.ze z ord[i] = readE x ^ i

/-- Then the batching round's target is the sum under the powers. -/
theorem batX_horner {a : (((c.s.B → GE) × (∀ b, c.s.Sb b)) × c.St₀) × c.s.S.Smp} {z : c.s.Z.D}
    {x : OnBytes.E} {tg : List GE} (h : Ordered c a z x tg) :
    (batX c a z).1.1 = hornerSum (readE x) tg := by
  classical
  obtain ⟨ord, hn, hall, ht, hz⟩ := h
  have e1 : (batX c a z).1.1 =
      ∑ ν, c.s.Z.ze z ν * (c.s.G.claims a.1.1 a.2).1 ν := rfl
  have e2 : (Finset.univ : Finset (c.s.G.Row c.s.B)) = ord.toFinset := by
    ext ν
    simp [hall ν]
  rw [e1, e2, List.sum_toFinset _ hn,
    sum_horner (c.s.Z.ze z) (c.s.G.claims a.1.1 a.2).1 (readE x) ord 0
      (fun i hi => by rw [hz i hi, Nat.zero_add]), pow_zero, one_mul, ht]

variable {c} {rB rE rR : Round} (ρ : Rd c rB rE rR) (L : List (BatFoldCaller GE))

/-- **The target is tied, from the rows.** -/
theorem batFold_tied_rows (hS : ρ.Scal) (hst : StepOK (Yc c).val (Yc c).n c.fx (rd2 c))
    (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1) {g o : Nat} {row : GroupRow}
    {lay : GroupLayout} {F : FoldShape} {out : SingleRows} {x x4 x6 x7 : Ctx}
    (hd : x.ch.dry = false) (ht : ρ.DefAt x.ch.pending)
    (hb : (batVerify g).Yields x (row, lay) x4) (hn : x6.ch = x4.ch)
    (hf : (foldVerify F row (some o)).Yields x6 out x7) (hk : F.layout.k = (Yc c).k)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (hO : ∀ G r t e z, x.st.groups[g]? = some G → x.ch.pending = r :: t →
      r.drawn.elems = [e.triple] → ρ.rdZ (drawnOf r) = some z →
      Ordered c a.1 z e ((runRows x.st G).toList.map fun w => readE w.target))
    (hR : ∀ G, x.st.groups[g]? = some G →
      ∀ w ∈ (runRows x.st G).toList, RowFits (begun x.st g G) w)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (rest : List Fmt.RoundView)
    (hp : x.ch.pending = ρ.V τ ++ rest) :
    ∃ τ' a', ρ.carS.tr τ = some τ' ∧ ((kBatFoldRide L).block c).R.red.out a τ' = some a' ∧
      x7.ch.pending = rest ∧ a'.1.1.1 = readE out.target := by
  obtain ⟨G, e, _, _, r, t, B, -, -, -, p1, -, p3, -, -, -⟩ := batVerify_inv g row lay x x4 hd hb
  refine batFold_tied ρ L hS hst hfx hd ht hb hn hf hk a (fun r' t' z hp' hz => ?_) τ rest hp
  obtain ⟨er, -⟩ := List.cons.inj (p1.symm.trans hp')
  subst er
  rw [batX_horner c (hO G r t e z B.group p1 p3 hz)]
  have h1 := combine_target rdE (begun x.st g G) g ⟨lay, runRows x.st G⟩ e row B.row (hR G B.group)
  simp only [rdE_val] at h1
  exact h1.symm

end VerifiableInference.OnPublicFiles.BatFoldAt

#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batX_horner
#print axioms VerifiableInference.OnPublicFiles.BatFoldAt.batFold_tied_rows
