-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndForms.lean: the single equations of a smallness test's ties and reads as
forms on the committed entries.

Definitions, statements and proofs. OnBytes/Tie/Pv/Tail/EndRows.lean gives an equation as a function
of the arrays' entries A t r c. Here J is any finite set of committed entries with addresses
(`Lay`, OnBytes/Tie/Pv/Led/LedJoint.lean), and an equation becomes a form: a coefficient for each
entry, and a target (`TWhole.Form`, Cb/G6/Led.lean).
Main names:
  `Lin g`: g is a sum of coefficients times entries, and a constant. `Lin.add`, `Lin.sub`,
    `Lin.const_mul`, `Lin.sum`, `lin_tieRow`, `lin_readRow`, `lin_rowsTail`.
  `formOfGap Y g`: the form: the coefficient of an entry is what g gains when that entry alone is 1.
  `formOfGap_gap`: for such g the form's gap on m is g at the cells that m gives.
  `rowsForm Y ρ tl funs pc`: the list of OnBytes/Tie/Pv/Tail/EndRows.lean, as forms.
  `batch_rowsForm`: the one form of that list at θ has, on m, the gap `batchOf θ` of the list of
    functions at the cells of m.
  `objectsF_forms`: if objectsF returns: no two exponents are equal; each is at most pc + the
    number of indices - 1; the total grows by the gap of that one form.
Limits: the premises of `objectsF_spread` (OnBytes/Tie/Pv/Tail/EndSpread.lean) stand, at the cells
of m. The number pc is read off the state behind objectsF. Of what the lookup's claims add to the
total nothing is said.
-/
import OnBytes.Tie.Pv.Led.LedLay
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset OnBytes.Road.Rows

variable {K : Type} [Field K]

/-! ## Functions of the entries that are sums of coefficients times entries, and a constant -/

/-- the value of a list of coefficients and places -/
def linVal (l : List (K × Nat × Nat × Nat)) (A : Nat → Nat → Nat → K) : K :=
  (l.map fun z => z.1 * A z.2.1 z.2.2.1 z.2.2.2).sum

/-- g is a sum of coefficients times entries, and a constant. -/
def Lin (g : Gap K) : Prop :=
  ∃ (l : List (K × Nat × Nat × Nat)) (c0 : K), ∀ A, g A = linVal l A + c0

theorem linVal_append (l l' : List (K × Nat × Nat × Nat)) (A : Nat → Nat → Nat → K) :
    linVal (l ++ l') A = linVal l A + linVal l' A := by
  unfold linVal
  rw [List.map_append, List.sum_append]

theorem linVal_scale (a : K) (A : Nat → Nat → Nat → K) : ∀ l : List (K × Nat × Nat × Nat),
    linVal (l.map fun z => (a * z.1, z.2)) A = a * linVal l A
  | [] => by simp [linVal]
  | z :: l => by
      have ih := linVal_scale a A l
      unfold linVal at ih ⊢
      rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
      ring

theorem Lin.const (c : K) : Lin (fun _ => c) := ⟨[], c, fun _ => by simp [linVal]⟩

theorem Lin.entry (t r c : Nat) : Lin (K := K) (fun A => A t r c) :=
  ⟨[(1, t, r, c)], 0, fun _ => by simp [linVal]⟩

theorem Lin.add {g h : Gap K} (a : Lin g) (b : Lin h) : Lin (fun A => g A + h A) := by
  obtain ⟨l, c, e⟩ := a
  obtain ⟨l', c', e'⟩ := b
  exact ⟨l ++ l', c + c', fun A => by
    show g A + h A = _
    rw [e, e', linVal_append]
    ring⟩

theorem Lin.const_mul (x : K) {g : Gap K} (a : Lin g) : Lin (fun A => x * g A) := by
  obtain ⟨l, c, e⟩ := a
  exact ⟨l.map fun z => (x * z.1, z.2), x * c, fun A => by
    show x * g A = _
    rw [e, linVal_scale]
    ring⟩

theorem Lin.sub {g h : Gap K} (a : Lin g) (b : Lin h) : Lin (fun A => g A - h A) := by
  have e : (fun A => g A - h A) = fun A => g A + -1 * h A := funext fun A => by ring
  rw [e]
  exact a.add (b.const_mul (-1))

theorem Lin.sum : ∀ {n : ℕ} (f : Fin n → Gap K), (∀ i, Lin (f i)) → Lin (fun A => ∑ i, f i A)
  | 0, _, _ => by simpa using Lin.const (K := K) 0
  | n + 1, f, h => by
      have e : (fun A => ∑ i, f i A) = fun A => f 0 A + ∑ i : Fin n, f i.succ A :=
        funext fun A => Fin.sum_univ_succ _
      rw [e]
      exact (h 0).add (Lin.sum (fun i => f i.succ) fun i => h i.succ)

theorem Lin.cell {m : ℕ} (a : Fin m → Gap K) (h : ∀ i, Lin (a i)) (i' l : ℕ) :
    Lin (fun A => Alg.lane (fun i => a i A) i' l) := by
  unfold Alg.lane
  by_cases hc : 3 * i' + l < m
  · simpa only [dif_pos hc] using h ⟨3 * i' + l, hc⟩
  · simpa only [dif_neg hc] using Lin.const (K := K) 0

theorem Lin.pack (rad : ℤ) {m : ℕ} (a : Fin m → Gap K) (h : ∀ i, Lin (a i)) (i' : ℕ) :
    Lin (fun A => Alg.pack rad (fun i => a i A) i') := by
  unfold Alg.pack
  exact ((Lin.cell a h i' 0).add ((Lin.cell a h i' 1).const_mul _)).add
    ((Lin.cell a h i' 2).const_mul _)

theorem lin_tieRow (tl : HTailF2) (mu : Nat) (i' : Fin (Alg.symRows (tl.shp.getD mu {}).m))
    (u : Fin tl.tau) : Lin (K := K) (tieRow tl mu i' u) := by
  unfold tieRow tieGap
  refine Lin.sub (Lin.pack _ (fun i A => A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i) +
    (2 : K) ^ 10 * A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i) - (2 : K) ^ 17) (fun i => ?_) i')
    (Lin.sum _ fun c => (Lin.entry _ _ _).const_mul _)
  exact ((Lin.entry _ _ _).add ((Lin.entry _ _ _).const_mul _)).sub (Lin.const _)

theorem lin_readRow (ρ : Reading K) (tl : HTailF2) (x : HFun × Nat) (u : Fin tl.tau) :
    Lin (readRow ρ tl x u) := by
  unfold readRow readGap
  refine Lin.sub (Lin.sum _ fun i => Lin.const_mul _ ?_)
    (Lin.sum _ fun c => (Lin.entry _ _ _).const_mul _)
  exact ((Lin.entry _ _ _).add ((Lin.entry _ _ _).const_mul _)).sub (Lin.const _)

theorem lin_readRows (ρ : Reading K) (tl : HTailF2) (pc : Nat) :
    ∀ (l : List (HFun × Nat)) (q : Nat), ∀ r ∈ readRowsFrom ρ tl pc q l, Lin r.2
  | [], _, r, h => absurd h (List.not_mem_nil)
  | x :: l, q, r, h => by
      rw [readRowsFrom_cons] at h
      rcases List.mem_append.1 h with h | h
      · obtain ⟨u, _, rfl⟩ := List.mem_map.1 h
        exact lin_readRow ρ tl x u
      · exact lin_readRows ρ tl pc l (q + 1) r h

theorem lin_rowsTail (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    ∀ r ∈ rowsTail ρ tl funs pc, Lin r.2 := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · obtain ⟨mu, _, h⟩ := List.mem_flatMap.1 h
    obtain ⟨i', _, h⟩ := List.mem_flatMap.1 h
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 h
    exact lin_tieRow tl mu i' u
  · exact lin_readRows ρ tl pc _ 0 r h

/-! ## Forms on the committed entries -/

variable {J : Type} [Fintype J] (Y : Lay J)

/-- the arrays in which the entry j alone is 1 -/
def unitAt (j : J) : Nat → Nat → Nat → K := fun t r c => if Y.addr j = .cell t r c then 1 else 0

/-- The form of a function of the entries. -/
def formOfGap (g : Gap K) : TWhole.Form K J :=
  ⟨fun j => g (unitAt Y j) - g fun _ _ _ => 0, -(g fun _ _ _ => 0)⟩

theorem linVal_zero (l : List (K × Nat × Nat × Nat)) : linVal l (fun _ _ _ => 0) = 0 := by
  unfold linVal
  induction l with
  | nil => rfl
  | cons z l ih => rw [List.map_cons, List.sum_cons, ih]; ring

theorem linVal_cells (m : J → K) : ∀ l : List (K × Nat × Nat × Nat),
    ∑ j, linVal l (unitAt Y j) * m j = linVal l fun t r c => Y.cellAt m t r c
  | [] => by simp [linVal]
  | z :: l => by
      have ih := linVal_cells m l
      unfold linVal at ih ⊢
      simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
      rw [ih]
      congr 1
      unfold Lay.cellAt unitAt
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      split_ifs <;> ring

/-- The form's gap on m is the function at the cells that m gives. -/
theorem formOfGap_gap {g : Gap K} (h : Lin g) (m : J → K) :
    (formOfGap Y g).gap m = g fun t r c => Y.cellAt m t r c := by
  obtain ⟨l, c0, e⟩ := h
  unfold TWhole.Form.gap formOfGap
  simp only [e, linVal_zero, zero_add, add_sub_cancel_right, sub_neg_eq_add]
  rw [linVal_cells]

/-- The list of all single equations, as forms. -/
def rowsForm (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    List (Nat × TWhole.Form K J) :=
  (rowsTail ρ tl funs pc).map fun r => (r.1, formOfGap Y r.2)

theorem batch_forms (θ : K) (m : J → K) : ∀ L : List (Nat × Gap K), (∀ r ∈ L, Lin r.2) →
    (batchAt θ (L.map fun r => (r.1, formOfGap Y r.2))).gap m =
      batchOf θ (fun t r c => Y.cellAt m t r c) L := by
  intro L hL
  rw [batchAt_gap, List.map_map]
  unfold batchOf
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  show θ ^ r.1 * (formOfGap Y r.2).gap m = _
  rw [formOfGap_gap Y (hL r hr)]

theorem batch_rowsForm (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) (θ : K)
    (m : J → K) :
    (batchAt θ (rowsForm Y ρ tl funs pc)).gap m =
      batchOf θ (fun t r c => Y.cellAt m t r c) (rowsTail ρ tl funs pc) :=
  batch_forms Y θ m _ (lin_rowsTail ρ tl funs pc)

omit [Fintype J] in
theorem fst_rowsForm (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    (rowsForm Y ρ tl funs pc).map Prod.fst = (rowsTail ρ tl funs pc).map Prod.fst := by
  unfold rowsForm
  rw [List.map_map]
  rfl

omit [Field K] in
/-- Exponents that rise are all different. -/
theorem nodup_of_rising {L : List (Nat × Gap K)} (h : Rising L) : (L.map Prod.fst).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact h.imp fun hab => Nat.ne_of_lt hab

/-- If objectsF returns: no two exponents of the list of forms are equal; each is at most pc plus
the number of indices, less 1; and behind the lookup's claims the total, in a world that reads the
four kinds of virtual rows off the cells of m, grows by the gap on m of the one form of the list at
the batching element. -/
theorem objectsF_forms (ρ : Reading K) (W : World K) (tl tl' : HTailF2) (funs : Array HFun)
    (F G : Fork) (c c' : Ctx) (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hfit : Fits tl)
    (m : J → K)
    (hV : RawRows W tl G funs (ρ.val G.theta) fun t r c => Y.cellAt m t r c) :
    ((rowsForm Y ρ tl funs G.planClaimsF).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tl funs G.planClaimsF,
      G.planClaimsF ≤ p.1 ∧ p.1 ≤ G.planClaimsF + topOf tl funs - 1) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      (Fc.LS.size = Fc.ns → c' = cc ∧ Kept Fc G ∧
        G.nClaim = Fc.nClaim + tl.NM + (readsList tl funs).length ∧
        G.total ρ W = Fc.total ρ W +
          (batchAt (ρ.val G.theta) (rowsForm Y ρ tl funs G.planClaimsF)).gap m) := by
  obtain ⟨hr, hb, g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, himp⟩ :=
    objectsF_spread ρ W tl tl' funs F G c c' h hfit _ hV
  refine ⟨by rw [fst_rowsForm]; exact nodup_of_rising hr, fun p hp => ?_,
    g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, hg, hFo, hJ, hB, fun hs => ?_⟩
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hp
    have := hb r hr'
    show G.planClaimsF ≤ r.1 ∧ r.1 ≤ G.planClaimsF + topOf tl funs - 1
    omega
  · obtain ⟨e1, hk, hn, ht⟩ := himp hs
    exact ⟨e1, hk, hn, by rw [ht, batch_rowsForm]⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.lin_rowsTail
#print axioms OnBytes.Tie.Pv.Tail.Port.formOfGap_gap
#print axioms OnBytes.Tie.Pv.Tail.Port.batch_rowsForm
#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_forms
