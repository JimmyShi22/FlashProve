-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowB2.lean: what one placed panel of the verifier adds to the B side of the
batched sumcheck's summand at its end values is what the pieces of its panel of the library add to
the typed second sum, from the panel's fields; and so the typed second sum is BsAt.

Main names:
  `BFields`: what is asked of a pair (b, pn): the bits; the panel's number; that the verifier's test
    of that number has passed; whether the panel has the selector; that b has a first weight claim,
    number v0, exactly if pn is a weight panel; its rows; the rows' public factors.
  `f2_mem_right`: a tool on lists related member by member.
  `pairB`: the fourth number of dEnd (Johnson/Road/FormsKeysEnd.lean) at b is the sum over the
    pieces of pn of the typed coefficient times the end value.
  `bs_of_fields`: the typed second sum is BsAt (by bs_typed, Johnson/Road/K4/StackRowB.lean).
Limits. BFields of every pair of the placed list and the library's list, the numbers v0, that the
typed point reads as the challenges turned round, and that the end values by name are the values by
number, are premises. Identities on public numbers and given values: nothing on a world, on a draw,
on soundness or on hiding.


-/
import Johnson.Road.K4.StackRowB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World eqIndexOK)
open OnBytes.Model.Layer (SBlk Lay)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (IB cntB InnPar0 kS nP wrow wid_eq)
open Blocks (eqN)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {ρ : Reading K} (P : InnPar0 K) (st : P.St)

/-- What is asked of a placed panel b and its panel pn of the library. -/
structure BFields (ρ : Reading K) (rs : Array E) (lam : ℕ) (b : SBlk) (pn : Pan) (v0 : ℕ) :
    Prop where
  bw : b.w = pn.wid P.D
  bwy : b.wy = pn.wcol P.D
  off : b.off / 2 ^ b.w = nP P.D pn
  ok : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true
  tri : b.tri = pn.three
  /-- a weight panel has a first weight claim -/
  v0s : pn.weight = true → b.v0 = some v0
  /-- a panel without weights has none, and no never-sent vector -/
  v0n : pn.weight = false → b.v0 = none ∧ b.virt = none
  ni : pn.three = false → b.ni = pn.nr P.D
  /-- the rows' public factors: with a never-sent vector on the A side they stand on the B side -/
  facV : pn.three = false → ∀ k, b.virt = some k → ∀ i, i < pn.nr P.D →
    ρ.val b.ec * wtK ρ b i = P.κB st pn i
  facN : pn.three = false → b.virt = none → ∀ i, i < pn.nr P.D → P.κB st pn i = 1

variable {P st}

omit scl in
/-- In lists that are related member by member, each pair's second member is a member of the second
list. -/
theorem f2_mem_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → List.Forall₂ (fun a b => b ∈ l' ∧ R a b) l l'
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons h1 h2 => List.Forall₂.cons ⟨List.mem_cons_self, h1⟩
      ((f2_mem_right h2).imp fun _ _ k => ⟨List.mem_cons_of_mem _ k.1, k.2⟩)

/-- **One pair.** vN: the end values of the pieces of pn, by number. -/
theorem pairB {rs : Array E} {lam : ℕ} {b : SBlk} {pn : Pan} {v0 : ℕ}
    (Fd : BFields P st ρ rs lam b pn v0) (hl : lam ≤ rs.size) (hk : lam = kS P.D)
    (z : Fin (kS P.D) → K) (hz : ∀ j, j < kS P.D → Blocks.nat z j = zR ρ rs lam j)
    (hp : pn ∈ pans P.D) (W : World K) (y : Lay) (om : Array E) (h1 vv vN : ℕ → K)
    (hv : ∀ i, i < cntB P.D pn → vv (v0 + i) = vN i) :
    (dEnd ρ W y rs lam om h1 vv b).2.2.2.1 =
      ∑ i : Fin (cntB P.D pn), P.sideB.side.c (.inr ⟨⟨pn, hp⟩, i⟩) st z * vN i := by
  subst hk
  have hwl : pn.wid P.D ≤ kS P.D := by
    rw [Cb.Pv.Lay.At.kS_eq]
    exact Cb.Pv.Lay.At.wid_le P.D hp
  have cz : ∀ m c, m ≤ kS P.D →
      eqN m 0 (zR ρ rs (kS P.D)) c = eqN m 0 (Blocks.nat z) c := fun m c hm =>
    eqN_congr' _ _ (fun j hj => by
      rw [Nat.zero_add]
      exact (hz j (Nat.lt_of_lt_of_le hj hm)).symm) c
  cases hw : pn.weight with
  | false =>
    obtain ⟨e0, ek⟩ := Fd.v0n hw
    have hc : cntB P.D pn = 0 := by
      unfold cntB
      rw [hw]
      rfl
    haveI : IsEmpty (Fin (cntB P.D pn)) := by
      rw [hc]
      infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    unfold dEnd
    rw [e0, ek]
    cases b.tri <;> rfl
  | true =>
    have e0 := Fd.v0s hw
    cases h3 : pn.three with
    | true =>
      have hc : cntB P.D pn = 1 := by
        unfold cntB
        rw [hw, h3]
        rfl
      have et : b.tri = true := Fd.tri.trans h3
      rw [Finset.sum_congr rfl fun i _ => by rw [cB_three P st z ⟨pn, hp⟩ h3 i],
        Fin.sum_univ_eq_sum_range
          (fun i => eqN (kS P.D - pn.wid P.D) 0 (Blocks.nat z) (nP P.D pn) * vN i) (cntB P.D pn),
        hc, sum_range_one, ← hv 0 (by omega), Nat.add_zero, ← cz _ _ (Nat.sub_le _ _),
        ← Fd.bw, ← Fd.off, ← geo_sb ρ hl Fd.ok]
      unfold dEnd
      rw [et, e0]
      cases b.virt <;> rfl
    | false =>
      have hc : cntB P.D pn = pn.nr P.D := by
        unfold cntB
        rw [hw, h3]
        rfl
      have et : b.tri = false := Fd.tri.trans h3
      have hwy : b.wy ≤ b.w := by
        rw [Fd.bw, Fd.bwy, wid_eq]
        exact Nat.le_add_left _ _
      have hwr : b.w - b.wy = wrow P.D pn := by
        rw [Fd.bw, Fd.bwy, wid_eq, Nat.add_sub_cancel]
      have hrow : ∀ i, i < pn.nr P.D → i < 2 ^ (b.w - b.wy) := fun i hi => by
        rw [hwr]
        exact Nat.lt_of_lt_of_le hi (Nat.le_pow_clog (by decide) _)
      have geo : ∀ i, i < pn.nr P.D → sbK ρ rs (kS P.D) b * eiK ρ rs b i =
          eqN (kS P.D - pn.wcol P.D) 0 (Blocks.nat z) (nP P.D pn * 2 ^ wrow P.D pn + i) :=
        fun i hi => by
          rw [geo_sbei ρ hl Fd.ok hwy (by rw [Fd.bw]; exact hwl) (hrow i hi), Fd.off, hwr,
            Fd.bwy, cz _ _ (Nat.sub_le _ _)]
      rw [Finset.sum_congr rfl fun i _ => by rw [cB_two P st z ⟨pn, hp⟩ h3 i],
        Fin.sum_univ_eq_sum_range (fun i => P.κB st pn i *
          eqN (kS P.D - pn.wcol P.D) 0 (Blocks.nat z) (nP P.D pn * 2 ^ wrow P.D pn + i) * vN i)
          (cntB P.D pn), hc]
      unfold dEnd
      rw [et, e0]
      cases hvk : b.virt with
      | some k =>
        show ∑ i ∈ range b.ni, sbK ρ rs (kS P.D) b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
          vv (v0 + i) = _
        rw [Fd.ni h3]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [← Fd.facV h3 k hvk i hi', ← geo i hi', hv i (by rw [hc]; exact hi')]
        ring
      | none =>
        show ∑ i ∈ range b.ni, sbK ρ rs (kS P.D) b * eiK ρ rs b i * vv (v0 + i) = _
        rw [Fd.ni h3]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [Fd.facN h3 hvk i hi', ← geo i hi', hv i (by rw [hc]; exact hi'), one_mul]

/-- **The typed second sum is BsAt.** v0Of: the number of a panel's first weight claim; v: the end
values by the pieces' names. -/
theorem bs_of_fields {rs : Array E} {lam : ℕ} {bl : List SBlk} (v0Of : Pan → ℕ)
    (F2 : List.Forall₂ (fun b pn => BFields P st ρ rs lam b pn (v0Of pn)) bl (pans P.D))
    (hl : lam ≤ rs.size) (hk : lam = kS P.D) (z : Fin (kS P.D) → K)
    (hz : ∀ j, j < kS P.D → Blocks.nat z j = zR ρ rs lam j) (W : World K) (y : Lay)
    (om : Array E) (h1 vv : ℕ → K) (v : IB P.D → K)
    (hv : ∀ (p : {p : Pan // p ∈ pans P.D}) (i : Fin (cntB P.D p.1)),
      v (.inr ⟨p, i⟩) = vv (v0Of p.1 + i)) :
    ∑ j : IB P.D, P.sideB.side.c j st z * v j =
      BsAt ρ W y rs lam om h1 vv (v (.inl ())) bl := by
  refine bs_typed P st z W y rs lam om h1 vv v
    (fun pn => if hp : pn ∈ pans P.D then ∑ i : Fin (cntB P.D pn),
      P.sideB.side.c (.inr ⟨⟨pn, hp⟩, i⟩) st z * vv (v0Of pn + i) else 0) (fun p => ?_) ?_
  · beta_reduce
    rw [dif_pos p.2]
    exact Finset.sum_congr rfl fun i _ => by rw [hv p i]
  · refine (f2_mem_right F2).imp fun b pn k => ?_
    beta_reduce
    rw [dif_pos k.1]
    exact pairB k.2 hl hk z hz k.1 W y om h1 vv (fun i => vv (v0Of pn + i)) fun _ _ => rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pairB
#print axioms OnBytes.Road.K4.bs_of_fields
