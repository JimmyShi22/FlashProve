-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TableStrongGuard.lean: the number r of E2E/TableStrong.lean cannot be raised: at r + 1 columns
the law of a committed table's columns does hang on the rows' messages. Statements and proofs.

What is shown.
  **`not_strong_succ`**: for a code of at most 2^32 positions that has at least r + 1 positions and
    at least one entry in a row's message: the configuration with the format's encoder
    (`codingHonest`) has NOT the library's property `ConfigurationWithOutOfDomainSample.Strong` at r + 1.
  `not_strong_full`: so at the full size's code: not at 44,040,192.

How. Take r + 1 positions, the table of messages 0 and the table whose rows have the entry 1 at
place 0. If the two laws were one, the columns of the second table at encoding randomness 0 would
also be columns of the first at some encoding randomness ρ. In row number 0 that says: the
polynomial with the coefficients ρ, of degree below r, agrees with X^r at r + 1 distinct points. A
polynomial of degree r that is not 0 has at most r zeros (the library's `Code.RS.card_zeros_lt`).

Why it is here. A bound that holds for a free letter says little. This shows that the r in
`strong_codingHonest` is the code's own number and is sharp.

Limits.
- It says that some two tables of messages have different laws at some r + 1 columns. (The proof
  takes an arbitrary set of that size.) It states no size of the difference.
- It is on `Strong`, the property of the encoder at FIXED messages, pads included. That
  `ConfigurationWithOutOfDomainSample.Hides`, the encoder's joint clause of E2E/TableHides.lean on matrices, fails at r + 1 is
  not shown HERE: there the pads are sampled too, and the two tables of messages here need not hold
  matrices. It is shown in E2E/TableHidesGuard.lean (`not_hides_succ`, `differ_at`: at some OOD
  seed, at two matrices, at every set of r + 1 positions; no size of the difference is stated).

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.TableStrong
import OnBytes.Slice.FullRecLink

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Table
open Iop Prob Hiop
open OnBytes.Flat (relationsAndEncodingOfClaims Coding codingHonest rowWords tailWords)
open OnBytes.Slice (Sz GF GE toF ofF ptOf honestTab frS frZ)

variable (S : Sz)

/-- Read in the field, word j of the message of row number a is the first coordinate of the entry j
at the vertex of a's bits. -/
theorem toF_rowWords (m : S.ix.Row × S.En → GE) (a : ℕ) (j : Fin S.P.T.l) :
    toF ((rowWords S m a).getD j.val 0) = (m (fun t => a.testBit t.val, j)).c0 := by
  have hl : j.val < (List.ofFn fun j : Fin S.P.T.l =>
      ofF (m (fun t : Fin S.P.v => a.testBit t.val, j)).c0).length := by
    rw [List.length_ofFn]
    exact j.isLt
  show toF ((List.ofFn fun j : Fin S.P.T.l =>
    ofF (m (fun t : Fin S.P.v => a.testBit t.val, j)).c0).getD j.val 0) = _
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
  exact OnBytes.Slice.toF_ofF _

/-- The message's share, as a sum over the entries. -/
theorem share_eq (m : S.ix.Row × S.En → GE) (a : Fin (2 ^ S.P.v)) (x : S.Pos) :
    share S m a x = ∑ j : Fin S.P.T.l,
      ptOf S.P.T.a x ^ (S.P.T.r + j.val) * (m (fun t => a.val.testBit t.val, j)).c0 := by
  unfold share
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [toF_rowWords S m a.val j]

/-- Two columns of field values that are one stored column have the same field values. -/
theorem colOf_inj (x : S.Pos) (c c' : Fin (2 ^ S.P.v) → GF) (h : colOf S x c = colOf S x c') :
    c = c' := by
  have h2 : (List.ofFn fun a => ofF (c a)) = List.ofFn fun a => ofF (c' a) :=
    congrArg Prod.snd h
  funext a
  have h3 : ofF (c a) = ofF (c' a) := congrFun (List.ofFn_injective h2) a
  rw [← OnBytes.Slice.toF_ofF (c a), h3, OnBytes.Slice.toF_ofF]

variable (Z : Cb.Ood.Sample GE S.En) (cut : ℕ) {X : Type} (A : (S.toDecR Z cut).Claims X)
  (Pad : Type) [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64)

/-- **At r + 1 columns the encoder is not strong.** -/
theorem not_strong_succ (ha : S.P.T.a ≤ 32) (hn : S.P.T.r + 1 ≤ 2 ^ S.P.T.a) (hl : 0 < S.P.T.l) :
    ¬ (OnBytes.Slice.DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A (codingHonest S Z cut A Pad holdW))).Strong
      (S.P.T.r + 1) := by
  classical
  intro h
  obtain ⟨Q, -, hQ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset S.Pos))
    (n := S.P.T.r + 1) (by rw [Finset.card_univ, Fintype.card_fin]; exact hn)
  -- the two tables of messages
  let m₀ : S.ix.Row × S.En → GE := fun _ => 0
  let m₁ : S.ix.Row × S.En → GE := fun n => if n.2.val = 0 then 1 else 0
  have e : (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
        (fun ρ => fun p : Q => honestTab S (rowWords S m₁) (tailWords S ρ) p) =
      (unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
        (fun ρ => fun p : Q => honestTab S (rowWords S m₀) (tailWords S ρ) p) :=
    h Q hQ.le m₁ m₀
  -- the second table's columns at encoding randomness 0 lie in the first law's support
  have hmem : (fun p : Q => honestTab S (rowWords S m₁) (tailWords S 0) p) ∈
      ((unif (Fin (2 ^ S.P.v) → Fin S.P.T.r → GF)).map
        (fun ρ => fun p : Q => honestTab S (rowWords S m₀) (tailWords S ρ) p)).support := by
    rw [← e]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨0, PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨ρ, -, hρ⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
  -- row number 0
  let a₀ : Fin (2 ^ S.P.v) := ⟨0, Nat.two_pow_pos _⟩
  have hrow : ∀ p : Q, Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) (ρ a₀) p =
      ptOf S.P.T.a p ^ S.P.T.r := by
    intro p
    have h1 := congrFun hρ p
    rw [honestTab_col S m₀ ρ p, honestTab_col S m₁ 0 p] at h1
    have h2 := congrFun (colOf_inj S p _ _ h1) a₀
    have s0 : share S m₀ a₀ p = 0 := by
      rw [share_eq]
      exact Finset.sum_eq_zero fun j _ => mul_zero _
    have s1 : share S m₁ a₀ p = ptOf S.P.T.a p ^ S.P.T.r := by
      rw [share_eq, Finset.sum_eq_single (⟨0, hl⟩ : Fin S.P.T.l)]
      · show ptOf S.P.T.a p ^ (S.P.T.r + 0) * (if (0 : ℕ) = 0 then (1 : GE) else 0).c0 = _
        rw [if_pos rfl, Nat.add_zero]
        exact mul_one _
      · intro j _ hj
        have hj' : ¬ j.val = 0 := fun h0 => hj (Fin.ext h0)
        show ptOf S.P.T.a p ^ (S.P.T.r + j.val) * (if j.val = 0 then (1 : GE) else 0).c0 = 0
        rw [if_neg hj']
        exact mul_zero _
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    have g0 : Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ))
        ((0 : Fin (2 ^ S.P.v) → Fin S.P.T.r → GF) a₀) p = 0 := by
      show Code.RS.gen (ptOf S.P.T.a) (fun t : Fin S.P.T.r => (t : ℕ)) 0 p = 0
      rw [map_zero]
      rfl
    rw [s0, s1, g0, zero_add, add_zero] at h2
    exact h2
  -- the polynomial with the coefficients ρ a₀ and -1 vanishes on Q
  let v : Fin (S.P.T.r + 1) → GF := Fin.snoc (ρ a₀) (-1)
  have hv : v ≠ 0 := by
    intro h0
    have h1 : v (Fin.last S.P.T.r) = 0 := congrFun h0 _
    rw [show v (Fin.last S.P.T.r) = -1 from Fin.snoc_last _ _] at h1
    exact one_ne_zero (neg_eq_zero.1 h1)
  have hz : ∀ p : Q, Code.RS.gen (fun q : Q => ptOf S.P.T.a q)
      (fun t : Fin (S.P.T.r + 1) => (t : ℕ)) v p = 0 := by
    intro p
    rw [Code.RS.gen_apply, Fin.sum_univ_castSucc]
    have h1 := hrow p
    rw [Code.RS.gen_apply] at h1
    show (∑ i : Fin S.P.T.r, v i.castSucc * ptOf S.P.T.a p ^ (i : ℕ)) +
      v (Fin.last S.P.T.r) * ptOf S.P.T.a p ^ S.P.T.r = 0
    rw [show v (Fin.last S.P.T.r) = -1 from Fin.snoc_last _ _]
    simp only [show ∀ i : Fin S.P.T.r, v i.castSucc = ρ a₀ i from fun i => Fin.snoc_castSucc _ _ i]
    rw [h1]
    ring
  have hx : Function.Injective fun q : Q => ptOf S.P.T.a q :=
    fun q q' hq => Subtype.ext (OnBytes.Slice.ptOf_inj S.P.T.a ha hq)
  have hc := Code.RS.card_zeros_lt hx (ex := fun t : Fin (S.P.T.r + 1) => (t : ℕ))
    Fin.val_injective (k := S.P.T.r + 1) (fun i => i.isLt) hv
  have hall : Nat.card {j : Q // Code.RS.gen (fun q : Q => ptOf S.P.T.a q)
      (fun t : Fin (S.P.T.r + 1) => (t : ℕ)) v j = 0} = S.P.T.r + 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hz), Nat.card_eq_fintype_card, Fintype.card_coe, hQ]
  omega

/-- **At the full size's code**: not at 44,040,192 columns. -/
theorem not_strong_full {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (Pad : Type)
    [Fintype Pad] [Nonempty Pad] (holdW : A.Mat → Pad → ℕ → List UInt64) :
    ¬ (OnBytes.Slice.DecR.configurationOfStoredTable A
      (relationsAndEncodingOfClaims A (codingHonest frS frZ 402653181 A Pad holdW))).Strong 44040192 :=
  not_strong_succ frS frZ 402653181 A Pad holdW (Nat.le_refl 32)
    (by show 44040191 + 1 ≤ 2 ^ 32; norm_num) (by show 0 < 402653184; norm_num)

end AtPublicFiles.Table

#print axioms AtPublicFiles.Table.not_strong_succ
#print axioms AtPublicFiles.Table.not_strong_full
