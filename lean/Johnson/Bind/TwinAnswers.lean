-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinAnswers.lean: the out-of-domain (OOD) answers of the committer that runs
(Johnson/Bind/Twin.lean), read in the extension field, are the answers of the library's sample map
of one row of a stored table (`recZ`, OnBytes/Slice/RecordRead.lean). Statements and proofs; general
in the shape, where a message has room for its pads (3 s ≤ l); the number of a point's coordinates
is a letter of its own (lg), which no statement here ties to the shape's cube. No hash function, no
oracle, no coding of queries is named here.

Main names (namespace `Bind.Twin`).
  `toE_eqAt_ofFn`: `eqAt` at the spelled coordinates of a point is the equality kernel at that point
    and the place's binary digits, the lowest first.
  `toE_sumFrom`, `getD_eqTable`, `toE_answerAt`: the running sum, read in the field.
  `recZ_val_at`: an answer of `recZ`, parted: the entries before the pads; the answer's three pads.
  **`answerAt_read`**: the answer i of a row, computed by `answerAt` at the spelled seed, is read as
    the answer i of `recZ` at that seed, on every vector that the row's plain entries and pads
    spell.
  `numbered_ofFn`, `range_flatMap_ofFn`: two laws on lists.
  **`answers_spelled`**: the whole list `answers` at the spelled seeds is the spelling
    (`spellAns`, OnBytes/K/IdTableSpell.lean) of the answers of `recZ`, one sample for each row.
Limits. Values in a field. No binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no correctness of extraction and no index privacy is
stated here. Nothing on any program. The one shape
at which this library takes these statements (Johnson/Bind/Cpp/AnswersFull.lean) has one answer a
row.

-/
import Johnson.Bind.Twin
import OnBytes.Slice.RecordOK
import OnBytes.Slice.SimBase
import OnBytes.Flat.EntryAccepts
import OnBytes.K.IdTableSpell
import OnBytes.K.IdSeedSpell
import Cb.Gen.OodDecPadProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
open Fmt (Ext Fld)
open OnBytes.Slice

/-- **The equality kernel.** -/
theorem toE_eqAt_ofFn : ∀ (n : ℕ) (ζ : Fin n → GE) (p : ℕ),
    toE (eqAt (List.ofFn fun t => ofE (ζ t)) p) = Alg.eqk ζ fun t => p.testBit t.val
  | 0, ζ, p => by
    unfold Alg.eqk
    rw [List.ofFn_zero, Fin.prod_univ_zero]
    exact toE_oneE
  | n + 1, ζ, p => by
    unfold Alg.eqk
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    show toE (Fld.two.mulE (if p % 2 = 1 then ofE (ζ 0) else Fld.two.subE Fld.oneE (ofE (ζ 0)))
      (eqAt (List.ofFn fun t : Fin n => ofE (ζ t.succ)) (p / 2))) = _
    rw [toE_mulE, toE_eqAt_ofFn n (fun t => ζ t.succ) (p / 2)]
    unfold Alg.eqk
    congr 1
    · by_cases h : p % 2 = 1
      · simp [h, toE_ofE, Nat.testBit_zero]
      · simp [h, toE_ofE, toE_subE, toE_oneE, Nat.testBit_zero]
    · refine Finset.prod_congr rfl fun t _ => ?_
      simp only [Fin.val_succ, Nat.testBit_succ]

/-- The running sum, read in the field. -/
theorem toE_sumFrom (eqs : Array Ext) (row : ℕ → UInt64) : ∀ (n p : ℕ) (acc : Ext),
    toE (sumFrom eqs row n p acc) =
      toE acc + ∑ k ∈ Finset.range n, toF (row (p + k)) • toE (eqs.getD (p + k) Fld.zeroE)
  | 0, p, acc => by
    show toE acc = _
    rw [Finset.sum_range_zero, add_zero]
  | n + 1, p, acc => by
    show toE (sumFrom eqs row n (p + 1)
      (Fld.two.addE acc (Fld.two.scaleE (row p) (eqs.getD p Fld.zeroE)))) = _
    rw [toE_sumFrom eqs row n (p + 1), toE_addE, toE_scaleE, Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show p + 1 + k = p + (k + 1) by omega]

/-- An entry of the table of the equality kernel. -/
theorem getD_eqTable (z : List Ext) (n q : ℕ) (hq : q < n) :
    (eqTable z n).getD q Fld.zeroE = eqAt z q := by
  have hs : q < ((Array.range n).map (eqAt z)).size := by
    rw [Array.size_map, Array.size_range]
    exact hq
  unfold eqTable
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  simp

/-- An answer, read in the field. -/
theorem toE_answerAt (S : Shape) (T : Table) (b i : ℕ) (z : List Ext) (factor : Ext) :
    toE (answerAt S T b i (eqTable z S.plain) factor) =
      (∑ k ∈ Finset.range S.plain, toF (T.entry b k) • toE (eqAt z k)) +
        toE factor * toE (T.pad b (3 * i), T.pad b (3 * i + 1), T.pad b (3 * i + 2)) := by
  unfold answerAt
  rw [toE_addE, toE_mulE, toE_sumFrom, toE_zeroE, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Nat.zero_add, getD_eqTable z S.plain k (Finset.mem_range.1 hk)]

/-- **An answer of the sample map of one row, parted**: the entries before the pads, each with the
equality kernel at the seed's point; the answer's own three pads, each with the seed's factor times
1, X, X^2. -/
theorem recZ_val_at (l lg s : ℕ) (h : 3 * s ≤ l) (ρ : (recZ l lg s).D) (v : Fin l → GE)
    (i : Fin s) :
    (recZ l lg s).val ρ v i =
      (∑ j : Fin (l - 3 * s), Alg.eqk (ρ i).1 (fun t => j.val.testBit t.val) *
        v ((entryEquiv l s h).symm (.inl j))) +
      ∑ t : Fin 3, (ρ i).2.val * readE (OnBytes.thetaE t.val) *
        v ((entryEquiv l s h).symm (.inr (i, t))) := by
  show ∑ p, (recZ l lg s).mat ρ i p * v p = _
  rw [← Equiv.sum_comp (entryEquiv l s h).symm, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [recZ_before l lg s ρ i ((entryEquiv l s h).symm (.inl j)) j.isLt]
    congr 1
    show Alg.eqk _ _ = _
    congr 1
    funext t
    exact dif_pos t.isLt
  · rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [recZ_pad l lg s ρ i ((entryEquiv l s h).symm (.inr (i, t))) i t rfl, if_pos rfl]
    · intro a _ hne
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [recZ_pad l lg s ρ i ((entryEquiv l s h).symm (.inr (a, t))) a t rfl, if_neg hne,
        zero_mul]
    · intro hh
      exact absurd (Finset.mem_univ _) hh

/-- **THE ANSWER THAT RUNS IS THE SAMPLE MAP'S.** v: any vector over the extension field that the
row's plain entries and pads spell, each word read in the base field. -/
theorem answerAt_read (S : Shape) (T : Table) (b lg : ℕ) (h : 3 * S.s ≤ S.l)
    (ρ : (recZ S.l lg S.s).D) (i : Fin S.s) (v : Fin S.l → GE)
    (hv1 : ∀ j : Fin (S.l - 3 * S.s), v ((entryEquiv S.l S.s h).symm (.inl j)) =
      algebraMap GF GE (toF (T.entry b j.val)))
    (hv2 : ∀ (a : Fin S.s) (t : Fin 3), v ((entryEquiv S.l S.s h).symm (.inr (a, t))) =
      algebraMap GF GE (toF (T.pad b (3 * a.val + t.val)))) :
    toE (answerAt S T b i.val (eqTable (List.ofFn fun t => ofE ((ρ i).1 t)) S.plain)
      (ofE (ρ i).2.val)) = (recZ S.l lg S.s).val ρ v i := by
  rw [toE_answerAt, recZ_val_at S.l lg S.s h ρ v i]
  congr 1
  · show ∑ k ∈ Finset.range (S.l - 3 * S.s), _ = _
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hv1 j, toE_eqAt_ofFn, Algebra.smul_def, mul_comm]
  · rw [toE_ofE, Fin.sum_univ_three, hv2 i 0, hv2 i 1, hv2 i 2]
    apply Code.Cubic.ext <;> simp [readE_theta, toE] <;> ring

/-! ## The lists -/

/-- The members of a list that is given by a function, numbered. -/
theorem numbered_ofFn {β : Type} : ∀ (n k : ℕ) (f : Fin n → β),
    Fmt.numbered k (List.ofFn f) = List.ofFn fun i : Fin n => (k + i.val, f i)
  | 0, k, f => by
    rw [List.ofFn_zero, List.ofFn_zero]
    rfl
  | n + 1, k, f => by
    rw [List.ofFn_succ, List.ofFn_succ]
    show (k, f 0) :: Fmt.numbered (k + 1) (List.ofFn fun i : Fin n => f i.succ) = _
    rw [numbered_ofFn n (k + 1) fun i => f i.succ]
    congr 1
    congr 1
    funext i
    rw [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

/-- R lists of s members each, one behind the other, as one list of R s members. -/
theorem range_flatMap_ofFn {α : Type} (R s : ℕ) (A : ℕ → Fin s → α)
    (hs : ∀ n : Fin (R * s), n.val % s < s) :
    (List.range R).flatMap (fun b => List.ofFn (A b)) =
      List.ofFn fun n : Fin (R * s) => A (n.val / s) ⟨n.val % s, hs n⟩ := by
  rw [List.ofFn_mul, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    congr 1
    funext j
    have h0 : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have e1 : (i * s + j.val) / s = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ h0, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have e2 : (i * s + j.val) % s = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    simp only [e1, e2]

/-- **THE ANSWERS THAT RUN, AS A LIST, ARE THE SAMPLE MAP'S, SPELLED.** u: any table of messages
over the extension field that the table's plain entries and pads spell, row by row. -/
theorem answers_spelled (S : Shape) (T : Table) (lg : ℕ) (h : 3 * S.s ≤ S.l)
    (ρ : (recZ S.l lg S.s).D) (u : (Fin S.v → Bool) × Fin S.l → GE)
    (hu1 : ∀ (b : ℕ) (j : Fin (S.l - 3 * S.s)), b < 2 ^ S.v →
      u (vtx S.v b, (entryEquiv S.l S.s h).symm (.inl j)) =
        algebraMap GF GE (toF (T.entry b j.val)))
    (hu2 : ∀ (b : ℕ) (a : Fin S.s) (t : Fin 3), b < 2 ^ S.v →
      u (vtx S.v b, (entryEquiv S.l S.s h).symm (.inr (a, t))) =
        algebraMap GF GE (toF (T.pad b (3 * a.val + t.val)))) :
    (OnBytes.K.IdTable.spellAns S.v S.s
        (((recZ S.l lg S.s).rows (Fin S.v → Bool)).val ρ u)).map OnBytes.E.triple =
      answers S T ((OnBytes.K.IdTable.spellSeedL lg S.s ρ).map fun y =>
        (y.1.map OnBytes.E.triple, y.2.triple)) := by
  have hseeds : ((OnBytes.K.IdTable.spellSeedL lg S.s ρ).map fun y =>
      (y.1.map OnBytes.E.triple, y.2.triple)) =
      List.ofFn fun i : Fin S.s => (List.ofFn fun t : Fin lg => ofE ((ρ i).1 t),
        ofE (ρ i).2.val) := by
    unfold OnBytes.K.IdTable.spellSeedL OnBytes.K.IdTable.spellSeed1
    rw [List.map_ofFn]
    congr 1
    funext i
    show ((List.ofFn fun t : Fin lg => writeE ((ρ i).1 t)).map OnBytes.E.triple,
      (writeE (ρ i).2.val).triple) = _
    rw [List.map_ofFn]
    rfl
  unfold answers
  rw [hseeds, List.map_ofFn, numbered_ofFn]
  simp only [List.map_ofFn]
  show _ = (List.range (2 ^ S.v)).flatMap fun b => List.ofFn fun i : Fin S.s =>
    answerAt S T b (0 + i.val) (eqTable (List.ofFn fun t : Fin lg => ofE ((ρ i).1 t)) S.plain)
      (ofE (ρ i).2.val)
  rw [range_flatMap_ofFn (2 ^ S.v) S.s _ fun n => Nat.mod_lt _ (pos_of_place n)]
  unfold OnBytes.K.IdTable.spellAns
  rw [List.map_ofFn]
  congr 1
  funext n
  have hb : n.val / S.s < 2 ^ S.v :=
    Nat.div_lt_of_lt_mul (lt_of_lt_of_eq n.isLt (Nat.mul_comm _ _))
  show ofE (((recZ S.l lg S.s).rows (Fin S.v → Bool)).val ρ u
    (vtx S.v (n.val / S.s), ⟨n.val % S.s, _⟩)) = _
  rw [Cb.ood_val_rows_same, Nat.zero_add,
    ← answerAt_read S T (n.val / S.s) lg h ρ ⟨n.val % S.s, Nat.mod_lt _ (pos_of_place n)⟩
      (fun j => u (vtx S.v (n.val / S.s), j)) (fun j => hu1 _ j hb) (fun a t => hu2 _ a t hb)]
  exact OnBytes.Flat.ofE_toE _ (okE_addE _ _)

end Bind.Twin

#print axioms Bind.Twin.numbered_ofFn
#print axioms Bind.Twin.range_flatMap_ofFn
#print axioms Bind.Twin.answers_spelled
#print axioms Bind.Twin.toE_eqAt_ofFn
#print axioms Bind.Twin.toE_sumFrom
#print axioms Bind.Twin.getD_eqTable
#print axioms Bind.Twin.toE_answerAt
#print axioms Bind.Twin.recZ_val_at
#print axioms Bind.Twin.answerAt_read
