-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TiedAtK10.lean: K10On's CLAUSE "tied": A TERM FOR THE NUMBERING num OF
K10's LAW, AND RowsTied (Johnson/Desc/First/Close/Law/AtPieceAll.lean) AT THAT TERM FROM FACTS A
ROW. A definition, statements and proofs. General in the signature and the arrangement.

Why. RowsTied speaks of rows[num ν] with rows := runRows T G = the plain rows ++ each member's
sample rows, in the members' order ++ the generator rows (OnBytes/Slice/BlkBegin.lean). At a free
num it is false. So num must follow that order.

  numBy nP nG es   THE TERM: the claim's rows are B := Fin nP ⊕ Fin nG (the plain rows; the
                   generator rows); es lists the members' samples in the members' order: a plain row
                   b ↦ b · the sample es[j] ↦ nP + j · a generator row g ↦ nP + es.length + g
  numBy_plain | _sample | _gen its three values
  runRows_toList   runRows as three lists
  row_at_plain | _sample | _gen what stands at these numbers in runRows, where the members are es'
                   messages (noOf) and each has just one sample row (rOf)
  rowsTied_of      **RowsTied at numBy**, from: the counts nP, nG · the members are es' messages ·
                   one sample row a member · at a row of the claim: the target and rowVec of the row
                   at its number · at a sample: the answer is its row's target · pS at the seed is
                   its row's rowVec · NamesOne · SampleFits

Limits. A NUMBERING AND BOOK-KEEPING: the facts a row are premises: the answer and NamesOne are
sample_member's (SampleAtK10.lean) under K1.SeedIs and K1.Tie; pS HAS A TERM, NOT HERE: pSseed
(DrawnSeed.lean), laid in at tied_laid_in (TiedLaidIn.lean) under hG, hl and TiedOwes, of which no
field is shown of any state there; SampleFits is shown of nothing. No
soundness statement.

-/
import Johnson.Desc.First.Close.Law.AtPieceAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Cb.Pv Johnson.Top.H KObj
open VerifiableInference.Desc.First.Close (RowsTied NamesOne SampleFits rowVec SlotNames)

section Num
variable {X : Type} [DecidableEq X]

/-- **THE NUMBERING**: plain rows, the members' samples in the order of es, generator rows. -/
def numBy (nP nG : ℕ) (es : List X) (nd : es.Nodup) (hall : ∀ x, x ∈ es) :
    ((Fin nP ⊕ Fin nG) ⊕ X) ≃ Fin (nP + es.length + nG) :=
  ((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
    (Equiv.sumAssoc _ _ _).symm)).trans
    (((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _)
      (nd.getEquivOfForallMemList es hall).symm) (Equiv.refl _)).trans
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl _))).trans finSumFinEquiv)

theorem numBy_plain (nP nG : ℕ) (es : List X) (nd : es.Nodup) (hall : ∀ x, x ∈ es) (b : Fin nP) :
    (numBy nP nG es nd hall (.inl (.inl b))).val = b.val := by
  simp [numBy]

theorem numBy_sample (nP nG : ℕ) (es : List X) (nd : es.Nodup) (hall : ∀ x, x ∈ es) (x : X) :
    (numBy nP nG es nd hall (.inr x)).val = nP + es.idxOf x := by
  simp [numBy, List.Nodup.getEquivOfForallMemList]

theorem numBy_gen (nP nG : ℕ) (es : List X) (nd : es.Nodup) (hall : ∀ x, x ∈ es) (g : Fin nG) :
    (numBy nP nG es nd hall (.inl (.inr g))).val = nP + es.length + g.val := by
  simp [numBy]

end Num

section Rows

theorem foldl_append_toList {α β : Type} (f : α → Array β) : ∀ (l : List α) (acc : Array β),
    (l.foldl (fun a o => a ++ f o) acc).toList = acc.toList ++ l.flatMap fun o => (f o).toList
  | [], acc => by simp
  | o :: l, acc => by
    rw [List.foldl_cons, foldl_append_toList f l, Array.toList_append, List.flatMap_cons,
      List.append_assoc]

/-- runRows as three lists. -/
theorem runRows_toList (T : Statement) (G : Group) :
    (runRows T G).toList = (G.rows.filter (·.kind == .plain)).toList ++
      (G.members.toList.flatMap fun o =>
        (((T.oracles[o]?).map (·.sampleRows)).getD #[]).toList) ++
      (G.rows.filter (·.kind == .generator)).toList := by
  unfold runRows
  rw [Array.toList_append, Array.toList_append, ← Array.foldl_toList, foldl_append_toList]
  simp

variable {X : Type} [DecidableEq X] (T : Statement) (G : Group) (nP : ℕ)
  (hP : (G.rows.filter (·.kind == .plain)).toList.length = nP) (es : List X) (noOf : X → ℕ)
  (hmem : G.members.toList = es.map noOf) (rOf : X → OnBytes.Row)
  (hone : ∀ x ∈ es, ((T.oracles[noOf x]?).map (·.sampleRows)).getD #[] = #[rOf x])

include hmem hone in
/-- The middle list is the samples' rows, in es' order. -/
theorem samples_are : (G.members.toList.flatMap fun o =>
    (((T.oracles[o]?).map (·.sampleRows)).getD #[]).toList) = es.map rOf := by
  rw [hmem, List.flatMap_map]
  clear hmem
  induction es with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, hone x List.mem_cons_self, List.map_cons,
      ih fun y hy => hone y (List.mem_cons_of_mem _ hy)]
    rfl

include hP hmem hone in
/-- What stands at a sample's number. -/
theorem row_at_sample (x : X) (hx : x ∈ es) :
    (runRows T G).toList[nP + es.idxOf x]? = some (rOf x) := by
  rw [runRows_toList, samples_are T G es noOf hmem rOf hone, List.append_assoc,
    List.getElem?_append_right (by omega), hP, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [List.length_map]; exact List.idxOf_lt_length_iff.2 hx),
    List.getElem?_map, List.getElem?_idxOf hx]
  rfl

end Rows

section Tied
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R)
  (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)

open Classical in
/-- **RowsTied AT THE NUMBERING numBy.** -/
theorem rowsTied_of (T : Statement) (G : Group) (T' : Statement) (lay : GroupLayout) (nP nG : ℕ)
    (hP : (G.rows.filter (·.kind == .plain)).toList.length = nP)
    (hG : (G.rows.filter (·.kind == .generator)).toList.length = nG)
    (es : List (Σ a : R.G.A, (S.om a.1).Z.S)) (nd : es.Nodup) (hall : ∀ x, x ∈ es)
    (noOf : (Σ a : R.G.A, (S.om a.1).Z.S) → ℕ) (hmem : G.members.toList = es.map noOf)
    (rOf : (Σ a : R.G.A, (S.om a.1).Z.S) → OnBytes.Row)
    (hone : ∀ x ∈ es, ((T.oracles[noOf x]?).map (·.sampleRows)).getD #[] = #[rOf x])
    (x : ((Fin nP ⊕ Fin nG) → GE) × ((Fin nP ⊕ Fin nG) → R.Sh.Cin.J → GE)) (σ : S.Smp)
    (hB : ∀ (hn : (runRows T G).toList.length = nP + es.length + nG) b,
      x.1 b = readE ((runRows T G).toList[(numBy nP nG es nd hall (.inl b)).val]'(
        Nat.lt_of_lt_of_eq (numBy nP nG es nd hall (.inl b)).isLt hn.symm)).target ∧
      x.2 b = rowVec N T' lay ((runRows T G).toList[(numBy nP nG es nd hall (.inl b)).val]'(
        Nat.lt_of_lt_of_eq (numBy nP nG es nd hall (.inl b)).isLt hn.symm)))
    (hS : ∀ as, (σ as.1.1).2 as.2 = readE (rOf as).target ∧
      pS as (σ as.1.1).1 = rowVec N T' lay (rOf as) ∧
      ∃ o, NamesOne (rOf as) o ∧ SampleFits N T' lay (rOf as) o as.1
        (Slf.atMem (Jf := fun a : R.G.A => (S.om a.1).C.J) as.1
          ((S.om as.1.1).row as.2) (σ as.1.1).1)) :
    RowsTied R (nP + es.length + nG) (numBy nP nG es nd hall) N pS x σ T' lay
      (runRows T G).toList := by
  have hn : (runRows T G).toList.length = nP + es.length + nG := by
    rw [runRows_toList, samples_are T G es noOf hmem rOf hone, List.length_append,
      List.length_append, List.length_map, hP, hG]
  refine ⟨hn, hB hn, fun as => ?_⟩
  have hr : (runRows T G).toList[(numBy nP nG es nd hall (.inr as)).val]'(
      Nat.lt_of_lt_of_eq (numBy nP nG es nd hall (.inr as)).isLt hn.symm) = rOf as := by
    have h1 := row_at_sample T G nP hP es noOf hmem rOf hone as (hall as)
    rw [← numBy_sample nP nG es nd hall as] at h1
    exact (List.getElem?_eq_some_iff.1 h1).2
  rw [hr]
  exact hS as

end Tied

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.numBy_plain
#print axioms VerifiableInference.Desc.LinkJoin.numBy_sample
#print axioms VerifiableInference.Desc.LinkJoin.numBy_gen
#print axioms VerifiableInference.Desc.LinkJoin.runRows_toList
#print axioms VerifiableInference.Desc.LinkJoin.row_at_sample
#print axioms VerifiableInference.Desc.LinkJoin.rowsTied_of
