-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/DeclHalfOf.lean (it imports
Johnson/Desc/AtSeats/ToldHalves.lean): THE DECLARED HALF OF THE
FIELD told, AND THE COUNT's TIE, EACH FROM WHAT A PLACE's OWN LAWS GIVE. General: no place, no size.

  flatten_at       entry number n of the k-th of a list of lists stands in the flattened list behind
                   the lengths of the lists in front.
  oracleAt_firstTold   WHAT THE IOP AS WRITTEN IN LEAN TELLS OF THE TREE NUMBER "the trees told in
                   front of the first chain's sub-protocol k, and n more" IS THAT SUB-PROTOCOL's OWN
                   DECLARATION NUMBER n (FileDescription.oracleAt, Johnson/Desc/Msg.lean). (Its kin for the
                   shared chain: Second.Seam.oracleAt_told, Johnson/Second/Seam/SeatOfTold.lean.)
  declHalf_of      DeclHalf, from: the sub-protocol's declared list decl; base = the trees told in
                   front; a reading q of decl's depths and widths (a place's law gives it: the
                   layout's); the table has q n at base + n (a closed test).
  countTie_of      CountTie, from the trees that the data send in front of the two rounds and behind
                   them.

What is not claimed. Any premise at any place. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.ToldHalves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (FileDescription oraclesOf)

theorem flatten_at {α : Type} : ∀ (L : List (List α)) (k n : ℕ) (l : List α), L[k]? = some l →
    n < l.length → L.flatten[((L.take k).map List.length).sum + n]? = l[n]?
  | [], k, n, l, h, _ => by simp at h
  | x :: L, 0, n, l, h, hn => by
    obtain rfl : x = l := by simpa using h
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
    exact List.getElem?_append_left hn
  | x :: L, k + 1, n, l, h, hn => by
    have h' : L[k]? = some l := by simpa using h
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
    rw [List.getElem?_append_right (by omega)]
    have e : x.length + ((L.take k).map List.length).sum + n - x.length =
        ((L.take k).map List.length).sum + n := by omega
    rw [e]
    exact flatten_at L k n l h' hn

/-- **What is told of a tree of the first chain, by the sub-protocol that declares it.** -/
theorem oracleAt_firstTold {Xi : Type} (F : FileDescription Xi) (k n : ℕ)
    (decl : List VerifiableInference.Desc.Oracle)
    (h : (F.first.blocksInOrder.map fun b => b.oracles.flatMap id)[k]? = some decl) (hn : n < decl.length) :
    F.oracleAt ((((F.first.blocksInOrder.map fun b => b.oracles.flatMap id).take k).map
      List.length).sum + n) = decl[n]? := by
  have key := flatten_at _ k n decl h hn
  have e1 : oraclesOf F.first.blocksInOrder = (F.first.blocksInOrder.map fun b => b.oracles.flatMap id).flatten := by
    unfold oraclesOf
    rw [List.flatMap_def]
  have hlt : (((F.first.blocksInOrder.map fun b => b.oracles.flatMap id).take k).map List.length).sum + n <
      (oraclesOf F.first.blocksInOrder).length := by
    rw [e1]
    have : decl[n]? = some decl[n] := List.getElem?_eq_getElem hn
    rw [this] at key
    exact (List.getElem?_eq_some_iff.1 key).1
  unfold FileDescription.oracleAt
  rw [List.getElem?_append_left (by rw [List.length_append]; omega),
    List.getElem?_append_left hlt, e1]
  exact key

/-- **The declared half.** -/
theorem declHalf_of {Xi : Type} (F : FileDescription Xi) (k : ℕ)
    (decl : List VerifiableInference.Desc.Oracle)
    (h : (F.first.blocksInOrder.map fun b => b.oracles.flatMap id)[k]? = some decl) (base : ℕ)
    (hb : base = (((F.first.blocksInOrder.map fun b => b.oracles.flatMap id).take k).map List.length).sum)
    (q : ℕ → ℕ × ℕ) (hq : ∀ τ O, decl[τ]? = some O → (O.logLength, O.words) = q τ)
    (h4 : ∀ n, n < decl.length → laidFull[base + n]? = some (q n)) :
    DeclHalf F base decl.length := by
  intro n hn o ho a W hl
  rw [hb, oracleAt_firstTold F k n decl h hn] at ho
  have e := hq n o ho
  rw [h4 n hn, ← e] at hl
  have e2 := Option.some.inj hl
  exact ⟨congrArg Prod.fst e2, congrArg Prod.snd e2⟩

/-- **The count's tie.** -/
theorem countTie_of {ds : List RDT} {i₀ m s : ℕ}
    (h1 : ((ds.take i₀).map (·.trees.length)).sum = s)
    (h2 : ((ds.take (i₀ + 2)).map (·.trees.length)).sum = s + m) : CountTie ds i₀ m := by
  intro d₁ d₂ e
  have e3 : ds.take (i₀ + 2) = ds.take i₀ ++ (ds.drop i₀).take 2 := List.take_add
  rw [e3, e, List.map_append, List.sum_append, h1] at h2
  simp at h2
  omega

end HashBuild
