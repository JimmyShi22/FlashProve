-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LikeOf.lean: THE PREMISE `like` OF THE PROXIMITY TEST's LAW (`AtPlace`,
Sheet.lean), AND `batNone`, FROM WHAT A FILE's MAKER SAYS OF A STRETCH's DATA ROUND BY ROUND.
Statements and proofs, on lists; no file's description is named here.

`like` asks that the stretch's data be the place's declared rounds "as written"
(`H2K.Pub.writtenOf`, Johnson/Desc/K12/Law/PubOk.lean): entry, kind, items, and THE SHAPE OF THE
TREE THAT A ROUND SENDS. A file's maker does not read that shape off the sending round: it takes the
shape under which the tree is opened. So the shapes agree because the test's own rounds open every
tree that the test sends, under the shape that the plan tells.

  `layOpens_flat`, `told_mem`: every tree that the test sends is opened by one of its declared
    rounds, under its told shape and its own number.
  `layW_roots`, `layW_like`: along `layW`: if the data have each declared round's entry, kind and
    cut, send as many trees as it declares roots, open no stored table, and THEIR TREES IN A ROW ARE
    THE TOLD SHAPES, then they are `Like` the written rounds.
  `RoundAs`: what is asked of one round's data against its declared round.
  `flat_trees`: the trees in a row are the told shapes: from a list allT of all the file's trees'
    shapes such that (cut) the stretch's n-th tree is allT's number base + n, (open) every declared
    opening o finds its shape at allT's number num o.2, and `numOwn`.
  `like_of_data`: **`like`**.
Limits: the premises `RoundAs`, (cut) and (open) are shown of no file's data here. No soundness is
claimed.
A tool.
-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.OpenLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (writtenOf WR layW)

/-- The told shapes and sources of the trees that a test sends. -/
def toldOf (N : H2U.TestNums) : List (Fmt.Shape × Fmt.TreeSource) :=
  N.sent.zipIdx.map fun t => N.own t.1.1 t.1.2 (N.free + t.2)

theorem layOpens_flat (own : Bool) : ∀ (rs : List Fmt.Round) (seen : Bool)
    (L : List (List (Fmt.Shape × Fmt.TreeSource))) (ds : List Fmt.DeclaredRound),
    H2U.layOpens own seen rs L = some ds → ds.flatMap (·.opens) = L.flatten
  | [], _, [], ds, h => by
    cases h
    rfl
  | [], _, _ :: _, _, h => by cases h
  | r :: rs, seen, L, ds, h => by
    unfold H2U.layOpens at h
    dsimp only at h
    split at h
    · obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [List.flatMap_cons, layOpens_flat own rs _ L ds' h']
      rfl
    · split at h
      · rename_i x t
        split at h
        · cases h
        · obtain ⟨ds', h', rfl⟩ := Option.map_eq_some_iff.1 h
          rw [List.flatMap_cons, layOpens_flat own rs _ t ds' h', List.flatten_cons]
      · cases h

theorem told_mem (N : H2U.TestNums) (rs : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rs) : ∀ o ∈ toldOf N, o ∈ rs.flatMap (·.opens) := by
  intro o ho
  unfold H2U.roundsOfNums at h
  split at h
  · rw [layOpens_flat _ _ _ _ _ h, List.flatten_cons, List.mem_append, List.mem_append]
    have ho' : o ∈ (toldOf N).take 1 ++ (toldOf N).drop 1 := by
      rw [List.take_append_drop]
      exact ho
    cases hm : N.ownMask with
    | true =>
      rcases List.mem_append.1 ho' with h1 | h1
      · exact .inl (.inr (by simpa using h1))
      · refine .inr ?_
        rw [List.mem_flatten]
        exact ⟨[o], List.mem_map.2 ⟨o, by simpa using h1, rfl⟩, List.mem_singleton.2 rfl⟩
    | false =>
      refine .inr ?_
      rw [List.mem_flatten]
      exact ⟨[o], List.mem_map.2 ⟨o, by simpa [toldOf] using ho, rfl⟩, List.mem_singleton.2 rfl⟩
  · cases h

theorem layW_roots : ∀ (rs : List Fmt.DeclaredRound) (sh : List Fmt.Shape) (ws : List WR),
    layW rs sh = some ws → (rs.map (·.entry.roots)).sum = sh.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | r :: rs, sh, ws, h => by
    unfold layW at h
    split at h
    · cases h
    · split at h
      · rename_i h0
        obtain ⟨ws', h', _⟩ := Option.map_eq_some_iff.1 h
        rw [List.map_cons, List.sum_cons, layW_roots rs sh ws' h', eq_of_beq h0, Nat.zero_add]
      · split at h
        · rename_i h1
          split at h
          · rename_i s t
            obtain ⟨ws', h', _⟩ := Option.map_eq_some_iff.1 h
            rw [List.map_cons, List.sum_cons, layW_roots rs t ws' h', eq_of_beq h1,
              List.length_cons, Nat.add_comm]
          · cases h
        · cases h

/-- What is asked of one round's data against its declared round. -/
def RoundAs (d : RDT) (r : Fmt.DeclaredRound) : Prop :=
  d.entry = r.entry ∧ Fmt.kindOf r.entry.name = some d.kind ∧ d.items = r.items ∧
    d.trees.length = r.entry.roots ∧ d.stored = []

theorem layW_like : ∀ (rs : List Fmt.DeclaredRound) (sh : List Fmt.Shape) (ws : List WR)
    (ds : List RDT), layW rs sh = some ws → List.Forall₂ RoundAs ds rs →
    ds.flatMap (·.trees) = sh → List.Forall₂ Like ds ws
  | [], [], _, _, h, .nil, _ => by
    cases h
    exact .nil
  | [], _ :: _, _, _, h, _, _ => by cases h
  | r :: rs, sh, ws, _, h, .cons (a := d) (l₁ := ds) hd ht, hf => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hd
    unfold layW at h
    rw [a2] at h
    dsimp only at h
    split at h
    · rename_i h0
      obtain ⟨ws', h', rfl⟩ := Option.map_eq_some_iff.1 h
      have hn : d.trees = [] := List.eq_nil_of_length_eq_zero (a4.trans (eq_of_beq h0))
      rw [List.flatMap_cons, hn, List.nil_append] at hf
      exact .cons ⟨a1, rfl, a3, hn, a5⟩ (layW_like rs sh ws' ds h' ht hf)
    · split at h
      · rename_i h1
        split at h
        · rename_i s t
          obtain ⟨ws', h', rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 (a4.trans (eq_of_beq h1))
          rw [List.flatMap_cons, hy, List.singleton_append] at hf
          obtain ⟨rfl, hf'⟩ := List.cons.inj hf
          exact .cons ⟨a1, rfl, a3, hy, a5⟩ (layW_like rs t ws' ds h' ht hf')
        · cases h
      · cases h

theorem trees_sum : ∀ (ds : List RDT) (rs : List Fmt.DeclaredRound), List.Forall₂ RoundAs ds rs →
    (ds.flatMap (·.trees)).length = (rs.map (·.entry.roots)).sum
  | _, _, .nil => rfl
  | _, _, .cons hd ht => by
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, hd.2.2.2.1,
      trees_sum _ _ ht]

/-- The stretch's trees in a row are the told shapes. -/
theorem flat_trees (N : H2U.TestNums) (rs : List Fmt.DeclaredRound)
    (hrs : H2U.roundsOfNums N = some rs) (ws : List WR)
    (hw : layW rs ((toldOf N).map (·.1)) = some ws) (ds : List RDT)
    (hE : List.Forall₂ RoundAs ds rs) (num : Fmt.TreeSource → ℕ) (base : ℕ)
    (allT : List Fmt.Shape)
    (hcut : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allT[base + n]? = some x)
    (hopen : ∀ o ∈ rs.flatMap (·.opens), allT[num o.2]? = some o.1)
    (hnum : ∀ n, num (.own (N.free + n)) = base + n) :
    ds.flatMap (·.trees) = (toldOf N).map (·.1) := by
  have hlen : (ds.flatMap (·.trees)).length = ((toldOf N).map (·.1)).length := by
    rw [trees_sum ds rs hE, layW_roots rs _ ws hw]
  refine List.ext_getElem hlen fun n h1 h2 => ?_
  have c1 := hcut n _ (List.getElem?_eq_getElem h1)
  have h3 : n < (toldOf N).length := by rwa [List.length_map] at h2
  have c2 := hopen _ (told_mem N rs hrs _ (List.getElem_mem h3))
  have e : ((toldOf N)[n]).2 = .own (N.free + n) := by
    unfold toldOf
    rw [List.getElem_map, List.getElem_zipIdx]
    show Fmt.TreeSource.own (N.free + (0 + n)) = _
    rw [Nat.zero_add]
  rw [e, hnum n, c1] at c2
  rw [List.getElem_map]
  exact Option.some.inj c2

/-- **`AtPlace.like`, from what a maker says of the stretch's data.** -/
theorem like_of_data (π : P12) (rs : List Fmt.DeclaredRound)
    (hrs : H2U.roundsOfNums π.nums = some rs) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) (ds : List RDT) (hE : List.Forall₂ RoundAs ds rs)
    (num : Fmt.TreeSource → ℕ) (base : ℕ) (allT : List Fmt.Shape)
    (hcut : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allT[base + n]? = some x)
    (hopen : ∀ o ∈ rs.flatMap (·.opens), allT[num o.2]? = some o.1)
    (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n) :
    ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like ds (w0 :: l) := by
  have hw' : layW rs ((toldOf π.nums).map (·.1)) = some (w0 :: l) := by
    unfold writtenOf at hw
    rw [hrs] at hw
    unfold toldOf
    rw [List.map_map]
    exact hw
  exact ⟨w0, l, hw, layW_like rs _ _ ds hw' hE
    (flat_trees π.nums rs hrs _ hw' ds hE num base allT hcut hopen hnum)⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.told_mem
#print axioms VerifiableInference.Desc.K12.Coin.layW_like
#print axioms VerifiableInference.Desc.K12.Coin.flat_trees
#print axioms VerifiableInference.Desc.K12.Coin.like_of_data
