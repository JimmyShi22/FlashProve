-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/BaseAtPiece.lean: in a row of pieces that tiles a chain, a piece's base (the
number, through the file, of the first tree that its stretch sends) is the row's first base plus THE
ROOTS THAT THE SUB-PROTOCOLS IN FRONT DECLARE. At every row, every size, every kind. Statements and
proofs; no definition.

  `base_at`          q.base = p.base + the trees that the stretches in front send
  `trees_of_along`   a stretch that goes along declared rounds, one for one, sends as many trees as
                     these rounds' entries declare roots
  `base_declared`    THE STATEMENT: q.base = p.base + the roots declared by the rounds of the
                     sub-protocols in front
Premises of `base_declared`: the row tiles (`Tiled`, Johnson/Desc/Sound/ChainRule.lean) · each
piece's stretch goes along its own sub-protocol's declared rounds (`Along (RoundIs num)`,
Johnson/Desc/Sound/Stretch.lean: `stretchOfData` has that of every piece of an IOP as written).
Limits. Nothing on the verifier's state: that the state has counted just these roots is other
files' to show. Nothing on soundness.

-/
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.Sound.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (Frame Piece Tiled nTrees Along RoundIs)
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- A piece's base is the row's first base plus the trees that the stretches in front send. -/
theorem base_at : ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W), Tiled p l →
    ∀ (k : Nat) (q : Piece C F S Cl W), (p :: l)[k]? = some q →
      q.base = p.base + (((p :: l).take k).map (·.trees)).sum
  | _, p, _, 0, q, hq => by
    obtain rfl : p = q := by simpa using hq
    simp
  | [], _, _, k + 1, q, hq => by simp at hq
  | q' :: l, p, ht, k + 1, q, hq => by
    obtain ⟨-, -, -, hb, ht'⟩ := ht
    have hq' : (q' :: l)[k]? = some q := by simpa using hq
    rw [base_at l q' ht' k q hq', hb, List.take_succ_cons, List.map_cons, List.sum_cons]
    omega

/-- A stretch that goes along declared rounds, one for one, sends as many trees as they declare
roots. -/
theorem trees_of_along {num : Fmt.TreeSource → Nat} : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    ds.length = rs.length → Along (RoundIs num) rs ds →
    nTrees ds = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl
  | r :: rs, d :: ds, hl, h => by
    have h' : RoundIs num r d ∧ Along (RoundIs num) rs ds := h
    have ih := trees_of_along rs ds (Nat.succ.inj hl) h'.2
    have e : d.trees.length = r.entry.roots := h'.1.2.2.2.2.2
    unfold nTrees at ih ⊢
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, e]

/-- In a tiling row every piece but the last has no round put behind its own, and is owed just its
stretch: so its stretch has as many rounds as its sub-protocol declares. -/
theorem length_in_front : ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W), Tiled p l →
    ∀ (k : Nat), k < l.length + 1 → ∀ x ∈ (p :: l).take k, x.ds.length = x.b.rounds.length
  | _, _, _, 0, _, x, hx => by simp at hx
  | [], _, _, k + 1, hk, _, _ => by simp at hk
  | q' :: l, p, ht, k + 1, hk, x, hx => by
    obtain ⟨ho, -, hb, -, ht'⟩ := ht
    rw [List.take_succ_cons] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have := ho.1
      rw [hb] at this
      simpa using this
    · exact length_in_front l q' ht' k (by simpa using hk) x hx

/-- **A piece's base is the row's first base plus the roots that the sub-protocols in front
declare.** -/
theorem base_declared {num : Fmt.TreeSource → Nat} (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (ht : Tiled p l)
    (hA : ∀ x ∈ p :: l, Along (RoundIs num) x.b.rounds x.ds) {k : Nat} {q : Piece C F S Cl W}
    (hq : (p :: l)[k]? = some q) :
    q.base = p.base +
      (((p :: l).take k).map fun x => (x.b.rounds.map (·.entry.roots)).sum).sum := by
  rw [base_at l p ht k q hq]
  congr 1
  have hk : k < l.length + 1 := by
    have := (List.getElem?_eq_some_iff.1 hq).1
    simpa using this
  congr 1
  refine List.map_congr_left fun x hx => ?_
  exact trees_of_along x.b.rounds x.ds (length_in_front l p ht k hk x hx)
    (hA x (List.mem_of_mem_take hx))

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.base_at
#print axioms VerifiableInference.Desc.First.K2.trees_of_along
#print axioms VerifiableInference.Desc.First.K2.length_in_front
#print axioms VerifiableInference.Desc.First.K2.base_declared
