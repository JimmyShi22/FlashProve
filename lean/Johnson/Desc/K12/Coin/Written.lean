-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Written.lean: A STRETCH WHOSE ROUNDS SEND AT MOST ONE TREE, BESIDE THE
LIBRARY's WRITTEN ROUNDS WITH AT MOST ONE TREE, WHATEVER THE STRETCH's ROUNDS OPEN. Definitions,
statements and proofs.

OnBytes/Maker/TreesOne.lean ties the two texts of a written round at `ds.map ofRD`: there a round's
data open what the library's round's data open. A file's stretch numbers what it opens through the
whole file; the library's chain of a proximity test numbers its own trees. No typed round, no view's
round and no column hangs on that list: so the tie is said again with the list free.

  `mk`: a round's data of the library with a list of openings of its own, as a stretch's.
  `trW`, `errW`: a stretch's transcript as the library's; the library's errors as the stretch's.
  `doomed_back`: **where the prover has lost over the library's rounds, it has lost over the
    stretch's**, at the same numbers, towards the same thing read along `trW`.
  `rvT_trW`, `pass_trW`, `colAtST_trW`, `treeShT_mk`: the rounds of a view, the tests of work, a
    column and a tree's shape are the same on both sides.
Nearest kin: OnBytes/Maker/TreesOne.lean (`trOneBack`, `rvT_one`, `passT_one`, `colAtST_one`), whose
`orcOneBack` is called and whose proofs are followed line for line.
A tool.
-/
import OnBytes.Maker.TreesOne
import Iop.Compose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker

/-- A round's data of the library, with a list of openings of its own; no stored table. -/
def mk (x : RD × List ℕ) : RDT := ⟨⟨x.1.entry, x.1.kind, x.1.items, x.1.tree.toList, x.2⟩, []⟩

section
variable (C : CK)

def trW : (lo : List (RD × List ℕ)) → Iop.Tr (uLT C (lo.map mk)) → Iop.Tr (uL C (lo.map (·.1)))
  | [], _ => ()
  | x :: lo, (m, c, τ) => ((orcOneBack x.1.tree m.1, m.2), c, trW lo τ)

def errW : (lo : List (RD × List ℕ)) → Err (uL C (lo.map (·.1))) → Err (uLT C (lo.map mk))
  | [], _ => ()
  | _ :: lo, (e, ε) => (e, errW lo ε)

/-- **The prover's loss goes back to the stretch.** -/
theorem doomed_back : ∀ (lo : List (RD × List ℕ)) (ε : Err (uL C (lo.map (·.1))))
    (bad : Iop.Tr (uL C (lo.map (·.1))) → Prop), Doomed (uL C (lo.map (·.1))) ε bad →
    Doomed (uLT C (lo.map mk)) (errW C lo ε) fun τ => bad (trW C lo τ)
  | [], _, _, h => h
  | x :: lo, (e, ε), bad, h => fun m => by
    have h1 : cnt (fun c : ((roundS C x.1).up).Chal => ¬ Doomed (uL C (lo.map (·.1))) ε
        fun τ => bad ((orcOneBack x.1.tree m.1, m.2), c, τ)) ≤ e :=
      h (orcOneBack x.1.tree m.1, m.2)
    refine le_trans (cnt_mono ?_) h1
    intro c hc hd
    exact hc (doomed_back lo ε (fun τ => bad ((orcOneBack x.1.tree m.1, m.2), c, τ)) hd)

theorem rvT_trW : ∀ (lo : List (RD × List ℕ)) (τ : Iop.Tr (uLT C (lo.map mk))),
    rvSL C (lo.map (·.1)) (trW C lo τ) = rvT C (lo.map mk) τ
  | [], _ => rfl
  | x :: lo, (m, c, τ) =>
    congrArg ((⟨PlainOf.gots x.1.items (GPlain.old (b := x.1.entry.work) m.2),
      C.dr x.1.entry x.1.kind (GChal.old (b := x.1.entry.work) c)⟩ : RV) :: ·) (rvT_trW lo τ)

theorem pass_trW : ∀ (lo : List (RD × List ℕ)) (τ : Iop.Tr (uLT C (lo.map mk))),
    passSL C (lo.map (·.1)) (rhoSL C (lo.map (·.1)) (trW C lo τ)) =
      passT C (lo.map mk) (rhoT C (lo.map mk) τ)
  | [], _ => rfl
  | x :: lo, (_, c, τ) => congrArg (GChal.pass (b := x.1.entry.work) c && ·) (pass_trW lo τ)

end

theorem treeShT_mk : ∀ (lo : List (RD × List ℕ)) (n : ℕ),
    treeShT (lo.map mk) n = treeSh (lo.map (·.1)) n
  | [], _ => rfl
  | (⟨_, _, _, none, _⟩, _) :: lo, n => by
      show (if n < 0 then _ else treeShT (lo.map mk) (n - 0)) = treeSh (lo.map (·.1)) n
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, treeShT_mk lo n]
  | (⟨_, _, _, some s, _⟩, _) :: lo, n => by
      show (if n < 1 then [s][n]? else treeShT (lo.map mk) (n - 1)) =
        if n = 0 then some s else treeSh (lo.map (·.1)) (n - 1)
      by_cases h : n = 0
      · subst h
        rfl
      · rw [if_neg (by omega), if_neg h, treeShT_mk lo (n - 1)]

theorem colAtST_trW (C : CK) : ∀ (lo : List (RD × List ℕ)) (τ : Iop.Tr (uLT C (lo.map mk)))
    (n x : ℕ), colAtST C (lo.map mk) τ n x = colAtS C (lo.map (·.1)) (trW C lo τ) n x
  | [], _, _, _ => rfl
  | (⟨_, _, _, none, _⟩, _) :: lo, (_, _, τ), n, x => by
      show (if n < 0 then _ else colAtST C (lo.map mk) τ (n - 0) x) =
        colAtS C (lo.map (·.1)) (trW C lo τ) n x
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero, colAtST_trW C lo τ n x]
  | (⟨_, _, _, some s, _⟩, _) :: lo, (m, _, τ), n, x => by
      show (if n < 1 then (posAtT [s] n x).map fun p => colT [s] p (m.1 p)
          else colAtST C (lo.map mk) τ (n - 1) x) =
        if n = 0 then (if h : x < 2 ^ s.a then some (List.ofFn (m.1 (.inl ⟨x, h⟩))) else none)
          else colAtS C (lo.map (·.1)) (trW C lo τ) (n - 1) x
      by_cases h : n = 0
      · subst h
        rw [if_pos Nat.one_pos, if_pos rfl]
        by_cases hx : x < 2 ^ s.a
        · have e : posAtT [s] 0 x = some (.inl ⟨x, hx⟩) := dif_pos hx
          rw [e, dif_pos hx]
          rfl
        · have e : posAtT [s] 0 x = none := dif_neg hx
          rw [e, dif_neg hx]
          rfl
      · rw [if_neg (by omega), if_neg h, colAtST_trW C lo τ (n - 1) x]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.doomed_back
#print axioms VerifiableInference.Desc.K12.Coin.rvT_trW
#print axioms VerifiableInference.Desc.K12.Coin.pass_trW
#print axioms VerifiableInference.Desc.K12.Coin.colAtST_trW
