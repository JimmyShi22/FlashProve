-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RoundsLink.lean: what the link's first five rounds send and draw.

The link, the format's protocol between two stored tables (OnBytes/Slice/README.md has the
vocabulary), begins with five rounds, which the format defines from the sizes: `rLinkPoint`, `rLink`
and `rLinkPhi` (Fmt/M3Plan.lean), `rSeedN` and `rAnswers` (Fmt/M2Plan.lean). For each of them this
file says how many elements the prover sends, how many elements and positions the verifier draws,
and that nothing else is drawn. The notions `IsRd` and `SendsDraws` are those of
OnBytes/Slice/RoundsOf.lean, which does the same for the rounds after these five.

Main theorems.
 `rLinkPoint_sd`  the point: nothing is sent, v elements are drawn.
 `rSeedN_sd`      the sending of a tree: no element is sent, n + 1 elements are drawn.
 `rSeedN_nz`      the last of these, the seed's factor, is drawn other than 0.
 `rAnswers_sd`    n answers are sent, nothing is drawn.
 `rLink_sd`       nothing is sent, n positions below 2^a are drawn.
 `rLinkPhi_sd`    nothing is sent, a elements are drawn.

Not claimed. Nothing on the trees that a round sends or opens, nor on the test of work. Nothing on
which rounds a given description has.
-/
import Fmt.M3Plan
import OnBytes.Slice.RoundsOf

set_option autoImplicit false

namespace OnBytes.Slice
open Run

/-- A message of n answers holds n elements. -/
theorem nS_replicate_answer : ∀ n, nS (List.replicate n Fmt.Item.answer) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (nS_replicate_answer n)

/-- The link's point: nothing is sent, v elements are drawn. -/
theorem rLinkPoint_sd {d : PQ.RD} {v : ℕ} (h : IsRd d (Fmt.M3.rLinkPoint v)) :
    SendsDraws d 0 v 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.elems ≠ .sealed) (by decide : Fmt.Kind.elems ≠ .seeds)
    (Nat.zero_le v) (Nat.zero_le 64)

/-- The sending of a tree: no element is sent; a seed of n elements and a factor is drawn. -/
theorem rSeedN_sd {d : PQ.RD} {n : ℕ} (h : IsRd d (Fmt.M2.rSeedN n)) :
    SendsDraws d 0 (n + 1) 0 0 where
  sent := by rw [h.items]; rfl
  plain := by
    rw [h.dsOf]
    exact plain_dsOf _ _ rfl (by decide : Fmt.Kind.seeds ≠ .sealed)
  els := by rw [h.dsOf]; exact nE_dsOf_seed (Fmt.M2.rSeedN n).entry rfl (Nat.le_add_left 1 n)
  poss := by rw [h.dsOf]; exact nP_dsOf (Fmt.M2.rSeedN n).entry _
  allPos := by rw [h.dsOf]; exact allPos_dsOf (Fmt.M2.rSeedN n).entry _
  logN := by rw [h.entry]; exact Nat.zero_le 64

/-- The factor of the seed, its last element, is drawn other than 0. -/
theorem rSeedN_nz {d : PQ.RD} {n : ℕ} (h : IsRd d (Fmt.M2.rSeedN n)) :
    IsNZ (Fmt.dsOf d.entry d.kind) n := by
  rw [h.dsOf]
  exact isNZ_dsOf_seed (Fmt.M2.rSeedN n).entry rfl

/-- The answers to a seed: n elements are sent, nothing is drawn. -/
theorem rAnswers_sd {d : PQ.RD} {n : ℕ} (h : IsRd d (Fmt.M2.rAnswers n)) :
    SendsDraws d n 0 0 0 := by
  have h0 : SendsDraws d (nS (List.replicate n Fmt.Item.answer)) 0 0 0 :=
    sendsDraws_of h rfl (by decide : Fmt.Kind.nothing ≠ .sealed)
      (by decide : Fmt.Kind.nothing ≠ .seeds) (Nat.le_refl 0) (Nat.zero_le 64)
  exact ⟨h0.sent.trans (nS_replicate_answer n), h0.plain, h0.els, h0.poss, h0.allPos, h0.logN⟩

/-- The link's draws: nothing is sent, n positions below 2^a are drawn. -/
theorem rLink_sd {d : PQ.RD} {work n a : ℕ} (h : IsRd d (Fmt.M3.rLink work n a)) (ha : a ≤ 64) :
    SendsDraws d 0 0 n a :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.positions ≠ .sealed)
    (by decide : Fmt.Kind.positions ≠ .seeds) (Nat.le_refl 0) ha

/-- The link's second point: nothing is sent, a elements are drawn. -/
theorem rLinkPhi_sd {d : PQ.RD} {a : ℕ} (h : IsRd d (Fmt.M3.rLinkPhi a)) :
    SendsDraws d 0 a 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.elems ≠ .sealed) (by decide : Fmt.Kind.elems ≠ .seeds)
    (Nat.zero_le a) (Nat.zero_le 64)

end OnBytes.Slice

#print axioms OnBytes.Slice.rLinkPoint_sd
#print axioms OnBytes.Slice.rSeedN_sd
#print axioms OnBytes.Slice.rSeedN_nz
#print axioms OnBytes.Slice.rAnswers_sd
#print axioms OnBytes.Slice.rLink_sd
#print axioms OnBytes.Slice.rLinkPhi_sd
