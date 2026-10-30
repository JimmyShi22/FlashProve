-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Lot/K4One.lean: in the list of K4's lot (`k4From`,
Johnson/Desc/ProofFile/Lot/K4.lean) ONE MEMBER AT MOST BEARS A GIVEN SEGMENT's NUMBER; and the lot's
block's place is made of that number. Statements and proofs on the lot's own text.

  `k4From_link_ge`: every member of `k4From Z G L n last` has n ≤ x.2.link.
  `k4From_link_inj`: two members of one such list with the same x.2.link are the same pair: Bool,
    name, the list before and all.
  `k4Block_place`: the lot's block at x stands at the place (1, x.2.link, x.2.piece, K4).
  `k4From_place_inj`: two members whose blocks bear one place are the same pair.

Limits. Nothing on which numbers occur (that is `k4From_par`'s and the seat's laws'), on what G.W
is, or on the values of the Bool and of the field before. «At most one», not «one». Nothing on
soundness.
-/
import Johnson.Desc.ProofFile.Lot.K4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- Every member's segment's number is at least the number at which the list starts. -/
theorem k4From_link_ge (Z : Pub) (G : Ground) :
    ∀ (l : List LinkH) (n : Nat) (last : Option String) (x : Bool × OnBytes.Desc.First.K4.Par),
      x ∈ k4From Z G l n last → n ≤ x.2.link
  | [], _, _, x, h => by simp [k4From] at h
  | X :: rest, n, last, x, h => by
    unfold k4From at h
    split at h
    · rcases List.mem_append.mp h with h1 | h2
      · split at h1
        · have e : x = _ := List.mem_singleton.mp h1
          subst e
          exact Nat.le_refl _
        · cases h1
      · exact Nat.le_of_succ_le (k4From_link_ge Z G rest (n + 1) (some X.name) x h2)
    · exact Nat.le_of_succ_le (k4From_link_ge Z G rest (n + 1) last x h)

/-- **One member at most bears a given segment's number.** -/
theorem k4From_link_inj (Z : Pub) (G : Ground) :
    ∀ (l : List LinkH) (n : Nat) (last : Option String)
      (x y : Bool × OnBytes.Desc.First.K4.Par),
      x ∈ k4From Z G l n last → y ∈ k4From Z G l n last → x.2.link = y.2.link → x = y
  | [], _, _, x, _, h, _, _ => by simp [k4From] at h
  | X :: rest, n, last, x, y, hx, hy, e => by
    unfold k4From at hx hy
    split at hx
    · rename_i hk
      rw [if_pos hk] at hy
      rcases List.mem_append.mp hx with x1 | x2
      · rcases List.mem_append.mp hy with y1 | y2
        · split at x1
          · rename_i hp hq
            split at y1
            · rename_i hp' hq'
              obtain rfl : hp = hp' := Option.some.inj (hq.symm.trans hq')
              exact (List.mem_singleton.mp x1).trans (List.mem_singleton.mp y1).symm
            · cases y1
          · cases x1
        · have q := k4From_link_ge Z G rest (n + 1) (some X.name) y y2
          split at x1
          · have ex : x = _ := List.mem_singleton.mp x1
            subst ex
            have e' : n = y.2.link := e
            omega
          · cases x1
      · rcases List.mem_append.mp hy with y1 | y2
        · have q := k4From_link_ge Z G rest (n + 1) (some X.name) x x2
          split at y1
          · have ey : y = _ := List.mem_singleton.mp y1
            subst ey
            have e' : x.2.link = n := e
            omega
          · cases y1
        · exact k4From_link_inj Z G rest (n + 1) (some X.name) x y x2 y2 e
    · rename_i hk
      rw [if_neg hk] at hy
      exact k4From_link_inj Z G rest (n + 1) last x y hx hy e

/-- The lot's block's place. -/
theorem k4Block_place (x : Bool × OnBytes.Desc.First.K4.Par) :
    (k4Block x).place = { chain := 1, link := some x.2.link, piece := x.2.piece, kind := .K4 } :=
  rfl

/-- **Two members whose blocks bear one place are the same pair.** -/
theorem k4From_place_inj (Z : Pub) (G : Ground) (l : List LinkH) (n : Nat) (last : Option String)
    (x y : Bool × OnBytes.Desc.First.K4.Par) (hx : x ∈ k4From Z G l n last)
    (hy : y ∈ k4From Z G l n last) (e : (k4Block x).place = (k4Block y).place) : x = y := by
  rw [k4Block_place, k4Block_place] at e
  have e1 : (some x.2.link : Option Nat) = some y.2.link :=
    congrArg VerifiableInference.Desc.Place.link e
  exact k4From_link_inj Z G l n last x y hx hy (Option.some.inj e1)

end ProofFile

#print axioms ProofFile.k4From_link_ge
#print axioms ProofFile.k4From_link_inj
#print axioms ProofFile.k4Block_place
#print axioms ProofFile.k4From_place_inj
