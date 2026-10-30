-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratWalk.lean: where a chain's `walk` (Honest/Walk.lean) returns,
the data fit the `Step`s (`RoundFits`), a `Step` without a move declares no item except roots
(`itemsFall`), and each `Step` has as many oracle messages as its entry counts roots, a speaker of
Honest/StratC.lean writes, at the same challenges, a transcript of which the library's readers show
exactly what the walk has produced: the rounds; and, of every table produced, real or substitute,
the column at every position (`trOfC_walk`). It is the counterpart of `trOf_play`
(Honest/Law/StratPlay.lean), which says the same of `play` and the speakers of Honest/Strat.lean.

  1  `tellC_ok`, `hearC_ok`   one round
  2  `trOfC_walk`   a chain

It uses `say_fits` and `heard_laid` (Honest/Law/WalkOn.lean).

Limits.
  * Nothing is said where the walk returns an error.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratChainC
import Johnson.Desc.ProofFile.Honest.Law.StratPlay
import Johnson.Desc.ProofFile.Honest.Law.WalkOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT roundT rvT drawnT colAtST posAtT)
open _root_.Run.PQ (CK PlainOf)

variable {S Cl W Y : Type}

/-! ## 1 One round -/

theorem tellC_ok {z : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} (h : z.say s = .ok x) :
    tellC z (some s) = some x := by
  show some (((z.say s).toOption).getD (subTold s.decl s.oracles)) = some x
  rw [h]
  rfl

theorem hearC_ok {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (hx : z.say s = .ok x) (hz : z.heard L s x d = .ok z') : progressAfterChallenge L z (some s) d = z' := by
  simp only [progressAfterChallenge, hx, hz]

/-! ## 2 A chain -/

/-- **Where the walk returns, the speaker's transcript shows what the walk has produced.** `left`:
the `Step`s after those for which the data have a round. Three more hypotheses: `RoundFits`,
`itemsFall`, and as many oracle messages as roots. -/
theorem trOfC_walk (C : CK) (L : Lay) (left : List (Step W Y)) : ∀ (ds : List RDT)
    (ss : List (Step W Y)) (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)) (z' : ChainProgress S Cl W Y),
    walk L ss (drawnT C ds ρ) z = .ok z' →
    List.Forall₂ RoundFits ds (ss.map fun s => (s.decl, s.oracles)) →
    itemsFall ss [] = true → (∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) →
    ∃ ps, z'.laid = z.laid ++ ps ∧ rvT C ds (trOfC C L ds (ss ++ left) z ρ) = roundsOf ps ∧
      endOfC C L ds (ss ++ left) z ρ = (left, z') ∧
      ∀ (n x : Nat) (pt : Place × Table), ((tablesOf ps)[n]?).bind id = some pt →
        x < 2 ^ pt.2.logLength →
        colAtST C ds (trOfC C L ds (ss ++ left) z ρ) n x = some (pt.2.col x)
  | [], [], z, ρ, z', hw, _, _, _ => by
    have hw' : walk L ([] : List (Step W Y)) [] z = .ok z' := hw
    rw [walk_nil_ok hw']
    exact ⟨[], (List.append_nil _).symm, rfl, rfl, fun n x pt h => by simp [tablesOf] at h⟩
  | [], _ :: _, _, _, _, _, hF, _, _ => by
    rw [List.map_cons] at hF
    cases hF
  | _ :: _, [], _, _, _, _, hF, _, _ => by cases hF
  | d :: ds, s :: ss, z, (c, ρ), z', hw, hF, hi, ho => by
    have hw' : walk L (s :: ss) (drOf C d c :: drawnT C ds ρ) z = .ok z' := hw
    obtain ⟨x, z₁, hx, hz₁, hw₁⟩ := walk_cons_ok hw'
    rw [List.map_cons] at hF
    obtain ⟨⟨hit, htr⟩, hF'⟩ := List.forall₂_cons.1 hF
    have hi' : ((s.move.isSome ||
        (([] : List Fmt.ItemValue).map itemOf == s.decl.items.filter (· != .root))) &&
        itemsFall ss []) = true := hi
    rw [Bool.and_eq_true, Bool.or_eq_true] at hi'
    obtain ⟨ps, ih0, ih1, ih2, ih3⟩ := trOfC_walk C L left ds ss z₁ ρ z' hw₁ hF' hi'.2
      fun s' hs' => ho s' (List.mem_cons_of_mem _ hs')
    obtain ⟨hv, hl, ht⟩ := say_fits hx (hi'.1.imp id fun h => beq_iff_eq.1 h)
      (ho s List.mem_cons_self)
    have hvals : x.vals.map itemOf = d.items.filter (· != .root) := by
      rw [hit]
      exact hv
    have htrO : trOfC C L (d :: ds) (s :: ss ++ left) z (c, ρ) =
        ((msgOf C d (some x), c, trOfC C L ds (ss ++ left) z₁ ρ) : Iop.Tr (uLT C (d :: ds))) := by
      show ((msgOf C d (tellC z (some s)), c, trOfC C L ds (ss ++ left)
        (progressAfterChallenge L z (some s) (drOf C d c)) ρ) : Iop.Tr (uLT C (d :: ds))) = _
      rw [tellC_ok hx, hearC_ok hx hz₁]
    have hend : endOfC C L (d :: ds) (s :: ss ++ left) z (c, ρ) =
        endOfC C L ds (ss ++ left) z₁ ρ := by
      show endOfC C L ds (ss ++ left) (progressAfterChallenge L z (some s) (drOf C d c)) ρ = _
      rw [hearC_ok hx hz₁]
    have hlen : x.tables.length = d.trees.length := by
      have h1 := congrArg List.length htr
      rw [List.length_map, List.length_map] at h1
      rw [hl, h1]
    refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, drOf C d c⟩ :: ps, ?_,
      ?_, ?_, ?_⟩
    · rw [ih0, heard_laid hz₁, List.append_assoc]
      rfl
    · rw [htrO]
      show (⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work)
        (Iop.GPlain.mk d.entry.work (plainOf d.items x.vals) (0 : ℕ))), drOf C d c⟩ : Fmt.RoundView) ::
          rvT C ds (trOfC C L ds (ss ++ left) z₁ ρ) = ⟨x.vals, drOf C d c⟩ :: roundsOf ps
      rw [Iop.GPlain.old_mk, gots_plainOf _ _ hvals, ih1]
    · rw [hend]
      exact ih2
    · intro n k pt hn hk
      rw [htrO, OnBytes.Maker.colAtST_cons]
      have hn' : (((x.tables.map fun t => t.map fun u => (s.addr.place, u)) ++
          tablesOf ps)[n]?).bind id = some pt := hn
      by_cases hlt : n < d.trees.length
      · rw [if_pos hlt]
        rw [List.getElem?_append_left (by rw [List.length_map, hlen]; exact hlt),
          List.getElem?_map] at hn'
        cases hp1 : x.tables[n]? with
        | none =>
          rw [hp1] at hn'
          cases hn'
        | some o =>
          rw [hp1] at hn'
          cases o with
          | none => cases hn'
          | some t =>
            cases hn'
            have h4 := ht n t hp1
            rw [← htr, List.getElem?_map] at h4
            cases hs1 : d.trees[n]? with
            | none =>
              rw [hs1] at h4
              cases h4
            | some sh =>
              rw [hs1] at h4
              have h5 : (sh.a, sh.W) = (t.logLength, t.words) := Option.some.inj h4
              have ha : sh.a = t.logLength := (Prod.mk.inj h5).1
              have hw2 : t.words = sh.W := (Prod.mk.inj h5).2.symm
              obtain ⟨q, hq⟩ := posAtT_some d.trees n k sh hs1 (by rw [ha]; exact hk)
              rw [hq]
              exact congrArg some (colT_orcOf d.trees x.tables n k q t sh hq hp1 hs1 hw2)
      · rw [if_neg hlt]
        have hge : d.trees.length ≤ n := Nat.le_of_not_lt hlt
        rw [List.getElem?_append_right (by rw [List.length_map, hlen]; exact hge),
          List.length_map, hlen] at hn'
        exact ih3 _ k pt hn' hk

end ProofFile.Honest

#print axioms ProofFile.Honest.tellC_ok
#print axioms ProofFile.Honest.hearC_ok
#print axioms ProofFile.Honest.trOfC_walk
