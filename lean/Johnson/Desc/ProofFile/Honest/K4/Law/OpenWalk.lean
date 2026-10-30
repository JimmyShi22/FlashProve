-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OpenWalk.lean: CONDITIONAL.

What is here. Two lists of weight claims, compared member by member. The verifier's function
(`ClaimEnv.weightClaims`, OnBytes/Model/LayerPanels.lean) makes both, at one environment but for the
batched sumcheck's challenges and the second token sumcheck's end point. Two members of one number
are claims on the unit of one kind and layer; their two rules for the factors agree on every group
of that kind's units which is named neither "kk" nor "e" nor "cd". At kind 0 the second rule's
factor on "cd" is the rotation factor at the end point.

  `ClaimPair`   the relation
  `claims_walk`   **the two lists are in the relation, member by member**

Limits. On the verifier's public functions alone. Both lists are given as returned; so is what
`headWeights` returns, which is asked even where no call holds the queries and keys. The names of a
kind's groups are the library's list `namesOf` (Johnson/Road/FormsKeysWLay.lean): that a layout's
units have these groups is not said here (the library has it of what `wsLayOf` returns:
`groups_found`, Johnson/Road/FormsKeysWv.lean). Nothing on a matrix or a value.

No property is claimed.
-/
import Johnson.Road.FormsKeysWv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (WsGrp WsFac WsClaim eqTab)
open OnBytes.Model.Layer (ClaimEnv isAcc)
open OnBytes.Road (namesOf weightClaims_some claimsA_not claimsA_eq claimsT_QK_eq claimsT_routed_eq
  claimsT_other mapM_rel rel_append rel_flatten bind_some)

/-- **Two claims on the unit of one kind X and layer lam**, made at the environments c0 and c by two
rules for the factors. The rules agree on every group whose name is one of the kind's and is neither
"kk" nor "e" nor "cd". At kind 0 the second rule's factor on "cd" is the rotation factor at c's end
point, with lfc for the equality table of the coordinates within a head. -/
def ClaimPair (c0 c : ClaimEnv) (lfc : Array E) (x0 x : WsClaim) : Prop :=
  ∃ (X lam : ℕ) (fac0 fac : WsGrp → Option WsFac), X ≤ 11 ∧ c0.claim X lam fac0 = some x0 ∧
    c.claim X lam fac = some x ∧
    (∀ G : WsGrp, G.name ∈ namesOf X → G.name ≠ "kk" → G.name ≠ "e" → G.name ≠ "cd" →
      fac0 G = fac G) ∧
    (X = 0 → ∀ G : WsGrp, G.name = "cd" →
      fac G = some { AV := c.ropeFactor (eqTab c.rt) lfc lam })

/-- **The two lists are in the relation, member by member.** AH, lfc: what `headWeights` returns.
-/
theorem claims_walk (c0 : ClaimEnv) (rs rt : Array E) (TS : List ℕ) {cl0 cl : List WsClaim}
    (h0 : c0.weightClaims TS = some cl0)
    (h : ({ c0 with rs := rs, rt := rt } : ClaimEnv).weightClaims TS = some cl)
    {AH lfc : Array E} (hw : c0.headWeights = some (AH, lfc)) :
    List.Forall₂ (ClaimPair c0 { c0 with rs := rs, rt := rt } lfc) cl0 cl := by
  obtain ⟨a, t, ha, ht, rfl⟩ :=
    weightClaims_some (p := ⟨c0.v, #[], #[], #[], fun _ _ _ => 0⟩) rfl h0
  obtain ⟨a', t', ha', ht', rfl⟩ := weightClaims_some (c := { c0 with rs := rs, rt := rt })
    (p := ⟨c0.v, #[], #[], #[], fun _ _ _ => 0⟩) rfl h
  have rA : List.Forall₂ (List.Forall₂ (ClaimPair c0 { c0 with rs := rs, rt := rt } lfc)) a a' := by
    refine mapM_rel _ _ a a' ha ha' fun sn _ l l' hl1 hl2 => ?_
    cases hacc : isAcc sn with
    | false =>
      rw [claimsA_not c0 _ hacc] at hl1
      rw [claimsA_not _ _ hacc] at hl2
      cases hl1
      cases hl2
      exact List.Forall₂.nil
    | true =>
      rw [claimsA_eq c0 sn hacc] at hl1
      rw [claimsA_eq _ sn hacc] at hl2
      refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
      refine ⟨_, _, _, _, ?_, hx, hx', fun G _ k1 _ _ => ?_, fun e0 => absurd e0 ?_⟩
      · split_ifs <;> decide
      · have k1' : (G.name == "kk") = false := by simpa using k1
        simp only [k1']
        rfl
      · split_ifs <;> decide
  have rT : List.Forall₂ (List.Forall₂ (ClaimPair c0 { c0 with rs := rs, rt := rt } lfc)) t t' := by
    refine mapM_rel _ _ t t' ht ht' fun sn _ l l' hl1 hl2 => ?_
    by_cases hQ : (sn == "QK") = true
    · have e : sn = "QK" := beq_iff_eq.mp hQ
      subst e
      rw [claimsT_QK_eq] at hl1 hl2
      obtain ⟨⟨AH1, lfc1⟩, hw1, hl1⟩ := bind_some hl1
      obtain ⟨⟨AH2, lfc2⟩, hw2, hl2⟩ := bind_some hl2
      have e1 : (AH1, lfc1) = (AH, lfc) := Option.some.inj (hw1.symm.trans hw)
      have e2 : (AH2, lfc2) = (AH, lfc) := Option.some.inj (hw2.symm.trans hw)
      cases e1
      cases e2
      refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
      refine ⟨0, i, _, _, Nat.zero_le _, hx, hx', fun G hG k1 _ k3 => ?_, fun _ G hG => ?_⟩
      · have hm : G.name = "hd" := by
          have : G.name ∈ ["hd", "cd", "kk"] := hG
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with e | e | e
          · exact e
          · exact absurd e k3
          · exact absurd e k1
        simp [hm]
      · simp [hG]
    · by_cases hR : (c0.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true
      · have hR' := hR
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hR'
        obtain ⟨h3, hgud⟩ := hR'
        have hname : sn = "G" ∨ sn = "U" ∨ sn = "D" := by
          rcases hgud with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        rw [claimsT_routed_eq c0 sn h3 hname] at hl1
        rw [claimsT_routed_eq ({ c0 with rs := rs, rt := rt } : ClaimEnv) sn h3 hname] at hl2
        refine mapM_rel _ _ l l' hl1 hl2 fun i _ x x' hx hx' => ?_
        refine ⟨_, _, _, _, ?_, hx, hx', fun G _ k1 k2 _ => ?_, fun e0 => absurd e0 ?_⟩
        · split_ifs <;> decide
        · have k1' : (G.name == "kk") = false := by simpa using k1
          have k2' : (G.name == "e") = false := by simpa using k2
          simp only [k1', k2']
          rfl
        · split_ifs <;> decide
      · rw [claimsT_other c0 _ hQ hR] at hl1
        rw [claimsT_other ({ c0 with rs := rs, rt := rt } : ClaimEnv) _ hQ hR] at hl2
        cases hl1
        cases hl2
        exact List.Forall₂.nil
  exact rel_append (rel_flatten rA) (rel_flatten rT)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.claims_walk
