-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Ledger.lean
(kind K9's soundness lemma): THEOREMS: (T1), the algebra of the ledger.
  addClaim_total   adding a claim (Johnson/Desc/Claim.lean: addClaim) adds chi ^ exponent * the
                   claim's value to the ledger's value (Fork.total), in every world under every
                   reading; what else of the ledger changes, and what does not.
  addAll_total     the same for a list of claims: the sum.
  t1               (T1) of Law/Statements.lean holds of addClaim.
  total_of_empty   a ledger that passes the test ledgerEmpty has the value 0 in every world.
  total_of_sums    two ledgers with the same sums (Measure.lean) have the same value in every world.
  addAll_sizes     the adding changes neither the number of coefficients LS nor the number of slots.
CARRIED from the library: Fork.kap_spec, Fork.push_total (OnBytes/Model/HideLaws.lean) and
Fork.pushRuns_total (OnBytes/Model/TreesLaws.lean). New: the weight chi ^ (n + first).
The sums with powers of chi are identities at the one element chi of the ledger; a claim's value may
itself depend on chi. Nothing where a step refuses. No count, no probability.

-/
import OnBytes.Iop.RowLaws
import Johnson.Desc.First.Batch.Law.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (ledgerEmpty)

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- **One claim.** -/
theorem addClaim_total (F G : Fork) (cl : Claim) (hs : F.LS.size = F.ns)
    (h : addClaim F cl = some G) :
    G.total ρ W = F.total ρ W +
        ρ.val F.theta ^ expo F.planClaimsF F.nClaim cl * claimValue ρ W cl ∧
      G = { F with trees := G.trees, LS := G.LS, c0 := G.c0, nClaim := F.nClaim + 1,
                   kapMapF := G.kapMapF } ∧
      G.LS.size = G.ns ∧ treesFrame G.trees = treesFrame F.trees := by
  simp only [addClaim, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k0, F1⟩, hk, k, hkk, F2, hp, h3⟩ := h
  obtain ⟨hk0, hF1, _, _⟩ := Fork.kap_spec F F1 k0 hk
  have hkv : ρ.val k = ρ.val F.theta ^ expo F.planClaimsF F.nClaim cl := by
    unfold expo
    cases he : cl.eqFirst with
    | none =>
      rw [he] at hkk
      have e : k0 = k := by simpa using hkk
      show ρ.val k = ρ.val F.theta ^ F.nClaim
      rw [← e, hk0, ρ.pow]
    | some first =>
      rw [he] at hkk
      show ρ.val k = ρ.val F.theta ^ (F.planClaimsF + first)
      by_cases hlt : F.nClaim < F.planClaimsF
      · have e : powE F.theta (F.planClaimsF + first) = k := by simpa [hlt] using hkk
        rw [← e, ρ.pow]
      · simp [hlt] at hkk
  have hs1 : F1.LS.size = F1.ns := by rw [hF1]; exact hs
  obtain ⟨t2, hF2, hs2, fr2⟩ := Fork.push_total ρ W F1 F2 k cl.form hs1 hp
  obtain ⟨t3, hG, fr3⟩ := Fork.pushRuns_total ρ W F2 G k cl.runs h3
  have t1 : F1.total ρ W = F.total ρ W := by rw [hF1]; rfl
  have tr1 : F1.trees = F.trees := by rw [hF1]
  have eLS : G.LS = F2.LS := by rw [hG]
  have eC0 : G.c0 = F2.c0 := by rw [hG]
  have eK : G.kapMapF = F1.kapMapF := by rw [hG, hF2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [t3, t2, t1, hkv, claimValue]
    ring
  · rw [eLS, eC0, eK]
    calc G = { F2 with trees := G.trees } := hG
      _ = _ := by rw [hF2, hF1]
  · rw [hG]; exact hs2
  · rw [fr3, fr2, tr1]

/-- **A list of claims.** -/
theorem addAll_total : ∀ (l : List Claim) (F G : Fork), F.LS.size = F.ns → addAll F l = some G →
    G.total ρ W = F.total ρ W + claimsSum ρ W (ρ.val F.theta) F.planClaimsF F.nClaim l ∧
      G = { F with trees := G.trees, LS := G.LS, c0 := G.c0, nClaim := F.nClaim + l.length,
                   kapMapF := G.kapMapF } ∧
      G.LS.size = G.ns ∧ treesFrame G.trees = treesFrame F.trees
  | [], F, G, hs, h => by
    have hF : F = G := by simpa [addAll] using h
    subst hF
    exact ⟨by simp [claimsSum, sumFrom], rfl, hs, rfl⟩
  | cl :: l, F, G, hs, h => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    cases hq : addClaim F cl with
    | none => simp [hq] at h
    | some F1 =>
      rw [hq] at h
      have h2 : addAll F1 l = some G := by simpa [addAll] using h
      obtain ⟨t1, e1, s1, f1⟩ := addClaim_total ρ W F F1 cl hs hq
      obtain ⟨t2, e2, s2, f2⟩ := addAll_total l F1 G s1 h2
      have hθ : F1.theta = F.theta := by rw [e1]
      have hn : F1.nClaim = F.nClaim + 1 := by rw [e1]
      have hp : F1.planClaimsF = F.planClaimsF := by rw [e1]
      have hlen : F1.nClaim + l.length = F.nClaim + (cl :: l).length := by
        rw [hn, List.length_cons]; omega
      refine ⟨?_, ?_, s2, f2.trans f1⟩
      · rw [t2, t1, hθ, hn, hp]
        simp only [claimsSum, sumFrom]
        ring
      · rw [hlen] at e2
        calc G = _ := e2
          _ = _ := by rw [e1]

/-! ## What the adding leaves alone, with no premise on sizes -/

theorem push_sizes (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) :
    G.LS.size = F.LS.size ∧ G.ns = F.ns := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h2
      exact ⟨OnBytes.foldlM_keeps Array.size (Fork.pushSlot w F.ns) (fun x b b' hb => by
        unfold Fork.pushSlot at hb
        split at hb
        · rw [← Option.some.inj hb, Array.size_modify]
        · simp at hb) _ _ _ h2, rfl⟩
    · simp at h

theorem addClaim_sizes (F G : Fork) (cl : Claim) (h : addClaim F cl = some G) :
    G.LS.size = F.LS.size ∧ G.ns = F.ns := by
  simp only [addClaim, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k0, F1⟩, hk, k, _, F2, hp, h3⟩ := h
  obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k0 hk
  obtain ⟨p1, p2⟩ := push_sizes F1 F2 k cl.form hp
  have hG : G.LS = F2.LS ∧ G.ns = F2.ns := by
    unfold Fork.pushRuns at h3
    simp only [Option.map_eq_some_iff] at h3
    obtain ⟨tr, _, rfl⟩ := h3
    exact ⟨rfl, rfl⟩
  have q1 : F1.LS = F.LS := by rw [hF1]
  have q2 : F1.ns = F.ns := by rw [hF1]
  exact ⟨by rw [hG.1, p1, q1], by rw [hG.2, p2, q2]⟩

/-- The adding changes neither the number of coefficients nor the number of slots. -/
theorem addAll_sizes : ∀ (l : List Claim) (F G : Fork), addAll F l = some G →
    G.LS.size = F.LS.size ∧ G.ns = F.ns
  | [], F, G, h => by
    have hF : F = G := by simpa [addAll] using h
    subst hF
    exact ⟨rfl, rfl⟩
  | cl :: l, F, G, h => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    cases hq : addClaim F cl with
    | none => simp [hq] at h
    | some F1 =>
      rw [hq] at h
      have h2 : addAll F1 l = some G := by simpa [addAll] using h
      obtain ⟨a1, a2⟩ := addClaim_sizes F F1 cl hq
      obtain ⟨b1, b2⟩ := addAll_sizes l F1 G h2
      exact ⟨b1.trans a1, b2.trans a2⟩

/-- **(T1) holds of addClaim.** -/
theorem t1 : T1 addClaim :=
  ⟨fun _ _ ρ W F G cl hs h => addClaim_total ρ W F G cl hs h,
    { thetaDrawnF := true }, {}, by
      simp [addClaim, Fork.kap, Fork.kapTake, Fork.kapAt, Fork.push, Fork.pushRuns]⟩

/-! ## The ledger before the first claim -/

/-- A ledger that passes ledgerEmpty has the value 0 in every world. -/
theorem total_of_empty (F : Fork) (h : ledgerEmpty F = true) : F.total ρ W = 0 := by
  simp only [ledgerEmpty, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨hT, hL⟩, hc⟩ := h
  have z : ∀ v : E, isZeroE v = true → ρ.val v = 0 := fun v hv => by
    rw [isZeroE_eq hv, ρ.zero]
  have a : treesValue ρ W F.trees = 0 := by
    unfold treesValue
    apply sumFrom_eq_zero
    intro t X hX
    unfold HTree.value
    apply sumFrom_eq_zero
    intro r R hR
    unfold HRow.value
    apply sumFrom_eq_zero
    intro i v hv
    rw [z v (hT X (Array.mem_toList_iff.mp hX) R (Array.mem_toList_iff.mp hR) v
      (Array.mem_toList_iff.mp hv)), zero_mul]
  have b : slotsValue ρ W F.LS = 0 := by
    unfold slotsValue
    apply sumFrom_eq_zero
    intro j v hv
    rw [z v (hL v (Array.mem_toList_iff.mp hv)), zero_mul]
  rw [Fork.total, a, b, z _ hc]
  simp

/-! ## What of a ledger its value reads -/

theorem sumFrom_map {α β : Type} (f : α → β) (g : Nat → β → K) :
    ∀ (l : List α) (s : Nat), sumFrom g s (l.map f) = sumFrom (fun i x => g i (f x)) s l
  | [], _ => rfl
  | x :: l, s => by simp only [List.map_cons, sumFrom, sumFrom_map f g l (s + 1)]

/-- The arrays' value, read off the weights L and their first columns alone. -/
theorem treesValue_skel (trees : Array HTree) :
    treesValue ρ W trees =
      sumFrom (fun t (rows : Array (Array E × Nat)) =>
        sumFrom (fun r (p : Array E × Nat) =>
          sumFrom (fun i v => ρ.val v * W.entry t r i) p.2 p.1.toList) 0 rows.toList) 0
        (trees.map fun X => X.rows.map fun r => (r.L, r.L0)).toList := by
  simp only [Array.toList_map, sumFrom_map]
  rfl

/-- **Two ledgers with the same sums have the same value in every world.** -/
theorem total_of_sums (G H : Fork) (h : sums H = sums G) : H.total ρ W = G.total ρ W := by
  simp only [sums, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, _⟩ := h
  rw [Fork.total, Fork.total, treesValue_skel, treesValue_skel, h1, h2, h3]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.total_of_sums
#print axioms VerifiableInference.Desc.K9L.addClaim_total
#print axioms VerifiableInference.Desc.K9L.addAll_total
#print axioms VerifiableInference.Desc.K9L.addAll_sizes
#print axioms VerifiableInference.Desc.K9L.t1
#print axioms VerifiableInference.Desc.K9L.total_of_empty
