-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/AddBound.lean: THE BATCHING's OWN YES BOUNDS THE NUMBER OF CLAIMS THAT
IT ADDS: AT MOST THE PLAN's NUMBER. No Ok, no fixed part, no table of lengths. Statements and
proofs.

Why it is so. A claim is added under the next weight (`addClaim`, Johnson/Desc/Claim.lean, by
`Fork.kap`); the weight of claim number c is handed out by `Fork.kapTake` (OnBytes/Model/Hide.lean),
  which, ONCE THE MAP OF HANDED-OUT WEIGHTS IS SET UP, refuses unless c is below the plan's number.
  The description's own batching draw (`K9.drawn`, Johnson/Desc/First/Batch/Kind.lean) sets that map
  up, with one place for each claim of the plan, and refuses a plan of no claims.

  `kap_bound`: a weight handed out where the map has the plan's number of places, not 0: the claims'
    number was below the plan's; it goes up by one; the plan's number and the map's size stay.
  `addClaim_bound`: so one claim added. `addAll_bound`: **so a list: addAll F l = some G; the map
    has the plan's number of places; that number is not 0; F.nClaim ≤ F.planClaimsF ⊢ F.nClaim +
    l.length ≤ F.planClaimsF.** (The last premise is needed at the empty list.)
  `drawn_kap`: behind a yes of the draw: the map has the plan's number of places; that number is not
    0, and is the number in front; no claim is added yet.
  `KeepsKap X g`: THE PREMISE ON THE GATHERER: what g does to the state between the draw and the
    adding leaves the open ledger's map's size, the plan's number and the claims' number.
  `batch_bound`: **a block whose yes is the draw's yes and then the adding of what g returns
    (`DrawMoves X p [.add g] b`); KeepsKap X g; a yes of its step at s ⊢ g returns some (c, e₁) at
    the state behind the draw, and c.length ≤ a.F.planClaimsF**, a the part at s.
Limits. `KeepsKap X g` IS A PREMISE: it is shown of no gatherer here. WITHOUT IT NOTHING IS BOUNDED:
a run that emptied the map would switch the refusal off. No soundness statement.
-/
import Johnson.Desc.First.Batch.Law.Moves
import Johnson.Desc.First.Batch.Law.RowsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where drawnClean drawn Drawn)

/-- A weight handed out where the map is set up. -/
theorem kap_bound {F G : Fork} {k : E} (h : F.kap = some (k, G))
    (hm : F.kapMapF.size = F.planClaimsF) (h0 : F.planClaimsF ≠ 0) :
    F.nClaim < F.planClaimsF ∧ G.nClaim = F.nClaim + 1 ∧ G.planClaimsF = F.planClaimsF ∧
      G.kapMapF.size = F.kapMapF.size := by
  have he : F.kapMapF.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff]
    intro e
    rw [e] at hm
    exact h0 hm.symm
  simp only [Fork.kap, Option.map_eq_some_iff] at h
  obtain ⟨⟨k', F'⟩, hx, e⟩ := h
  unfold Fork.kapTake at hx
  split at hx
  · exact nomatch hx
  · split at hx
    · rename_i _ hE
      rw [he] at hE
      exact nomatch hE
    · split at hx
      · rename_i hc
        obtain ⟨k'', _, e2⟩ := Option.map_eq_some_iff.1 hx
        obtain rfl : { F with kapMapF := F.kapMapF.set! F.nClaim true } = F' :=
          congrArg Prod.snd e2
        obtain rfl := congrArg Prod.snd e
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨hc.1.1, rfl, rfl, by simp⟩
      · exact nomatch hx

theorem push_kap (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) :
    G.nClaim = F.nClaim ∧ G.kapMapF = F.kapMapF := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rw [← Option.some.inj h]
      exact ⟨rfl, rfl⟩
    · simp at h

/-- One claim added. -/
theorem addClaim_bound {F G : Fork} {cl : Claim} (h : addClaim F cl = some G)
    (hm : F.kapMapF.size = F.planClaimsF) (h0 : F.planClaimsF ≠ 0) :
    F.nClaim < F.planClaimsF ∧ G.nClaim = F.nClaim + 1 ∧ G.planClaimsF = F.planClaimsF ∧
      G.kapMapF.size = F.kapMapF.size := by
  have hp := addClaim_plan F G cl h
  simp only [addClaim, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k0, F1⟩, hk, k, _, F2, hp2, h3⟩ := h
  obtain ⟨b1, b2, _, b4⟩ := kap_bound hk hm h0
  obtain ⟨c1, c2⟩ := push_kap F1 F2 k cl.form hp2
  have hG : G.nClaim = F2.nClaim ∧ G.kapMapF = F2.kapMapF := by
    unfold Fork.pushRuns at h3
    simp only [Option.map_eq_some_iff] at h3
    obtain ⟨tr, _, rfl⟩ := h3
    exact ⟨rfl, rfl⟩
  exact ⟨b1, by rw [hG.1, c1, b2], hp, by rw [hG.2, c2, b4]⟩

/-- **A LIST OF CLAIMS ADDED.** -/
theorem addAll_bound : ∀ (l : List Claim) (F G : Fork), addAll F l = some G →
    F.kapMapF.size = F.planClaimsF → F.planClaimsF ≠ 0 → F.nClaim ≤ F.planClaimsF →
    F.nClaim + l.length ≤ F.planClaimsF
  | [], _, _, _, _, _, hn => hn
  | cl :: l, F, G, h, hm, h0, _ => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, hq, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b1, b2, b3, b4⟩ := addClaim_bound hq hm h0
    have ih := addAll_bound l F1 G h2 (by rw [b4, b3]; exact hm) (by rw [b3]; exact h0)
      (by rw [b2, b3]; exact b1)
    rw [b2, b3] at ih
    rw [List.length_cons]
    omega

/-- Behind a yes of the draw. -/
theorem drawn_kap {rows : ℕ} {chi : E} {owed : Option ℕ} {used : ℕ} {L : LinkCtx} {F : Fork}
    {o : Drawn} (h : drawnClean rows chi owed used L F = .ok o) :
    o.F.kapMapF.size = o.F.planClaimsF ∧ o.F.planClaimsF ≠ 0 ∧ o.F.nClaim = 0 ∧
      o.F.planClaimsF = F.planClaimsF := by
  obtain ⟨_, _, d3, d4, _⟩ := drawnClean_ok _ _ _ _ _ _ _ h
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, hc, ho⟩ := ok_bind ho
  have hc' : F.planClaimsF ≠ 0 := by simpa using need_ok hc
  have e := Except.ok.inj ho
  refine ⟨?_, by rw [d4]; exact hc', d3, d4⟩
  rw [d4, ← e]
  simp

variable {T : Type}

/-- **THE PREMISE ON THE GATHERER.** -/
def KeepsKap (X : Lens T) (g : T → Except String (List Claim × T)) : Prop :=
  ∀ e c e₁ a, g e = .ok (c, e₁) → X.get? e = some a → ∀ a₁, X.get? e₁ = some a₁ →
    a₁.F.kapMapF.size = a.F.kapMapF.size ∧ a₁.F.planClaimsF = a.F.planClaimsF ∧
      a₁.F.nClaim = a.F.nClaim

/-- **THE BATCHING's OWN YES.** -/
theorem batch_bound {Cl : Type} (X : Lens T)
    (hX : ∀ s a, (X.get? s).isSome = true → ∃ a', X.get? (X.set s a) = some a' ∧ a'.F = a.F)
    (p : Where) (g : T → Except String (List Claim × T)) (b : Block T Cl)
    (hb : DrawMoves X p [.add g] b) (hg : KeepsKap X g) {ft : ℕ} {s : T} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {s' : T} {k : ℕ}
    (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ r x a o c e₁, rs = [r] ∧ r.drawn.elems = [x] ∧ X.get? s = some a ∧
      drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o ∧
      g (X.set s { a with owed := o.owed, L := o.L, F := o.F }) = .ok (c, e₁) ∧
      c.length ≤ a.F.planClaimsF := by
  obtain ⟨r, x, a, o, cls, e1, e2, ha, ho, hy⟩ := hb ft s rs cols s' k h
  obtain ⟨u, c, c', ⟨e₁, s₁, G, hge, hs₁, hG, _⟩, _, _⟩ := hy
  obtain ⟨a₀, ha₀, hF⟩ := hX s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have hF' : a₀.F = o.F := hF
  obtain ⟨k1, k2, k3, k4⟩ := drawn_kap ho
  obtain ⟨q1, q2, q3⟩ := hg _ c e₁ a₀ hge ha₀ s₁ hs₁
  rw [hF'] at q1 q2 q3
  have B := addAll_bound c s₁.F G hG (by rw [q1, q2]; exact k1) (by rw [q2]; exact k2)
    (by rw [q3, k3]; exact Nat.zero_le _)
  rw [q3, k3, q2, k4] at B
  exact ⟨r, x, a, o, c, e₁, e1, e2, ha, ho, hge, by omega⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.kap_bound
#print axioms VerifiableInference.Desc.K9L.push_kap
#print axioms VerifiableInference.Desc.K9L.addClaim_bound
#print axioms VerifiableInference.Desc.K9L.addAll_bound
#print axioms VerifiableInference.Desc.K9L.drawn_kap
#print axioms VerifiableInference.Desc.K9L.batch_bound
