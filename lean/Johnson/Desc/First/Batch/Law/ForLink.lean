-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ForLink.lean
(kind K9's soundness lemma): THEOREMS: what the law of a whole segment asks of the
batching's block ("BatchAdds"), in that law's shape, at any state T with K9's lens.
The segment's law speaks in letters (rd, fixed, chi, ready, good, later, wsum, one), which the kinds
fill together. Here:
  batchAdds_shape   the shape itself, for ANY letters, from two facts on them: (h1) what the draw
                    lays is good, has the fixed part of the state in front and holds the element
                    drawn; (h2) at a good state that still holds it, the adding gives what that law
                    concludes (a letter C here). The rest is batch_step.
  oneK, wvK, wsumK  K9's own filling of three letters: the ledger's value in the state s, read at
                    the state t; a claim's value with its weight, read at t; their sum.
  oneK_wsumK        (h2)'s equation at this filling: from addAll_total.
f, the function of claims, is any function.

-/
import Johnson.Desc.First.Batch.Law.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where batch drawnClean ledgerEmpty)

variable {T P K : Type}

/-- **The shape that the segment's law asks of the batching's block.** C s₂ s' x cls: what that law
concludes of the state s₂ that f returned, the state s' behind the block, the element drawn and the
claims: any proposition. -/
theorem batchAdds_shape (Xl : Lens T) (p : Where) (f : T → Except String (List Claim × T))
    (ft : Nat) (rd : Fmt.Ext → K) (fixed : T → P) (chi : T → K) (ready good : T → Prop)
    (C : T → T → Fmt.Ext → List Claim → Prop)
    (h1 : ∀ s a o x, ready s → Xl.get? s = some a →
      drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o →
      good (Xl.set s { a with owed := o.owed, L := o.L, F := o.F }) ∧
        fixed (Xl.set s { a with owed := o.owed, L := o.L, F := o.F }) = fixed s ∧
        chi (Xl.set s { a with owed := o.owed, L := o.L, F := o.F }) = rd x)
    (h2 : ∀ s₂ b G cls x, good s₂ → chi s₂ = rd x → Xl.get? s₂ = some b →
      addAll b.F cls = some G → C s₂ (Xl.set s₂ { b with F := G }) x cls) :
    ∀ s rs cols s' k, ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
      (batch Xl p f).step ft s rs cols = .ok (s', k) →
      ∃ x s₁ cls s₂, rs.flatMap (·.drawn.elems) = [x] ∧ good s₁ ∧ fixed s₁ = fixed s ∧
        chi s₁ = rd x ∧ f s₁ = .ok (cls, s₂) ∧ (good s₂ → chi s₂ = rd x → C s₂ s' x cls) := by
  intro s rs cols s' k hr _ h
  obtain ⟨r, x, a, o, cls, s₂, b, G, rfl, hx, ha, ho, hf, hb, hG, rfl⟩ :=
    batch_step Xl p f ft s rs cols s' k h
  obtain ⟨g1, g2, g3⟩ := h1 s a o x hr ha ho
  exact ⟨x, _, cls, s₂, by simp [hx], g1, g2, g3, hf, fun hg hc => h2 s₂ b G cls x hg hc hb hG⟩

variable [CommRing K] (Xl : Lens T) (ρ : Reading K)

/-- The ledger's value in the state s, what it speaks of read at the state t. -/
def oneK (t s : T) (y : Bound K) : K :=
  match Xl.get? t, Xl.get? s with
  | some a, some b => b.F.total ρ (worldAt ρ a.L a.F y)
  | _, _ => 0

/-- The value of the claim cl as claim number j, with its weight, read at the state t. -/
def wvK (t : T) (y : Bound K) (c : K) (j : ℕ) (cl : Claim) : K :=
  match Xl.get? t with
  | some a => c ^ expo a.F.planClaimsF j cl * claimValue ρ (worldAt ρ a.L a.F y) cl
  | none => 0

/-- The claims of a list as the claims number n, n + 1, ..: the sum. -/
def wsumK (t : T) (y : Bound K) (c : K) : ℕ → List Claim → K
  | _, [] => 0
  | n, cl :: l => wvK Xl ρ t y c n cl + wsumK t y c (n + 1) l

theorem wsumK_eq (t : T) (a : K9.Part) (h : Xl.get? t = some a) (y : Bound K) (c : K) :
    ∀ (l : List Claim) (n : ℕ),
      wsumK Xl ρ t y c n l = claimsSum ρ (worldAt ρ a.L a.F y) c a.F.planClaimsF n l
  | [], _ => rfl
  | cl :: l, n => by
    rw [wsumK, wsumK_eq t a h y c l (n + 1)]
    simp only [wvK, h, claimsSum, sumFrom]

/-- **The one equation behind the adding is the sum of the claims**, both read at a state t that has
the plan's number of claims of the ledger at which they were added. That ledger: empty; no claim
counted; one coefficient for each slot. (The draw's tests K9.ledger-empty and K9.no-claim-yet give
the first two at the ledger that the draw lays: drawnClean_ok; that the runs of claims keep them is
the runs' to show.) -/
theorem oneK_wsumK (t s' : T) (a b' : K9.Part) (F : Fork) (cls : List Claim) (y : Bound K)
    (ht : Xl.get? t = some a) (hs : Xl.get? s' = some b') (he : ledgerEmpty F = true)
    (hn : F.nClaim = 0) (hz : F.LS.size = F.ns) (hp : a.F.planClaimsF = F.planClaimsF)
    (hadd : addAll F cls = some b'.F) :
    oneK Xl ρ t s' y = wsumK Xl ρ t y (ρ.val F.theta) 0 cls := by
  rw [wsumK_eq Xl ρ t a ht]
  simp only [oneK, ht, hs]
  rw [(addAll_total ρ _ cls F b'.F hz hadd).1, total_of_empty ρ _ F he, zero_add, hn, hp]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.batchAdds_shape
#print axioms VerifiableInference.Desc.K9L.oneK_wsumK
