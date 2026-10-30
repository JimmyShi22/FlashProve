-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSmpEarnStep.lean: AN ACCEPTING STEP OF A SENDING IN THE WRAP EARNS smpY.
smpEarnAt (Johnson/Desc/K14/Law/LedgerSmpEarn.lean) says it of a piece
that holds the sending in the wrap. Its proof leaves the piece in its first two lines: it spends the
wrapped sub-protocol's own accepting step alone. HERE that step is the premise: the form that an
induction along "reached" wants. The proof is smpEarnAt's, line for line behind its first two lines.

  below_open      the wrap, opened at an accepting decision: the rounds shown are below the prime,
                  and the sub-protocol itself accepts.
  smpEarn_step    **the earning at a wrapped step.**
  smp_keep        one of the kind's eight that does not earn it hands smpY on: in the decision's
                  form.
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.LedgerSmpEarn
import Johnson.Desc.K14.Law.LedgerSmpK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Wit noDigest viewWordsBelowPrime fieldPrimeWord roundsFit foldConsOk chainAtOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt Seeds ReadsAs seedsOf cutSeeds
  decideSend decideSend_iff sendOwn condPort cond_tie seedIs_behind_len SeedIs draw_len
  cutSeeds_length)

/-- The wrap, opened at an accepting decision. -/
theorem below_open {σ Cl : Type} (b : Block σ Cl) (s s' : σ) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (below b).decide s rs gs = .ok s') :
    viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true ∧
      b.decide s rs gs = .ok s' := by
  have hB' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then
      b.decide s rs gs else .error "a word is not below the prime") = .ok s' := h
  split at hB'
  · exact ⟨by assumption, hB'⟩
  · cases hB'

/-- **An accepting step of the sending in the wrap earns smpY.** -/
theorem smpEarn_step {Cl : Type} (Q : P14) (n : String) (K : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hbk : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (rad : ℕ → ℕ) (hC : VerifiableInference.Desc.K1.condPort K rad = true)
    (k : Fin (shapesOf K).length) (hk : sampledAt K k) (hPl : PlanY K.codes (shapeAt K k))
    (c : Block St Cl) (hc : DecidesAs c (sendAt Q n K inFront groups behind))
    (hr : c.rounds = (sendAt Q n K inFront groups behind).rounds) (ft : ℕ) (s s' : St)
    (R : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (m : ℕ)
    (hst : (below c).step ft s R cols = .ok (s', m)) (k₀ j : ℕ) :
    smpY K.codes (shapeAt K k) (s.st.oracles.size + k.val) k₀ j s' = true := by
  obtain ⟨hfit, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ _ _ _ _ _ hst
  -- the rounds are the sending's two
  have hfit' : roundsFit (VerifiableInference.Desc.K1.rounds K) R =
      true := by
    have e : (below c).rounds = VerifiableInference.Desc.K1.rounds K := hr
    rw [← e]
    exact hfit
  -- the wrap's test, and the sending's own yes
  have hview := (below_open c s s' _ gs hdec).1
  have hyes := (below_open c s s' _ gs hdec).2
  rw [hc] at hyes
  simp only [sendAt, Block.inside] at hyes
  obtain ⟨t, ht, hyes⟩ := ebind_ok hyes
  cases ht
  obtain ⟨t', ht', hyes⟩ := ebind_ok hyes
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx2, rfl⟩ := emap_ok ht'
  obtain ⟨e1, _, _⟩ := hbk _ _ _ (named_some hyes)
  obtain ⟨r₁, r₂, hrs⟩ := decideSend_two K none _ _ _ hx2
  rw [hrs] at hx2 hview
  -- what the first round draws
  obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ q₂, R = [q₁, q₂] := by
    cases hl : R with
    | nil => rw [hl] at hrs; cases hrs
    | cons q₁ l =>
      cases l with
      | nil => rw [hl] at hrs; cases hrs
      | cons q₂ l =>
        cases l with
        | nil => exact ⟨q₁, q₂, rfl⟩
        | cons _ _ => rw [hl] at hrs; cases hrs
  rw [hq] at hrs hfit'
  obtain ⟨rfl, rfl⟩ : noDigest q₁ = r₁ ∧ noDigest q₂ = r₂ := by
    have := List.cons.inj hrs
    exact ⟨this.1, (List.cons.inj this.2).1⟩
  have hlen : ((noDigest q₁).drawn.elems.map E.ofTriple).length = K.seeds * (K.coordinates + 1) :=
    draw_len K q₁ q₂ hfit'
  have hokE : ∀ t ∈ (noDigest q₁).drawn.elems, okE (E.ofTriple t) = true := by
    intro t ht
    unfold viewWordsBelowPrime at hview
    simp only [Bool.and_eq_true, List.all_eq_true] at hview
    exact okE_of_below t (by
      have := (hview.1 (noDigest q₁) List.mem_cons_self).1 t ht
      simpa [Bool.and_eq_true] using this)
  obtain ⟨⟨_, _, hnz, _, _⟩, _, _⟩ := (decideSend_iff K none _ x2 _ _ ids).1 hx2
  obtain ⟨ρ, hρ⟩ := reads_of_ok K (noDigest q₁) hokE hnz
  obtain ⟨yy, hS⟩ := seedIs_behind_len K rad none _ x2 _ _ ids hC hlen hx2 ρ hρ k hk
  obtain ⟨xo, hxo, hokS⟩ := ok_of_seedIs (cond_tie K rad hC k hk) hPl hS
  refine (smpY_iff _ _ _ _ _ _).2 (Or.inr ⟨xo, ?_, hokS⟩)
  rw [e1]
  exact hxo


/-- One of the kind's eight hands smpY on, where it is not the one that earns it. -/
theorem smp_keep (cs : Codes) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (i : ℕ) (b : Block St Unit)
    (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : b.decide d rs gs = .ok d') (sh : OracleShape)
    (o k₀ : ℕ) (hne : i + 1 ≠ k₀) (h : smpY cs sh o k₀ (i + 1) d = true) :
    smpY cs sh o k₀ (i + 2) d' = true := by
  by_cases h3 : i + 2 ≤ k₀
  · exact (smpY_iff _ _ _ _ _ _).2 (Or.inl h3)
  have ks := Fence.keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) _ _ rs gs
    hd
  obtain ⟨x0, h1, _⟩ := ((smpY_iff _ _ _ _ _ d).1 h).resolve_left (by omega)
  exact smpOfPart _ _ _ _ (i + 1) (i + 2) (by omega) d d'
    (ks.2.2 _ (Array.getElem?_eq_some_iff.1 h1).1) h

end Desc.K14.Law

#print axioms Desc.K14.Law.below_open
#print axioms Desc.K14.Law.smpEarn_step
#print axioms Desc.K14.Law.smp_keep
