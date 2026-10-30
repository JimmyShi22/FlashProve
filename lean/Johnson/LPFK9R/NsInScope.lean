-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/NsInScope.lean: THE PLAN's TERM FOR "THE OPEN LEDGER's TWO NUMBERS" (`nsZ Z nH`,
SlotsSeat.lean: read off the frames' letters) IS, IN THE GOALS' SCOPE AND AT nH := THE HEAD's PLAN's
NUMBER OF SLOTS, THE BUILT SEGMENT's OWN NUMBER OF SLOTS, TWICE: AT ALL 25 SEGMENTS. Statements and
proofs.

  `zip_ns`: an entry of the built segments with their routines exchanged has the kind, the group and
    the number of slots of the entry that it stems from.
  `ns_even`, `ns_odd`, `ns_24`: the term at a layers' segment, an attention segment, the head's.
  `ns_in_scope`: **m < 25 ⊢ nsZ Z Z.p.X.H.ns m = (n, n), n := ((Z.p.built.links[m]?).map
    (·.ns)).getD 0.**
The stones: `IM.ground_named` (kinds and groups), `IM.ground_tails` (each built segment's number of
slots is its plan's), both at the blank letters' built list.
Limits. No soundness statement.

-/
import Johnson.LPFK9R.SlotsSeat
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open Johnson.Desc.First.Walk.Seat (frameAt zeroAt)

theorem zip_ns {bs ls : Array LinkH} {j : ℕ} {Y : LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.kind = b.kind ∧ Y.g = b.g ∧ Y.ns = b.ns := by
  rw [Array.getElem?_zipWith] at h
  cases hb : bs[j]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hx : ls[j]? with
    | none =>
      rw [hx] at h
      cases h
    | some y =>
      rw [hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl, rfl⟩

/-- A layers' segment. -/
theorem ns_even {built : Array LinkH} {W : Verify.Public} {m g : ℕ} {b : LinkH}
    {hp : Layer.HPlan2} (hb : built[m]? = some b) (hk : b.kind = 0) (hg : b.g = g)
    (hG : W.G[g]? = some hp) (nH : ℕ) : nsW built W nH m = hp.ns := by
  unfold nsW
  by_cases h0 : m = 0
  · subst h0
    rw [if_pos rfl]
    unfold zeroAt
    simp [hb, hk, hg, hG]
  · rw [if_neg h0]
    unfold frameAt
    simp [hb, hk, hg, hG, h0]

/-- An attention segment. -/
theorem ns_odd {built : Array LinkH} {W : Verify.Public} {m g : ℕ} {b : LinkH}
    {a : Attention.Plan} (hb : built[m]? = some b) (h0 : m ≠ 0) (hk : b.kind = 1) (hg : b.g = g)
    (hA : W.A[g]? = some a) (nH : ℕ) : nsW built W nH m = a.ns := by
  unfold nsW
  rw [if_neg h0]
  unfold frameAt
  simp [hb, hk, hg, hA, h0]

/-- The head's segment. -/
theorem ns_24 {built : Array LinkH} {W : Verify.Public} {m : ℕ} {b : LinkH}
    (hb : built[m]? = some b) (h0 : m ≠ 0) (hk : b.kind = 2) (nH : ℕ) :
    nsW built W nH m = nH := by
  unfold nsW
  rw [if_neg h0]
  unfold frameAt
  simp [hb, hk, h0]

/-- **AT ALL 25.** -/
theorem ns_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) {m : ℕ} (hm : m < 25) :
    nsZ Z Z.p.X.H.ns m = (((Z.p.built.links[m]?).map (·.ns)).getD 0,
      ((Z.p.built.links[m]?).map (·.ns)).getD 0) := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built hG
  have eW : G₀.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have key : nsW Z.p.built.links Z.p.X Z.p.X.H.ns m =
      ((Z.p.built.links[m]?).map (·.ns)).getD 0 := by
    by_cases h24 : m = 24
    · subst h24
      obtain ⟨l, f, k, _⟩ := (IM.ground_named hS hR hZ hG).2
      obtain ⟨l', f', _, _, _, hn, _⟩ := (IM.ground_tails hS hR hZ hG).2
      obtain rfl : l = l' := Option.some.inj (f.symm.trans f')
      rw [e] at f
      obtain ⟨b, hb, b1, _, b3⟩ := zip_ns f
      rw [ns_24 hb (by omega) (b1.symm.trans k), hb]
      show Z.p.X.H.ns = b.ns
      rw [← b3, hn, eW]
    · obtain ⟨l, l', f, k, g1, _, f', k', g1', _⟩ :=
        (IM.ground_named hS hR hZ hG).1 (m / 2) (by omega)
      obtain ⟨hp, a, y, y', hGg, hAg, q, _, _, _, n1, _, q', _, _, _, n2⟩ :=
        (IM.ground_tails hS hR hZ hG).1 (m / 2) (by omega)
      obtain rfl : l = y := Option.some.inj (f.symm.trans q)
      obtain rfl : l' = y' := Option.some.inj (f'.symm.trans q')
      rw [eW] at hGg hAg
      rcases Nat.mod_two_eq_zero_or_one m with ev | od
      · have em : 2 * (m / 2) = m := by omega
        rw [em, e] at f
        obtain ⟨b, hb, b1, b2, b3⟩ := zip_ns f
        rw [ns_even hb (b1.symm.trans k) (b2.symm.trans g1) hGg, hb]
        show hp.ns = b.ns
        rw [← b3, n1]
      · have em : 2 * (m / 2) + 1 = m := by omega
        rw [em, e] at f'
        obtain ⟨b, hb, b1, b2, b3⟩ := zip_ns f'
        rw [ns_odd hb (by omega) (b1.symm.trans k') (b2.symm.trans g1') hAg, hb]
        show a.ns = b.ns
        rw [← b3, n2]
  show (nsW Z.p.built.links Z.p.X Z.p.X.H.ns m, nsW Z.p.built.links Z.p.X Z.p.X.H.ns m) = _
  rw [key]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.zip_ns
#print axioms VerifiableInference.Desc.LinkJoin.ns_even
#print axioms VerifiableInference.Desc.LinkJoin.ns_odd
#print axioms VerifiableInference.Desc.LinkJoin.ns_24
#print axioms VerifiableInference.Desc.LinkJoin.ns_in_scope
