-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrownJoin.lean. The field «batch» asks Hands at the chain's own link's batching block at the link's own gatherer. Asked of K9.batch K9.atS p g at every gatherer g it could not be paid: the state behind the batching is built on what g returns, and a free g returns what it will: s1_of_shares would be true as stated, with a premise that nobody can pay. nAt stands in Johnson/IMR/WrittenList.lean.
THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: THE
JOIN: (S1) AT onlineDescription's FIRST CHAIN, IN THE GOALS' SCOPE, FROM TEN SHARES, EACH IN ITS OWN
CONSTANTS.
A RULE OVER SHARES: IT PAYS NOTHING BY ITSELF. What it does: it walks all 358 blocks of c.blocksInOrder by this folder's seats and shows that NOTHING ELSE IS OWED than the ten.
ON WORDS: «the state» is the value of type S that the description's fold carries from block to block (earlier files of this folder call it «the record»).
OBJECT. S1 N linksW E ft c (Johnson/IMR/HandsDef.lean), c onlineDescription's first chain. USER. Whoever spends (S1); every kind's files that have a share to pay.
LETTERS. N · E · ft as in Johnson/IMR/HandsDef.lean; Z · Bs · c as in Johnson/IMR/SeatOpen.lean's
Open; nAt l: the number of a link's blocks in front of its batching (9 at l = 24, else 7).

  Shares N E ft Z G₀ c   THE TEN:
    front     (1 block: number 0)    a sentence on the table alone: X 0 s → X 1 s.
    laid      (25: 14 l + 1)         every block without a round whose yes is layFront l's yes, with no mark behind it and the reply as it was.
    first     (25: 14 l + 2)         every block that is Joined of a lot's block at (1, some l, 1, k): the lot's block with the link's own row's «opened» behind it (hands_joined takes the two stages).
    hear      (152: 14 l + i + 2, 1 ≤ i)   THE LOT's OWN BLOCK at (1, some l, i + 1, k). (block_by_place, Johnson/IMR/LinkSeat.lean: a kind's files name it by their own term.)
    batch     (25: 14 l + nAt l + 2) the chain's own link's batching block AT THE LINK's OWN GATHERER: Lk.batch (claimsInBy Lk.each Lk.hear Lk.order). (batch_of_lot: whoever has Hands of K9's own K9.batch K9.atS p at that gatherer has the field.)
    behind    (25: 14 l + nAt l + 3) every block without a round whose decision is the link's runBehind.
    close     (75: 14 l + nAt l + 4 + j)   (K9.closeOf p Q)[j], carried over.
    cleared   (25: 14 l + nAt l + 7) every block without a round whose yes is the link's own row's clear's yes, with no mark behind it and the reply as it was.
    back      (4: 353 + j)           THE LOT's OWN BLOCK at (1, none, j + 1, k).
    last      (1: 357)               the seal: chainEnd 1 5 true …, carried over.
  s1_of_shares      in scope: Shares → S1 N linksW E ft c.

1 + 25 + 25 + 152 + 25 + 25 + 75 + 25 + 4 + 1 = 358.
What is not claimed. NO SHARE IS PAID HERE. (S0). The promise's other half. From a piece's «out a τ = some b» to the block's step. Nothing at an o other than secondHashFunction. No soundness.
-/
import Johnson.IMR.GrownBK
import Johnson.IMR.TableW
import Johnson.IMR.PlacesScope
import Johnson.IMR.SealSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers kindsBeforeBatching closeKinds backKinds)
open ProofFile (Cl)

/-- **THE TEN SHARES.** -/
structure Shares (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : Chain S Cl) : Prop where
  front : ∀ s, s.failed = none → XK N linksW placesW E 0 s = true → XK N linksW placesW E 1 s = true
  laid : ∀ l < 25, ∀ b : Block S Cl, b.rounds = [] →
    (∀ s rs gs t, b.decide s rs gs = .ok t →
      Johnson.Desc.First.Walk.layFront l s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) →
    Hands N linksW placesW E ft (14 * l + 1) b
  first : ∀ l < 25, ∀ (k : KindName) (b b' : Block S Cl),
    (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := 1, kind := k } →
    Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := k } →
    Hands N linksW placesW E ft (14 * l + 2) b
  hear : ∀ l < 25, ∀ (i : ℕ) (k : KindName) (b' : Block S Cl), 1 ≤ i →
    (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } →
    Hands N linksW placesW E ft (14 * l + i + 2) b'
  batch : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk →
    Hands N linksW placesW E ft (14 * l + nAt l + 2)
      (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order))
  behind : ∀ l < 25, ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[l]? = some Lk → b.rounds = [] →
    (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
    Hands N linksW placesW E ft (14 * l + nAt l + 3) b
  close : ∀ l < 25, ∀ p Q j (x : Block S Unit), k9At Z l = some p →
    ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q →
    (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x →
    Hands N linksW placesW E ft (14 * l + nAt l + 4 + j) x.retype
  cleared : ∀ l < 25, ∀ fs f (b : Block S Cl),
    Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs → fs[l]? = some f →
    b.rounds = [] →
    (∀ s rs gs t, b.decide s rs gs = .ok t →
      f.clear s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) →
    Hands N linksW placesW E ft (14 * l + nAt l + 7) b
  back : ∀ (j : ℕ) (k : KindName) (b' : Block S Cl), (backKinds true)[j]? = some k →
    (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := none, piece := j + 1, kind := k } →
    Hands N linksW placesW E ft (353 + j) b'
  last : Hands N linksW placesW E ft 357
    ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
      VerifiableInference.Desc.First.endAsks : Block S Unit).retype : Block S Cl)

/-- No block in front of a batching is of the kind K9 or K10. -/
theorem hear_kinds_plain {sub : ModelPart} {f : Bool} {i : ℕ} {k : KindName}
    (h : (kindsBeforeBatching sub f)[i]? = some k) : k ≠ KindName.K9 ∧ k ≠ KindName.K10 := by
  have hm := List.mem_of_getElem? h
  constructor <;> rintro rfl <;> revert hm <;> cases sub <;> cases f <;> decide

/-- Chain.blocksInOrder's «hasNoClaimsAndNothingAfter» turns the test on the plan alone: the step is the block's. -/
theorem under_bare {b b' : Block S Cl} (h : b.UnderR b') :
    ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl).UnderR b' := h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- The field «batch», from Hands of K9's own block at the link's own gatherer. -/
theorem batch_of_lot (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {ft : ℕ}
    (h : ∀ l < 25, ∀ (Lk : Link S Cl) p, c.links[l]? = some Lk → k9At Z l = some p →
      Hands N linksW placesW E ft (14 * l + nAt l + 2)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
          (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order))) :
    ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk →
      Hands N linksW placesW E ft (14 * l + nAt l + 2)
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro l hl Lk e1
  obtain ⟨Lk9, p, -, -, e9, hp, -, -, -, -, hal, -⟩ := (k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
  exact (h l hl Lk p e1 hp).under (alone_underR (hal _))

/-- **THE JOIN: (S1) AT onlineDescription's FIRST CHAIN, IN SCOPE, FROM THE TEN SHARES.** -/
theorem s1_of_shares (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {ft : ℕ} (Sh : Shares N E ft Z Bs.G₀ c) : S1 N linksW E ft c := by
  apply s1_of_hands
  rw [places_scope hS hR O]
  intro k b hb
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  have hk : k < 358 := hlen ▸ (List.getElem?_eq_some_iff.1 hb).1
  have hcase : k = 0 ∨ (∃ l j, l < 25 ∧ j < nAt l + 7 ∧ k = 14 * l + 1 + j) ∨
      (∃ j, j < 4 ∧ k = 353 + j) ∨ k = 357 := by
    by_cases h0 : k = 0
    · exact Or.inl h0
    by_cases h1 : k ≤ 336
    · refine Or.inr (Or.inl ⟨(k - 1) / 14, (k - 1) % 14, by omega, ?_, by omega⟩)
      unfold nAt
      rw [if_neg (by omega)]
      omega
    by_cases h2 : k ≤ 352
    · exact Or.inr (Or.inl ⟨24, k - 337, by omega, by unfold nAt; rw [if_pos rfl]; omega, by omega⟩)
    by_cases h3 : k ≤ 356
    · exact Or.inr (Or.inr (Or.inl ⟨k - 353, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  rcases hcase with rfl | ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl
  · -- the front
    have h := front_hands (ft := ft) O (N := N) (links := linksW) (E := E)
      (by rw [places_scope hS hR O]; exact Sh.front) b hb
    rw [places_scope hS hR O] at h
    exact h
  · -- a link
    obtain ⟨-, fs, hfs, hall⟩ := frame_of hS hR O
    obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, hlayf, hLay, hClear, iL, rL, dL, iB, rB, dB, iC, rC,
      dC⟩ := hall l hl
    have hn' : Lk.hear.length = nAt l := hn
    have hsub := subs_scope hS hR O l hl
    have hj' : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ nAt l) ∨ j = nAt l + 1 ∨ j = nAt l + 2 ∨
        (∃ q, q < 3 ∧ j = nAt l + 3 + q) ∨ j = nAt l + 6 := by
      by_cases a : j ≤ nAt l + 2
      · omega
      · by_cases a2 : j ≤ nAt l + 5
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j - (nAt l + 3), by omega, by omega⟩)))))
        · omega
    rcases hj' with rfl | rfl | ⟨j2, jn⟩ | rfl | rfl | ⟨q, hq, rfl⟩ | rfl
    · -- «laid»
      obtain rfl : bL = b := Option.some.inj (iL.symm.trans hb)
      refine Sh.laid l hl bL rL fun s rs gs t hy => ?_
      rw [dL] at hy
      have h := (hLay s t).1 hy
      rw [hlayf] at h
      exact h
    · -- the first place
      obtain ⟨k0, hk0⟩ : ∃ k0, (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k0 := by
        cases (subAt l) <;> cases (l == 0) <;> exact ⟨_, rfl⟩
      obtain ⟨Lk', b0, e1', e2, L, hL, b', hb', ep, hjn⟩ := first_sits hS hR O l hl k0 hk0
      have hix := hear_at_flat e1' e2
      rw [flatIx_scope hS hR O (by omega) 0] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      exact Sh.first l hl k0 b0 b' hk0 ⟨L, hL, hb'⟩ ep hjn
    · -- a block in front of the batching, behind the first place
      obtain ⟨Lk9, -, -, -, e9, -, -, -, -, -, -, -, -, -, -, -, -, hlen9, -⟩ := (k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      obtain ⟨k1, hk1⟩ : ∃ k1, (kindsBeforeBatching (subAt l) (l == 0))[j - 1]? = some k1 :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hlen9, hn']; omega)⟩
      obtain ⟨h9, h10⟩ := hear_kinds_plain hk1
      have hn9 : nAt l ≤ 9 := by unfold nAt; split <;> omega
      obtain ⟨Lk', b0, e1', e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
        chain_hear_alone O.made O.places O.chain l (subAt l) hsub (j - 1) k1 hk1 h9 h10
          ⟨by omega, by omega⟩
      have hix := hear_at_flat e1' e2
      rw [flatIx_scope hS hR O (by omega) (j - 1),
        show 14 * l + (j - 1) + 2 = 14 * l + 1 + j by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      have h := Sh.hear l hl (j - 1) k1 b' (by omega) hk1 ⟨L, hL, hb'⟩ ep
      rw [show 14 * l + (j - 1) + 2 = 14 * l + 1 + j by omega] at h
      exact h.under (alone_underR hla)
    · -- the batching
      obtain ⟨Lk9, p, -, -, e9, hp, -, -, -, -, hal, i9, -⟩ := (k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      rw [hn', show 14 * l + nAt l + 2 = 14 * l + 1 + (nAt l + 1) by omega] at i9
      obtain rfl := Option.some.inj (i9.symm.trans hb)
      have h := Sh.batch l hl Lk e1
      rw [show 14 * l + nAt l + 2 = 14 * l + 1 + (nAt l + 1) by omega] at h
      exact h
    · -- behind the batching
      rw [hn', show 14 * l + nAt l + 3 = 14 * l + 1 + (nAt l + 2) by omega] at iB
      obtain rfl : bB = b := Option.some.inj (iB.symm.trans hb)
      have h := Sh.behind l hl Lk bB e1 rB dB
      rw [show 14 * l + nAt l + 3 = 14 * l + 1 + (nAt l + 2) by omega] at h
      exact h
    · -- the closing's three
      obtain ⟨LkC, p, Q, eC, hp, hQ, hcl⟩ := close_of hS hR O l hl
      obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
      obtain ⟨kq, hkq⟩ : ∃ kq, closeKinds[q]? = some kq :=
        ⟨_, List.getElem?_eq_getElem (by show q < 3; exact hq)⟩
      obtain ⟨b0, x, e2, ex, hla⟩ := hcl q kq hkq
      have hix := close_numbers hS hR O hl e1 e2
      rw [hn', show 14 * l + nAt l + 4 + q = 14 * l + 1 + (nAt l + 3 + q) by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      have h := Sh.close l hl p Q q x hp hQ ex
      rw [show 14 * l + nAt l + 4 + q = 14 * l + 1 + (nAt l + 3 + q) by omega] at h
      exact h.under (alone_underR hla)
    · -- «cleared»
      rw [hn', show 14 * l + nAt l + 7 = 14 * l + 1 + (nAt l + 6) by omega] at iC
      obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
      have h := Sh.cleared l hl fs f bC hfs hf rC fun s rs gs t hy => by
        rw [dC] at hy
        exact (hClear s t).1 hy
      rw [show 14 * l + nAt l + 7 = 14 * l + 1 + (nAt l + 6) by omega] at h
      exact h
  · -- behind the links
    obtain ⟨-, -, -, hallB⟩ := base_made O.made
    obtain ⟨several, hsev, -, hbk⟩ := chain_back_any hallB (makers_K9 Z Bs.G₀) O.places O.chain
    obtain rfl : several = true := hsev.2 (base_has_K13 O)
    obtain ⟨kj, hkj⟩ : ∃ kj, (backKinds true)[j]? = some kj :=
      ⟨_, List.getElem?_eq_getElem (by show j < 4; exact hj)⟩
    have hk9 : kj ≠ KindName.K9 := by
      have hm := List.mem_of_getElem? hkj
      rintro rfl
      revert hm
      decide
    obtain ⟨b0, e0, sp, -, L, hL, b', hb', -, ep, hla⟩ := hbk j kj hkj hk9
    have hix := (back_numbers hS hR O).1 j b0 e0
    obtain rfl := Option.some.inj (hix.symm.trans hb)
    exact (Sh.back j kj b' hkj ⟨L, hL, hb'⟩ ep).under (under_bare (alone_underR hla))
  · -- the seal
    obtain ⟨b', -, rfl, hla⟩ := seal_seated O
    have hix := (back_numbers hS hR O).2
    obtain rfl := Option.some.inj (hix.symm.trans hb)
    exact Sh.last.under (under_bare (alone_underR hla))

end

end IM

#print axioms IM.batch_of_lot
#print axioms IM.s1_of_shares
