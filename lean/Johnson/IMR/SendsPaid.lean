-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsPaid.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): TWO OF Johnson/IMR/SendsJoin.lean's DEBTS PAID AT THE TERM NAMED FOR THE LETTER sn (Johnson/Desc/K12/Door/SentAtPlace.lean:
snAt Z G ps j: what the sub-protocol at the place number j of the list ps sends, off the public part and the ground alone):
  calm_snAt         the field «calm»: by that file's snAt_calm.
  k7Block_calm · sends_k7   the field «first» AT l = 24: K7's place's own sub-protocol (the head's front, then the reply's sub-protocol) sends nothing: by headFrontQ_codes | headFrontQ_size | headFrontQ_book (Johnson/Top/H0/Tw/K2C/) and k7Of_quiet (Johnson/Goal/Meaning/RecK7.lean).
  debts_at_snAt     SO: SendDebts at sn := snAt Z Bs.G₀ placesW FROM FIVE DEBTS, «first» at l < 24 alone: 24 + 51 + 25 + 25 + 3 = 128 numbers stay; 230 of the 358 are paid.
Compiled with the whole library. ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. The five debts. The plan's side. No soundness.
-/
import Johnson.IMR.SendsJoin
import Johnson.IMR.K7Seat
import Johnson.Desc.K12.Door.SentAtPlace
import Johnson.Goal.Meaning.RecK7
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.Tw.K2C.StillKeeps
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S kindsBeforeBatching backKinds)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

/-- **The field «calm» at the named term.** -/
theorem calm_snAt (Z : ProofFile.Pub) (G : ProofFile.Ground) : ∀ k kd, kindW k = some kd →
    senderKind kd = false → snAt Z G placesW k = [] := by
  intro k kd hk hs
  unfold kindW at hk
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hk
  refine VerifiableInference.Desc.K12.Door.snAt_calm Z G placesW k a ha ?_ ?_ ?_ <;>
    (intro e; rw [e] at hs; exact nomatch hs)

/-- K7's place's own sub-protocol: every accepting of its decision is Calm. -/
theorem k7Block_calm (X : OnBytes.Model.Verify.Public) (l : ℕ) : Decides Calm (k7Block X l) := by
  intro s rs gs t h
  obtain ⟨u, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  have hq : VerifiableInference.Desc.First.K2.headFrontQ X.H.tl s = .ok u :=
    (VerifiableInference.Desc.guarded_underR ProofFile.sameReply (fun _ => false) _).2 s _ _ u h1
  have c1 : Calm s u := ⟨VerifiableInference.Desc.First.K2.headFrontQ_codes hq,
    VerifiableInference.Desc.First.K2.headFrontQ_size hq,
    (VerifiableInference.Desc.First.K2.headFrontQ_book hq).1⟩
  have c2 : Calm u t := calm_of_enters ((Meaning.K2.k7Of_quiet X l).1 u _ _ t h2).1
  exact ⟨c2.1.trans c1.1, c2.2.1.trans c1.2.1, c2.2.2.trans c1.2.2⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The lot's own sub-protocol at K7's place sends nothing.** -/
theorem sends_k7 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := some 24, piece := 1, kind := .K7 }) :
    SendsAt ft codes [] b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨sz, -⟩ := ground_gets hS hR O.pub O.blank
  obtain ⟨x, hm, rfl⟩ := lot_K7 hL hb' (by rw [hp])
  unfold ProofFile.h1Own at hm
  rw [sz] at hm
  obtain rfl := List.mem_singleton.1 hm
  exact sends_of_calm (b := (k7Block Bs.G₀.W 24).retype) (k7Block_calm Bs.G₀.W 24)

set_option maxRecDepth 1000000 in
theorem kind_338 : kindW 338 = some .K7 := by decide +kernel

/-- **SendDebts at the named term, from five debts.** -/
theorem debts_at_snAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes} {s₀ : S}
    (first : ∀ l < 24, ∀ (k : KindName) (b' : Block S Cl),
      (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some l, piece := 1, kind := k } →
      SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + 2)) (snAt Z Bs.G₀ placesW (14 * l + 2)) b')
    (hear : ∀ l < 25, ∀ (i : ℕ) (k : KindName) (b' : Block S Cl), 1 ≤ i →
      (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k → senderKind k = true →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } →
      SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + i + 2))
        (snAt Z Bs.G₀ placesW (14 * l + i + 2)) b')
    (batch : ∀ l < 25, ∀ Lk : Link S Cl, c.links[l]? = some Lk →
      SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 2)) []
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)))
    (behind : ∀ l < 25, ∀ (Lk : Link S Cl) (b : Block S Cl), c.links[l]? = some Lk →
      b.rounds = [] → (∀ s rs gs, b.decide s rs gs = Lk.runBehind s) →
      SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (14 * l + nAt l + 3)) [] b)
    (back : ∀ (j : ℕ) (k : KindName) (b' : Block S Cl), (backKinds true)[j]? = some k →
      senderKind k = true → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := j + 1, kind := k } →
      SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ (353 + j)) (snAt Z Bs.G₀ placesW (353 + j)) b') :
    SendDebts ft codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ where
  calm := calm_snAt Z Bs.G₀
  first := by
    intro l hl k b' hk lot hp
    by_cases h24 : l < 24
    · exact first l h24 k b' hk lot hp
    · obtain rfl : l = 24 := by omega
      obtain rfl : KindName.K7 = k := Option.some.inj hk
      rw [show 14 * 24 + 2 = 338 from rfl, calm_snAt Z Bs.G₀ 338 _ kind_338 rfl]
      exact (sends_k7 hS hR O lot hp).on
  hear := hear
  batch := batch
  behind := behind
  back := back

end

end IM

#print axioms IM.calm_snAt
#print axioms IM.k7Block_calm
#print axioms IM.sends_k7
#print axioms IM.debts_at_snAt
