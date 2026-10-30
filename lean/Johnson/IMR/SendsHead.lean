-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsHead.lean, OVER ANOTHER SET OF THIS PROJECT's LEAN FILES: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): THE DEBT SendsOn AT THE HEAD's LINK's BATCHING (347) AND THE SUB-PROTOCOL BEHIND IT (348): THEY SEND NOTHING: by hear_runs24 (Johnson/IMR/HeadRest.lean: a light cut of Johnson/IMR/GroupHead.lean), called; its premise «the
link's second hearing sub-protocol (K2's, number 339) accepts somewhere» from «reached». AND THE SUM: 332 OF THE 358 NUMBERS PAID OUTRIGHT · K2's 25 UNDER K2Fences · ONE NUMBER STAYS: THE PROXIMITY TEST (354).
  hear_accepts      at a state reached behind a hearing place, that place's sub-protocol's decision has accepted somewhere.
  sends_batch24 · sends_behind24   the two debts.
  debts_one · seats_one   Johnson/IMR/SendsAll.lean's debts_three | seats_three without batch24 |
                          behind24.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. K2Fences · k12 (354) · the plan's test sendsAreB: A PREMISE HERE (a run is said to have evaluated it at three sets of public files: not held by this file's writer, and not in this library; in scope, by theorem: typed by nobody). No soundness.
-/
import Johnson.IMR.SendsAll
import Johnson.IMR.HeadRest

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- At a state reached behind a hearing place, that place's sub-protocol's decision has accepted somewhere. -/
theorem hear_accepts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ s : S} {l i j : ℕ}
    (hl : l < 25) (hj : 14 * l + i + 2 < j) (hg : ReachedAt ft c.blocksInOrder s₀ j s) {Lk : Link S Cl}
    (e1 : c.links[l]? = some Lk) :
    ∀ b₀, Lk.hear[i]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
  intro b₀ e0
  have hix := hear_at_flat e1 e0
  rw [flatIx_scope hS hR O (by omega) i] at hix
  obtain ⟨u, rs, cols, u', n, hy⟩ := reached_accepts hg (i := 14 * l + i + 2) hj hix
  exact ⟨u, _, _, u', (VerifiableInference.Desc.step_inv ft b₀ u u' rs cols n hy).2.2.2⟩

/-- **THE HEAD's LINK's BATCHING (347).** -/
theorem sends_batch24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes} {s₀ : S}
    {Lk : Link S Cl} (e1 : c.links[24]? = some Lk) :
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ 347) []
      (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order)) := by
  intro s s' rs cols n hg hy hc
  have hy1 := hear_accepts hS hR O (l := 24) (i := 1) (by omega) (by omega) hg e1
  obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, -, -⟩ := (k9_of hS hR O).2 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans eL')
  have hruns := Meaning.K2.hear_runs24 calmG_refl calmG_trans calmG_of_quiet hS hR O e1 hy1
  exact ((sends_of_calmG (calmG_batch p
    (Meaning.K2.link_claims_runs calmG_refl calmG_trans Lk hruns))).under (alone_underR (hal _)))
    s s' rs cols n hy hc

/-- **THE SUB-PROTOCOL BEHIND IT (348).** -/
theorem sends_behind24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes} {s₀ : S}
    {Lk : Link S Cl} {b : Block S Cl} (e1 : c.links[24]? = some Lk)
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    SendsOn ft codes (ReachedAt ft c.blocksInOrder s₀ 348) [] b := by
  intro s s' rs cols n hg hy hc
  have hy1 := hear_accepts hS hR O (l := 24) (i := 1) (by omega) (by omega) hg e1
  have hruns := Meaning.K2.hear_runs24 calmG_refl calmG_trans calmG_of_quiet hS hR O e1 hy1
  exact (sends_of_calmG (b := b) fun u rs' gs' t h =>
    Meaning.K2.link_behind_runs calmG_refl calmG_trans Lk hruns u t (by rw [← hd u rs' gs']; exact h))
    s s' rs cols n hy hc

/-- **THE SUM.** -/
theorem debts_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ : S}
    (K : K2Fences ft Z Bs.G₀ c s₀)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder s₀ 354) (snAt Z Bs.G₀ placesW 354) b') :
    SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ :=
  debts_three hS hR O K (fun _ e1 => sends_batch24 hS hR O e1)
    (fun _ _ e1 _ hd => sends_behind24 hS hR O e1 hd) k12

/-- **THE TOP.** -/
theorem seats_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} (p : ProofFile.InstPub)
    (K : K2Fences ft Z Bs.G₀ c (ProofFile.startS Z p))
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn ft Z.first.codes (ReachedAt ft c.blocksInOrder (ProofFile.startS Z p) 354)
        (snAt Z Bs.G₀ placesW 354) b')
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_under_test hS hR O p (debts_one hS hR O K k12) hu hB hLd hk hf

end

end IM

#print axioms IM.hear_accepts
#print axioms IM.sends_batch24
#print axioms IM.sends_behind24
#print axioms IM.debts_one
#print axioms IM.seats_one
