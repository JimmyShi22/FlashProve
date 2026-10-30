-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsFences.lean, OVER ANOTHER SET OF THIS PROJECT's LEAN FILES: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre» (Johnson/Desc/Sound/SmpPlaces.lean): THE JOIN: K2Fences (Johnson/IMR/SendsK2.lean) IS PAID, IN THE GOALS' SCOPE, AT ft := 0 AND s₀ := ProofFile.startS Z p, BY fence1_link · fence1_head · fence1_finish (Johnson/IMR/MsgsBehind.lean):
THREE CALLS. SO 357 OF THE 358 NUMBERS ARE PAID OUTRIGHT: 280 THAT SEND NOTHING AND 77 OF THE 78 SENDERS; ONE STAYS: THE PROXIMITY TEST (354).
  k2Fences_paid     K2Fences 0 Z Bs.G₀ c (ProofFile.startS Z p).
  debts_354 · seats_354   Johnson/IMR/SendsHead.lean's debts_one | seats_one without K2Fences.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
What is not claimed. k12 (354) · the plan's test sendsAreB: a premise here (a run is said to have evaluated it at three sets of public files: not held by this file's writer; in scope, by theorem: typed by nobody) · «the first state bears no mark». No soundness.
-/
import Johnson.IMR.SendsHead
import Johnson.IMR.MsgsBehind

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

/-- **THE THREE SENTENCES ON REACHED STATES, PAID.** -/
theorem k2Fences_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub) :
    K2Fences 0 Z Bs.G₀ c (ProofFile.startS Z p) where
  link := fun l hl s hg Pp n a nm st hP hn hst => by
    obtain ⟨rs, cols, r, hf, rfl⟩ := hg
    exact Meaning.Carry.fence1_link hS hR O hl (f₀ := hf) hP hn a nm st hst
  head := fun s hg Pp n a nm st hP hn hst => by
    obtain ⟨rs, cols, r, hf, rfl⟩ := hg
    exact Meaning.Carry.fence1_head hS hR O (f₀ := hf) hP hn a nm st hst
  finish := fun s hg Pp n a nm m hP hn hm => by
    obtain ⟨rs, cols, r, hf, rfl⟩ := hg
    exact Meaning.Carry.fence1_finish hS hR O (f₀ := hf) hP hn a nm hm

/-- **THE SUM.** -/
theorem debts_354 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn 0 Z.first.codes (ReachedAt 0 c.blocksInOrder (ProofFile.startS Z p) 354)
        (snAt Z Bs.G₀ placesW 354) b') :
    SendDebts 0 Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p) :=
  debts_one hS hR O (k2Fences_paid hS hR O p) k12

/-- **THE TOP.** -/
theorem seats_354 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      SendsOn 0 Z.first.codes (ReachedAt 0 c.blocksInOrder (ProofFile.startS Z p) 354)
        (snAt Z Bs.G₀ placesW 354) b')
    (hu : (ProofFile.startS Z p).failed = none) {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    VerifiableInference.Desc.K12.Door.atFirstSeats Ld out.1 = true ∧
      VerifiableInference.Desc.placesAre Ld.places out.1.st out.1.book = true :=
  seats_one hS hR O p (k2Fences_paid hS hR O p) k12 hu hB hLd hk hf

end

end IM

#print axioms IM.k2Fences_paid
#print axioms IM.debts_354
#print axioms IM.seats_354
