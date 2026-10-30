-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerNineTenAtRow.lean: THE JOIN OF THE PROXIMITY TEST's OWN FACTS AT THE
SUB-PROTOCOLS 9 AND 10 TO THE SHARED CHAIN's ROW AS THE LEDGER's TOP CUTS IT, AT THE SEAT: the two
sentences of Johnson/Desc/K14/Law/LedgerNineTenAtRowOwed.lean, PROVED.
  sharedPre_nine   where the IOP's whole test on the list of rounds passes: in front of the
  proximity test on G_u stand nine sub-protocols
  nine_at_row      NineAtRowOwed, to the letter
  ten_at_row       TenAtRowOwed, to the letter
THE ROAD. NOT through K12's files' laid forms (nine_facts_laid | ten_facts_laid, NineTenAtLaid.lean:
they speak at their own "there are Z N c" and at the written data): through their GENERAL theorems
nine_facts_tile₂ | ten_facts_tile₂ (NineTenFacts.lean), called at THIS seat's own IOP and at
the letter D, as their nine_facts_at_Gu | ten_facts_at_Gomega call them at theirs. The facts on the
two places' numbers (gu_facts | gomega_facts | omega_some_in_scope) read Z and N alone in their
ends: they are had at the chain c' that k12_sits gives, along the equation of the two spellings of
onlineDescription's one value; Z and N are the same by the makers' returns. The first chain's count of trees,
which the sentences spell as the count of the messages that its sub-protocols announce, is the IOP's
own t₁: counts_of_planOk (SeamDesc.lean) with opensShaped (DataRounds.lean). So nothing
is asked on whether c' is c, or the second seat B' that of K12's files.
What is not claimed. That SeatTies has a member. No law is paid here. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerNineTenAtRowOwed
import Johnson.Loose.H2K12.NineTenAtLaid
import Johnson.Desc.K14.Law.BlocksEight
import Johnson.Desc.RunLaws
import Johnson.Desc.Sound.SeamDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker OnBytes.Flat _root_.Run _root_.Run.PQ _root_.Iop
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12
open H2K.JointK
open H2K.Member (rUFull rOFull)

/-- A list's entry, at a number that is another number. -/
theorem entry_at {α : Type} {l : List α} {n m : ℕ} {x : α} (h : l[n]? = some x) (e : n = m) :
    l[m]? = some x := e ▸ h

theorem sharedPre_nine {Xi : Type} (F : FileDescription Xi) (hp : F.planOk = true) (Cl' : Type)
    (ch : Model.Verify.Chains) (P : P14) (N : H2U.Places4)
    (hm : ∀ b ∈ blocksOr P, b.planOk = true) : (sharedPre Cl' ch P N).length = 9 := by
  cases hb : blocks P with
  | some l =>
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := blocks_len P l hb
    simp [sharedPre, blocksOr, hb]
  | none =>
    exfalso
    have hne : ∃ b ∈ blocksOr P, b.planOk = false := by
      unfold blocksOr
      rw [hb]
      exact ⟨_, List.mem_singleton.2 rfl, rfl⟩
    obtain ⟨b, hbm, hbp⟩ := hne
    rw [hm b hbm] at hbp
    cases hbp

/-- Every sub-protocol that the kind lays passes its own test, where the seated list's do. -/
theorem blocksOr_ok {Cl' : Type} (ch : Model.Verify.Chains) (P : P14) (N : H2U.Places4)
    (l : List (Block St Cl')) (post : List (Block St Cl')) (hl : l = sharedPre Cl' ch P N ++ post)
    (hk : ∀ b ∈ l, b.planOk = true) : ∀ b ∈ blocksOr P, b.planOk = true := by
  intro b hb
  have hm : (b.retype (Cl' := Cl')).asBare ∈ l := by
    rw [hl]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hb))
  have hq := hk _ hm
  simp only [Block.asBare, Block.retype, Bool.and_eq_true] at hq
  exact hq.1.1

theorem nine_at_row : NineAtRowOwed := by
  intro Cells Tok o S D r Z N B' c hT c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd h₁ h₂ h₃
  obtain ⟨hS, hL, hd, hZ, hN⟩ := hT
  obtain ⟨F, hF, hp, hD, hs, -⟩ := LPFD.Full.laidPOf_ok hL
  obtain rfl : F = (seatFF o Z N B' c) := Except.ok.inj (hF.symm.trans hd)
  have hpin := LPFD.asks_written hs
  obtain ⟨Z', N', c', -, hZ', hN', e, -⟩ := k12_sits o S.pol S.lay S.KL _ hd
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain rfl : N' = N := Except.ok.inj (hN'.symm.trans hN)
  have hp' : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := e ▸ hp
  have hpin' : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := e ▸ hpin
  obtain ⟨hfree, hC, ho, hlb, -⟩ := gu_facts o S hS Z' hZ' ProofFile.pureRoad.links N' c' hN' hp' hpin'
  obtain ⟨b', post', eb⟩ := shared_behind ProofFile.Cl (p14N Z' N') N'
  have hcut : c₂ :: k₂ = sharedPre ProofFile.Cl Z'.p.chains (p14N Z' N') N' ++
      guEntry ProofFile.Cl N' :: b' :: post' := by
    rw [← eb]
    exact h₂.symm.trans (shared_cut ProofFile.Cl _ _ N')
  have hft : (pGu N').nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N'.U hC.plan)).trans
      (H2K.Made.places_firstTree Z'.made N' hN').2.1
  have hk : ∀ b ∈ c₂ :: k₂, b.planOk = true := fun b hb =>
    (((FileDescription.planOk_ok _).1 hp).blocks₂ b (h₂ ▸ hb)).1
  have hlen := sharedPre_nine _ hp ProofFile.Cl Z'.p.chains (p14N Z' N') N'
    (blocksOr_ok Z'.p.chains (p14N Z' N') N' _ _ hcut hk)
  obtain ⟨x₀, dB, dt, hx, NF⟩ := nine_facts_tile₂ (seatFF o Z' N' B' c) "proof file" D hD hp c₁ k₁
    c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd (pGu N') rUFull
    (Seat.enter (·.gU) (·.firstMask)) Seat.leave (sharedPre ProofFile.Cl Z'.p.chains (p14N Z' N') N')
    (guEntry ProofFile.Cl N') b' post' h₂ hcut (guEntry_alike ProofFile.Cl N')
    ((guEntry_keeps ProofFile.Cl N').1.trans (H2K.Made.k12_before guardedProximityTestParts (pGu N') hC.plan)) hfree
    hC.plan hC.chain hC.joh hC.bat ho (ownLabelsB_of_free _ hlb) hft
  have hx := entry_at hx hlen
  refine ⟨(seatFF o Z' N' B' c).t₂, dB, dt, fun x hx9 => ?_⟩
  obtain rfl : x₀ = x := Option.some.inj (hx.symm.trans hx9)
  have ht : (VerifiableInference.Desc.oraclesOf (seatFF o Z' N' B' c).first.blocksInOrder).length =
      (seatFF o Z' N' B' c).t₁ :=
    (Fence.counts_of_planOk _ "proof file" D hp hD).1.trans (opensShaped _ "proof file" D hD).2.1
  rw [ht]
  exact NF

theorem ten_at_row : TenAtRowOwed := by
  intro Cells Tok o S D r Z N B' c hT c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd h₁ h₂ h₃
  obtain ⟨hS, hL, hd, hZ, hN⟩ := hT
  obtain ⟨F, hF, hp, hD, hs, -⟩ := LPFD.Full.laidPOf_ok hL
  obtain rfl : F = (seatFF o Z N B' c) := Except.ok.inj (hF.symm.trans hd)
  have hpin := LPFD.asks_written hs
  obtain ⟨Z', N', c', -, hZ', hN', e, -⟩ := k12_sits o S.pol S.lay S.KL _ hd
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain rfl : N' = N := Except.ok.inj (hN'.symm.trans hN)
  have hp' : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := e ▸ hp
  have hpin' : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := e ▸ hpin
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z' ProofFile.pureRoad.links N' c' hp' hpin'
  obtain ⟨hfree, hC, ho, hPl, -, -⟩ :=
    gomega_facts o S hS Z' hZ' ProofFile.pureRoad.links N' nO hO c' hN' hp' hpin'
  have hcut : c₂ :: k₂ = (sharedPre ProofFile.Cl Z'.p.chains (p14N Z' N') N' ++ [guEntry ProofFile.Cl N']) ++
      omegaEntry ProofFile.Cl nO :: sharedEnd ProofFile.Cl (p14N Z' N') N' :: [] :=
    h₂.symm.trans (shared_cut_omega ProofFile.Cl Z'.p.chains (p14N Z' N') N' nO hO)
  have hft : (pGomega nO).nums.firstTree = 0 :=
    (congrArg (·.firstTree) (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO hC.plan)).trans
      ((H2K.Made.places_firstTree Z'.made N' hN').2.2.1 nO hO)
  have hk : ∀ b ∈ c₂ :: k₂, b.planOk = true := fun b hb =>
    (((FileDescription.planOk_ok _).1 hp).blocks₂ b (h₂ ▸ hb)).1
  have hlen := sharedPre_nine _ hp ProofFile.Cl Z'.p.chains (p14N Z' N') N'
    (blocksOr_ok Z'.p.chains (p14N Z' N') N' _ _ (hcut.trans (List.append_assoc _ _ _)) hk)
  obtain ⟨x₀, dB, dt, hx, TF⟩ := ten_facts_tile₂ (seatFF o Z' N' B' c) "proof file" D hD hp c₁ k₁
    c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd (pGomega nO) rOFull
    (Seat.enter (·.gOmega) fun _ => none) Seat.leave
    (sharedPre ProofFile.Cl Z'.p.chains (p14N Z' N') N' ++ [guEntry ProofFile.Cl N']) (omegaEntry ProofFile.Cl nO)
    (sharedEnd ProofFile.Cl (p14N Z' N') N') [] h₂ hcut (omegaEntry_alike ProofFile.Cl nO)
    ((omegaEntry_keeps ProofFile.Cl nO).1.trans (H2K.Made.k12_before guardedProximityTestParts (pGomega nO) hC.plan))
    hfree hC.plan hC.chain hC.joh hC.bat ho hPl hft
  have hx := entry_at hx ((List.length_append).trans (congrArg (· + 1) hlen))
  refine ⟨nO, hO, (seatFF o Z' N' B' c).t₂, dB, dt, fun x hx10 => ?_⟩
  obtain rfl : x₀ = x := Option.some.inj (hx.symm.trans hx10)
  have ht : (VerifiableInference.Desc.oraclesOf (seatFF o Z' N' B' c).first.blocksInOrder).length =
      (seatFF o Z' N' B' c).t₁ :=
    (Fence.counts_of_planOk _ "proof file" D hp hD).1.trans (opensShaped _ "proof file" D hD).2.1
  rw [ht]
  exact TF

end Desc.K14.Law
