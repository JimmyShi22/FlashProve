-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/OmegaMemberSent.lean: Omega's member of the last chain's
test and its sender in the shared chain.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.

  `omega_data_prefix`   (i) THE SENDER's DATA AT THE PREFIX THAT IT HAD HEARD IS THE DATA AT ALL
                 THAT THE CHAIN HEARD, where the number of "LIN point" stands within the prefix
  `omega_one_input`   (ii) AT ONE RUN the Local input of a part of the last chain and the Common
                 input of a part of the shared chain have one index and one committer's values: so
                 the test's `ask` is the sender's
  `one_A`       (iii) where the six are made, the sender's public data is `sendPub`'s: one A

  `omega_data_at_sender`   (i) with `omega_data_shift` (SendersW.lean), in one statement: the
                 member's data at the moved number, at h₁ ++ h ++ e, is the sender's at the prefix h

That the stretch holds the sender's coins is (h6). No theorem here joins (i), (ii) and (iii) at one
run: that the last chain's heard is h₁ ++ h ++ e for the sender's h is the caller's.

Limits.
- ha, in (i): that "LIN point" stands within what the sender had heard is a premise. By reading it
  is payable: where the list is of the flat form `A.atPoint` is 0 (`dataOf_flat`,
  K14/DataMade.lean), and "send o_omega" stands behind that round: the length of what the sender
  had heard is a clause of `called_at_run`. Not called here.
- One weights: (ii) is at one `wt` on both sides, and (iii) shows the senders at that `wt`:
  `secondW` lays `fun w => I.weights Z w.w₀`, the filling's shared field
  `nowSharedBy (I.weights Z) Z`.
- (iii) is a lemma, not a rfl: the review's term (h1) allows either.
- (ii) is a conditional at a run, of the walk: nothing shows that `runC` returns or a part is
  called.
- `one_A` has the six's return as a premise.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.SendersW
import Johnson.Desc.ProofFile.Honest.K12.DoorOpened
import Johnson.Desc.ProofFile.Honest.K12.CalledAtSecond
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block FileDescription)
open ProofFile.Honest.K12.Light (askOf)

/-- **(i) The sender's data at a prefix is its data at the whole**, where the number of "LIN point"
stands within the prefix. -/
theorem omega_data_prefix (P : Desc.K14.P14) (a : Nat) (ask : ProofFile.Honest.K14.Ask)
    (h e : List Fmt.Drawn) (k : Nat) (ha : a < h.length) :
    (ProofFile.Honest.K14.jobOmega ⟨P, a⟩).data ⟨ask, h ++ e, ()⟩ k =
      (ProofFile.Honest.K14.jobOmega ⟨P, a⟩).data ⟨ask, h, ()⟩ k := by
  have e₁ : ((h ++ e).drop a).take 1 = (h.drop a).take 1 := by
    rw [List.drop_append_of_le_length (Nat.le_of_lt ha),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  simp only [ProofFile.Honest.K14.jobOmega, heardFrom, e₁]

/-- **The member's data is the sender's at its prefix.** -/
theorem omega_data_at_sender (P : Desc.K14.P14) (a : Nat) (ask : ProofFile.Honest.K14.Ask)
    (h₁ h e : List Fmt.Drawn) (k : Nat) (ha : a < h.length) :
    (ProofFile.Honest.K14.jobOmega ⟨P, h₁.length + a⟩).data ⟨ask, h₁ ++ (h ++ e), ()⟩ k =
      (ProofFile.Honest.K14.jobOmega ⟨P, a⟩).data ⟨ask, h, ()⟩ k := by
  rw [omega_data_shift, omega_data_prefix P a ask h e k ha]

/-- **(ii) At one run the test's `ask` is the sender's.** A called part of the last chain and a
called part of the shared chain: their stands' inputs read one index and one committer's values. -/
theorem omega_one_input {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x c = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    {V₂ Pb₂ : Type} (σ₂ : Side F.S₂ F.Cl V₂ (Common W₀ Rc Ky) X₀ Pb₂)
    (u₂ : Member V₂ (Common W₀ Rc Ky) X₀ Pb₂) (pre₂ t₂ : List (Block F.S₂ F.Cl)) (i₂ : ℕ)
    (S₂ : StandsAt F.shared.blocksInOrder R.shared σ₂ u₂ pre₂ t₂ i₂)
    (hrun : runC F Bk P w₀ rc x c ρ = .ok r) (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hc₂ : r.called ⟨σ₂.block.place, u₂.number⟩ = true) (A : ProofFile.Honest.K14.SendPub)
    (wt : W₀ → Weights) (rd : Rc → TableRand) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (m₂ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midAtW F Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      midSharedAtW F Bk P w₀ rc x c ρ ⟨σ₂.block.place, u₂.number⟩ = .ok (some m₂) ∧
      askOf A (fun w : Local W₀ Rc Xi Tr => wt w.w₀) (fun w => rd w.rc) m.st.input =
        ⟨ProofFile.Honest.K14.rowsOf A.P.S (wt m₂.st.input.w₀) (rd m₂.st.input.rc)⟩ := by
  obtain ⟨m, -, -, -, -, -, -, -, tr, hm, -, hin, -⟩ :=
    ProofFile.Honest.K12.Light.called_at_second hpl hR σ u pre t i S hrun hc
  obtain ⟨m₂, -, -, hm₂, hin₂, -⟩ :=
    ProofFile.Honest.K12.Light.fold_at_called hpl hR σ₂ u₂ pre₂ t₂ i₂ S₂ hrun hc₂
  refine ⟨m, m₂, hm, hm₂, ?_⟩
  rw [hin, hin₂]
  rfl

/-- **(iii) Where the six are made the sender's public data is `sendPub`'s.** -/
theorem one_A {W₀ : Type} (wt : W₀ → Weights) (Z : Pub)
    {six : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)}
    (h : nowSharedBy wt Z = .ok six) :
    ∃ (A : ProofFile.Honest.K14.SendPub)
      (pre : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)),
      sendPub Z = some A ∧
      six = pre ++ ProofFile.Honest.K14.proverSidesOfSharedSendings A wt fun rc : IndexCommitterCoins => randAt A.P rc := by
  unfold nowSharedBy at h
  obtain ⟨P, hP, h⟩ := ProofFile.Honest.exBind_ok h
  have hP' : p14At Z = some P := by
    cases e : p14At Z with
    | none =>
      rw [e] at hP
      cases hP
    | some p =>
      rw [e] at hP
      cases hP
      rfl
  cases hs' : onlineSharedChain Z with
  | none =>
    rw [hs'] at h
    cases h
  | some s =>
    rw [hs'] at h
    replace h : ProofFile.Honest.K14.sixOf P s.chain.blocksInOrder wt
        (fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩) = .ok six := h
    unfold ProofFile.Honest.K14.sixOf at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i d hd
        obtain rfl := Except.ok.inj h
        unfold ProofFile.Honest.K14.dataOf at hd
        obtain ⟨a, ha, hd⟩ := Option.bind_eq_some_iff.1 hd
        obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1 hd
        refine ⟨⟨P, a⟩, _, ?_, rfl⟩
        unfold sendPub sharedInFront
        rw [hP', hs']
        simp only [Option.bind_some, ha, Option.map_some]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.omega_data_prefix
#print axioms ProofFile.Honest.K12.AtProof.omega_data_at_sender
#print axioms ProofFile.Honest.K12.AtProof.omega_one_input
#print axioms ProofFile.Honest.K12.AtProof.one_A
