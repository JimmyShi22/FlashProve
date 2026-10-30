--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPublic.lean: THE CLAUSES ON PUBLIC VALUES AND ON THE CARRIED CODES THAT THE KEY FILE's THIRD
CHAIN's START ASKS, from theorems that the library has already. Calls, and the ties of variables
that the calls want. Statements and proofs. On the verifier's own tests on public values and on what
its steps write: NOTHING IS SHOWN OF ANY PROVER.

What is shown.
  `KeyNamed.of_eq`: `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean) reads X, N, P through the IOP as
    written in Lean (below: the description) alone: it passes to any X', N', P' with the same
    description.
  `KeySourced Z X N P`: `KeyNamed`, AND X, N, P ARE WHAT THE LIBRARY's THREE READERS OF THE MAKER's
    ANSWER RETURN at Z's public files (`sourceOf`, `rangesNumbers`, `laterPlaces`).
    **`key_sourced`**: where the IOP's own test on the public files accepts there are such X, N, P:
      by the library's
    `descOfMade_is` (Johnson/Desc/Key/SlotIs.lean). The library's facts on public values speak of
    these readers' values.
  `third_public`: from the description's test on its own rounds alone: the table's shape is lawful
    at the sized key's codes, and it does not split the row (Dot): the first sub-protocol of the
    third chain asks both among its tests on public values.
  **`codes_tie`**: under `KeySourced`: the first chain's codes are the sized key's: by the library's
    `five_at` (Johnson/RunOne/Law/KeyInScope.lean).
  **`sized_sourced`**, **`five_sourced`**: IN SCOPE, under `KeySourced`: the sized key is the
    library's written value (`Lk6.AtPlan.keyFull`), and the first chain's five public values (the
    setting, the ranges' parameters, the shape of the test on the table, the index masks' notice,
    the codes) are that value's: calls of the library's `key_in_scope` and `five_in_scope`.
  `fold_codes`: a fold over sub-protocols under which a statement only grows, where it has accepted,
    leaves the codes as they were. **`codes_first`**, **`codes_shared`**: so behind any accepted
    fold over sub-protocols of the first | the shared chain, from that chain's first state, the
    carried codes are the sized key's (the first: under `KeySourced`).

So of the nine clauses of `Start₃` (E2E/KeyStartThird.lean) four are had at the chains' ends of any
accepted run: lawful, arm, codes₁, codes₂; a fifth (tested) is E2E/KeyEnds.lean's.

Limits.
- "Accepted" is a premise: nothing on whether a step accepts.
- The library's files on "a statement only grows" at the key file are not reviewed.


-/
import E2E.KeyPasses
import E2E.KeyStartThird
import Johnson.RunOne.KeyCodesLater
import Johnson.Desc.PlanPasses
import Johnson.RunOne.KeyPayD
import Johnson.RunOne.Law.KeyInScope

set_option autoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open VerifiableInference.Desc (FileDescription Block Grows foldBlocks OpenedColumn)
open VerifiableInference.Desc.Key (descriptionFromPlan descAt sourceOf madeAt fixedDigest)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Ground (By)
open Johnson.RunOne.KeyKeeps (st₁ st₂)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

section
variable {Z : PublicFiles} {X X' : VerifiableInference.Desc.Key.Source} {N N' : H2U.PlaceNums}
  {P P' : VerifiableInference.Desc.Key.LaterPlaces}

/-- It reads X, N, P through the description alone. -/
theorem KeyNamed.of_eq (h : KeyNamed Z X N P) (e : keyFileDescription X N P = keyFileDescription X' N' P') :
    KeyNamed Z X' N' P' :=
  ⟨e ▸ h.named, e ▸ h.plan, e ▸ h.wanted, e ▸ h.owed, e ▸ h.data, h.depth, e ▸ h.run⟩

/-- **X, N, P are what the key file's description at Z is made of, and they are what the library's
three readers of the maker's answer return there.** A member: `key_sourced`. -/
structure KeySourced (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) : Prop where
  named : KeyNamed Z X N P
  source : ∃ X₀ m,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
    madeAt X₀ Z.lay fixedDigest = .ok m ∧ sourceOf m = .ok X ∧
    VerifiableInference.Desc.Key.rangesNumbers m = .ok N ∧
    VerifiableInference.Desc.Key.laterPlaces m = .ok P

/-- **Where the test on the public files accepts, there are such X, N, P.** -/
theorem key_sourced (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ X N P, KeySourced Z X N P := by
  obtain ⟨X, N, P, hn⟩ := key_named Z live
  obtain ⟨X₀, m, h0, hm, hd, -⟩ := hn.named
  have hd' : descriptionFromPlan m = .ok (keyFileDescription X N P) := by
    unfold descAt at hd
    rw [hm] at hd
    exact hd
  obtain ⟨X', N', P', hX, hN, hP, e⟩ := VerifiableInference.Desc.Key.descOfMade_is m _ hd'
  exact ⟨X', N', P', hn.of_eq e, X₀, m, h0, hm, hX, hN, hP⟩

/-- **The two clauses on public values alone**, from the description's test on its own rounds. -/
theorem third_public (hp : (keyFileDescription X N P).planOk = true) :
    (X.chains.made.sized.key.codes.lengthsOk &&
        linOk X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape) = true ∧
      VerifiableInference.Desc.Third.plainArm X.chains.made.sized.key.once.shape = true := by
  have hm : ∃ b ∈ (keyFileDescription X N P).second.blocksInOrder, b.planOk = true →
      (X.chains.made.sized.key.codes.lengthsOk &&
        linOk X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape &&
        VerifiableInference.Desc.Third.plainArm X.chains.made.sized.key.once.shape) = true :=
    ⟨_, List.mem_cons_self .., fun h => by
      have h1 : (keyFileDescription X N P).second.first.planOk = true := (Bool.and_eq_true_iff.1 h).1
      have h2 : ((X.chains.made.sized.key.codes.lengthsOk &&
          linOk X.chains.made.sized.key.codes X.chains.made.sized.key.once.shape &&
          VerifiableInference.Desc.Third.plainArm X.chains.made.sized.key.once.shape) && true &&
          true) = true := h1
      simpa only [Bool.and_true] using h2⟩
  obtain ⟨b, hb, hk⟩ := hm
  have t := hk ((VerifiableInference.Desc.Keeps.planOk_blocks _ hp).2.2 b hb)
  exact Bool.and_eq_true_iff.1 t

/-- **The first chain's codes are the sized key's.** -/
theorem codes_tie (h : KeySourced Z X N P) :
    X.Y.k.oneTime.codes = X.chains.made.sized.key.codes := by
  obtain ⟨X₀, m, -, hm, hX, -, -⟩ := h.source
  have e1 : X.chains = m.p.chains := (Johnson.RunOne.KeyPay.pubsOf_ok hX).1
  rw [e1]
  exact (Johnson.RunOne.Law.SourceIs.five_at hm hX h.named.plan).2.2.2.2

/-- **In scope the sized key is the library's written value.** -/
theorem sized_sourced (h : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    X.chains.made.sized.key = Lk6.AtPlan.keyFull := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := h.source
  have e1 : X.chains = m.p.chains := (Johnson.RunOne.KeyPay.pubsOf_ok hX).1
  rw [e1]
  exact Johnson.RunOne.Law.KeyInScope.key_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm

/-- **In scope the first chain's five public values are the written value's**: the setting, the
ranges' parameters, the shape of the test on the table, the index masks' notice, the codes. -/
theorem five_sourced (h : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    X.set = Lk6.AtPlan.keyFull.set ∧ X.Y.k.oneTime.ranges = Lk6.AtPlan.keyFull.ranges.x ∧
      X.Y.k.oneTime.lin = Lk6.AtPlan.keyFull.once.shape ∧
      X.Y.k.oneTime.indexMasks = Lk6.AtPlan.keyFull.once.input ∧
      X.Y.k.oneTime.codes = Lk6.AtPlan.keyFull.codes := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := h.source
  exact Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX h.named.plan

end

/-- A fold over sub-protocols under which a statement only grows leaves the codes as they were. -/
theorem fold_codes {S Cl : Type} (st : S → Statement) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, Decides (By Grows st) b) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft bs s rs cols = .ok r) :
    (st r.1).codes = (st s).codes :=
  (VerifiableInference.Desc.Keeps.foldBlocks_keeps (By Grows st) (fun _ => Grows.refl _)
    (fun _ _ _ a b => Grows.trans a b) ft bs hb s rs cols r h).1

section
variable {Z : PublicFiles} {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **Behind an accepted fold over sub-protocols of the first chain, from its first state, the
carried codes are the sized key's.** -/
theorem codes_first (hs : KeySourced Z X N P)
    (bs : List (Block (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl))
    (hb : ∀ b ∈ bs, b ∈ (keyFileDescription X N P).first.blocksInOrder) (ft : Nat) (x : KeyInst) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : (keyFileDescription X N P).S₁ × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs ((keyFileDescription X N P).start₁ ((keyFileDescription X N P).pub x)) rs cols = .ok r) :
    (st₁ (show VerifiableInference.Desc.Key.FirstState from r.1)).codes =
      X.chains.made.sized.key.codes := by
  have t := fold_codes (S := VerifiableInference.Desc.Key.FirstState) st₁ bs
    (fun b hbb => VerifiableInference.Desc.Keeps.chain_flat_keeps (By Grows st₁)
      (fun _ => Grows.refl _) (fun _ _ _ a c => Grows.trans a c) _
      Johnson.RunOne.KeyCodes.first_grows b (hb b hbb)) ft _ rs cols r h
  exact t.trans (codes_tie hs)

/-- **The same of the shared chain.** No premise on X. -/
theorem codes_shared (bs : List (Block (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl))
    (hb : ∀ b ∈ bs, b ∈ (keyFileDescription X N P).shared.blocksInOrder) (ft : Nat) (x : KeyInst) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (r : (keyFileDescription X N P).S₂ × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs ((keyFileDescription X N P).start₂ ((keyFileDescription X N P).pub x)) rs cols = .ok r) :
    (st₂ (show _root_.Desc.K14.St from r.1)).codes = X.chains.made.sized.key.codes :=
  fold_codes (S := _root_.Desc.K14.St) st₂ bs
    (fun b hbb => VerifiableInference.Desc.Keeps.chain_flat_keeps (By Grows st₂)
      (fun _ => Grows.refl _) (fun _ _ _ a c => Grows.trans a c) _
      Johnson.RunOne.KeyCodes.shared_growsBy b (hb b hbb)) ft _ rs cols r h

end

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.KeyNamed.of_eq
#print axioms AtPublicFiles.AtFiles.key_sourced
#print axioms AtPublicFiles.AtFiles.third_public
#print axioms AtPublicFiles.AtFiles.codes_tie
#print axioms AtPublicFiles.AtFiles.sized_sourced
#print axioms AtPublicFiles.AtFiles.five_sourced
#print axioms AtPublicFiles.AtFiles.fold_codes
#print axioms AtPublicFiles.AtFiles.codes_first
#print axioms AtPublicFiles.AtFiles.codes_shared
