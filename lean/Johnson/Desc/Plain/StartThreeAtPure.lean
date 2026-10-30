-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/StartThreeAtPure.lean: THE PROOF FILE's DESCRIPTION `ProofFile.onlineDescription`, WHEREVER IT
IS GIVEN, IS `ProofFile.fileDescBy` AT TWO NAMED SEATS; AND WHAT A YES OF ITS LAST CHAIN's START SAYS
THERE, IN THE LETTERS OF THE RULE THAT STATES `TablesFit`'s FIELD SH₃ AT TEXTS. Statements with their proofs.

  `pAt Z`: the last chain's public parameters at the public part Z: THE TERM p AT THE SEAT.
  `seatedAt o Z N c`: `fileDescBy` at the shared seat `sharedSeatOf …` and the second seat
    `P2Third.secondSeatOf Z N`, at get := the identity, at a first chain c.
  `pureTail_cut`, `pureZ_cut`, **`descPure_cut`**: onlineDescription o pol lay KL = .ok G gives Z, N, c with:
    the public part is Z; the plan gives kind K12's four places N; G = seatedAt o Z N c. NO PREMISE
    BUT onlineDescription's RETURN.
  `ended_at`, `start_at`: at that value the shared seat's `ended` is `Desc.K14.ended` and the
    second seat's `start` is `startAtEnds (pAt Z)`: by rfl.
  **`hmark_at`**, **`hstart_at`**: at start₃ := the value's own start as the rule of composition
    takes it, and at any reader g of (public part, first record) whose second half is the record:
    a yes gives "no mark"; a yes gives "the shared chain has ended at some e, and s is
    startAtEnds (pAt Z) q (the record) e".
Limits. Facts on the description's text. Nothing on any block; nothing on whether the start ever
says yes. A laying of instances (`FileDescription.pull`) leaves start₃ as it is, by rfl: not used here.
NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.Desc.Plain.StartThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Third (S₃ P₁₄ startAtEnds)
open Desc.K14 (St sharedSeatOf sharedSeatAt beforePointOf)

/-- The last chain's public parameters at the seat. -/
def pAt (Z : Pub) : P₁₄ :=
  VerifiableInference.Desc.Third.p₁₄Z Z.p.chains.made.sized.proof.set
    Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch

/-- The shared seat at the public part and kind K12's places. -/
abbrev sharedAt (Z : Pub) (N : H2U.Places4) : SharedSeat :=
  sharedSeatOf Z.p.chains (beforePointOf N) (fun _ => VerifiableInference.Desc.K12.Seat.tests N) []
    VerifiableInference.Desc.K12.Seat.last
    (VerifiableInference.OnPublicFiles.OkD.AtC.beside Z.p.X Z.p.chains)

/-- **The value that `onlineDescription` gives.** -/
abbrev seatedAt (o : SecondHashFunctionArgument) (Z : Pub) (N : H2U.Places4) (c : Chain S Cl) : FileDescription Inst :=
  fileDescBy o pureRoad.links Z (sharedAt Z N) (P2Third.secondSeatOf Z N) (fun s => s) (startS Z) c

theorem pureTail_cut (Z : Pub) (T : PureSeat) (P : PureParts) (G : FileDescription Inst)
    (h : onlineDescriptionAfterTests Z T P = .ok G) :
    ∃ c A B, T.shared = some A ∧ T.second = some B ∧
      G = fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c := by
  unfold onlineDescriptionAfterTests at h
  cases hb : P.base with
  | error e => rw [hb] at h; cases h
  | ok base =>
    rw [hb] at h
    have h1 : ((chainBy Z base P.frames P.road).bind fun c =>
        match T.shared, T.second with
        | some A, some B =>
          Except.ok (fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c)
        | _, _ => .error "no description: nothing usable is supplied for: a later chain") =
        .ok G := h
    cases hc : chainBy Z base P.frames P.road with
    | error e => rw [hc] at h1; cases h1
    | ok c =>
      rw [hc] at h1
      have h2 : (match T.shared, T.second with
        | some A, some B =>
          Except.ok (fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c)
        | _, _ => .error "no description: nothing usable is supplied for: a later chain") =
        .ok G := h1
      cases hA : T.shared with
      | none => rw [hA] at h2; cases h2
      | some A =>
        cases hB : T.second with
        | none => rw [hA, hB] at h2; cases h2
        | some B =>
          rw [hA, hB] at h2
          cases h2
          exact ⟨c, A, B, rfl, rfl, rfl⟩

theorem pureZ_cut (Z : Pub) (T : PureSeat) (G : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z T = .ok G) :
    ∃ c A B, T.shared = some A ∧ T.second = some B ∧
      G = fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c := by
  unfold onlineDescriptionFromPublicPart at h
  cases hB : baseOf Z T with
  | error e => rw [hB] at h; cases h
  | ok B =>
    rw [hB] at h
    have h1 : (if !(faultsAt T B).isEmpty then
        Except.error ("no description: the supplied blocks are inconsistent: " ++
          "; ".intercalate (faultsAt T B))
      else if !(lackingAt T (partsAt T B)).isEmpty then
        .error ("no description: nothing usable is supplied for: " ++
          ", ".intercalate (lackingAt T (partsAt T B)))
      else onlineDescriptionAfterTests Z T (partsAt T B)) = .ok G := h
    split at h1
    · cases h1
    · split at h1
      · cases h1
      · exact pureTail_cut Z T _ G h1

/-- **Wherever `onlineDescription` gives a description, it is `fileDescBy` at the two named seats.** -/
theorem descPure_cut (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (G : FileDescription Inst)
    (h : onlineDescription o pol lay KL = .ok G) :
    ∃ (Z : Pub) (N : H2U.Places4) (c : Chain S Cl), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ G = seatedAt o Z N c := by
  unfold onlineDescription onlineDescriptionFromBlockTables at h
  cases hZ : pureRoad.pub o pol lay KL with
  | error e => rw [hZ] at h; cases h
  | ok Z =>
    rw [hZ] at h
    obtain ⟨c, A, B, hA, hB, rfl⟩ := pureZ_cut Z _ G h
    have hA' : sharedSeatAt Z = some A := hA
    have hB' : P2Third.secondSeat Z = some B := hB
    unfold sharedSeatAt at hA'
    unfold P2Third.secondSeat at hB'
    cases hN : H2U.placesOfMade Z.made with
    | error e => rw [hN] at hA'; cases hA'
    | ok N =>
      rw [hN] at hA' hB'
      cases hA'
      cases hB'
      exact ⟨Z, N, c, rfl, hN, rfl⟩

theorem ended_at (Z : Pub) (N : H2U.Places4) : (sharedAt Z N).ended = Desc.K14.ended := rfl

theorem start_at (Z : Pub) (N : H2U.Places4) :
    (P2Third.secondSeatOf Z N).start = startAtEnds (pAt Z) := rfl

variable (o : SecondHashFunctionArgument) (Z : Pub) (N : H2U.Places4) (c : Chain S Cl) {P₀ : Type}
  (g : InstPub × S → P₀ × S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
include hg

/-- **hmark at the seat.** -/
theorem hmark_at : ∀ (q : InstPub) (s₁ : S) (d : St) (s : S₃),
    ((seatedAt o Z N c).start₃ q s₁ d).toOption = some s → (g (q, s₁)).2.failed = none :=
  fun q s₁ d s h => start₃_no_mark o pureRoad.links Z (sharedAt Z N) (P2Third.secondSeatOf Z N)
    (fun s => s) (startS Z) c g hg q s₁ d s h

/-- **hstart at the seat.** -/
theorem hstart_at : ∀ (q : InstPub) (s₁ : S) (d : St) (s : S₃),
    ((seatedAt o Z N c).start₃ q s₁ d).toOption = some s →
    ∃ e, Desc.K14.ended d = some e ∧ startAtEnds (pAt Z) q (g (q, s₁)).2 e = .ok s :=
  fun q s₁ d s h => start₃_ends o pureRoad.links Z (sharedAt Z N) (P2Third.secondSeatOf Z N)
    (fun s => s) (startS Z) c g hg q s₁ d s h

end ProofFile

#print axioms ProofFile.descPure_cut
#print axioms ProofFile.ended_at
#print axioms ProofFile.start_at
#print axioms ProofFile.hmark_at
#print axioms ProofFile.hstart_at
