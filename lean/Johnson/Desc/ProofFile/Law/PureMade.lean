-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/PureMade.lean: what it means that `onlineDescription` returns a description.
OnlineDescriptionFromBlockTables.lean, Frames1.lean and FillCore.lean have cases in which nothing is tested, for a part that is
missing. Their comments say that a description that `onlineDescriptionFromPublicPart` returns does not reach these cases,
because `faultsAt` and `lackingAt` found nothing. These theorems state the first half of that: where
a description is returned, both lists are empty, and the description is `fileDescBy` at the chain
that `chainBy` makes.
  `pureZ_ok`        `onlineDescriptionFromPublicPart Z T = .ok F` gives the base, both lists empty, and `onlineDescriptionAfterTests`'s value
  `pureTail_ok`     `onlineDescriptionAfterTests Z T P = .ok F` gives the blocks, the chain, the two later chains, and
                    `F` as `fileDescBy` of these
  `descPure_parts`  both, for `onlineDescription`
  `descPure_startOk`   where `onlineDescription` returns a description, State.lean's four tests on the first
                    chain's public parameters (`S.startOk`) hold, at the plan's own number of
                    samples.
                    They are asked while the public part is computed (`pubBy`), not by `planOk`.
Not here: that an empty `lackingAt` implies that each of the cases is not reached. That still has to
be read off `lackingAt`, `partsAt` and `chainBy`.

-/
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

theorem pureZ_ok {Z : Pub} {T : PureSeat} {F : FileDescription Inst} (h : onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ B, baseOf Z T = .ok B ∧ faultsAt T B = [] ∧ lackingAt T (partsAt T B) = [] ∧
      onlineDescriptionAfterTests Z T (partsAt T B) = .ok F := by
  unfold onlineDescriptionFromPublicPart at h
  obtain ⟨B, hB, h⟩ := exBind_ok h
  refine ⟨B, hB, ?_⟩
  by_cases hf : (faultsAt T B).isEmpty = true
  · by_cases hl : (lackingAt T (partsAt T B)).isEmpty = true
    · refine ⟨List.isEmpty_iff.mp hf, List.isEmpty_iff.mp hl, ?_⟩
      simpa [hf, hl] using h
    · simp [hf, hl] at h
  · simp [hf] at h

theorem pureTail_ok {Z : Pub} {T : PureSeat} {P : PureParts} {F : FileDescription Inst}
    (h : onlineDescriptionAfterTests Z T P = .ok F) :
    ∃ (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
      P.base = .ok base ∧ chainBy Z base P.frames P.road = .ok c ∧ T.shared = some A ∧
      T.second = some B ∧ F = fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c := by
  unfold onlineDescriptionAfterTests at h
  obtain ⟨base, hb, h⟩ := exBind_ok h
  obtain ⟨c, hc, h⟩ := exBind_ok h
  split at h
  · rename_i A B hA hB
    exact ⟨base, c, A, B, hb, hc, hA, hB, (Except.ok.inj h).symm⟩
  · exact (error_ne_ok h).elim

theorem descPure_parts {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (B : PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat)
      (B' : SecondSeat),
      pureRoad.pub o pol lay KL = .ok Z ∧ baseOf Z (pureSeat o Z) = .ok B ∧
      faultsAt (pureSeat o Z) B = [] ∧ lackingAt (pureSeat o Z) (partsAt (pureSeat o Z) B) = [] ∧
      (partsAt (pureSeat o Z) B).base = .ok base ∧
      chainBy Z base (partsAt (pureSeat o Z) B).frames (partsAt (pureSeat o Z) B).road = .ok c ∧
      onlineSharedChain Z = some A ∧ onlineLastChain Z = some B' ∧
      F = fileDescBy o pureRoad.links Z A B' (fun s => s) (startS Z) c := by
  obtain ⟨Z, hZ, hF⟩ := descPure_made h
  obtain ⟨B, hB, hf, hl, ht⟩ := pureZ_ok hF
  obtain ⟨base, c, A, B', hb, hc, hA, hB', hE⟩ := pureTail_ok ht
  exact ⟨Z, B, base, c, A, B', hZ, hB, hf, hl, hb, hc, hA, hB', hE⟩

/-! ### The tests on the first chain's public parameters -/

theorem orSay_ok {α : Type} {why : String} {x : Option α} {a : α} (h : orSay why x = .ok a) :
    x = some a := by
  cases x with
  | none => exact (error_ne_ok h).elim
  | some b => exact congrArg some (Except.ok.inj h)

/-- The first state in a public part is the value of the function that was passed in for it, at the
first chain's parameters. -/
theorem pubBy_start
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : Starts}
    {pol lay KL : ByteArray} {Z : Pub} (h : pubBy made st pol lay KL = .ok Z) :
    st.start (st.par Z.first) Z.first = some Z.s₀ := by
  unfold pubBy at h
  obtain ⟨m, _, h⟩ := bind_ok h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; exact orSay_ok (by assumption))

theorem startP_ok {P : VerifiableInference.Desc.First.Par} {codes : OnBytes.Codes}
    {shape : OnBytes.Params.ReqShape} {layout : OnBytes.Params.ReqLayout} {s : S}
    (h : S.startP P codes shape layout = some s) : S.startOk P codes shape layout = true := by
  unfold S.startP at h
  split at h
  · assumption
  · cases h

theorem descPure_startOk {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧
      S.startOk (VerifiableInference.Desc.First.parP Z.first) Z.first.codes Z.first.shape
        Z.first.layout = true := by
  obtain ⟨Z, hZ, _⟩ := descPure_made h
  exact ⟨Z, hZ, startP_ok (pubBy_start
    (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from hZ))⟩

end ProofFile.Law

#print axioms ProofFile.Law.descPure_startOk
#print axioms ProofFile.Law.pureZ_ok
#print axioms ProofFile.Law.pureTail_ok
#print axioms ProofFile.Law.descPure_parts
