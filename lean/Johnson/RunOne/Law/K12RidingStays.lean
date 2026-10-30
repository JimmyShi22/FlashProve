-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12RidingStays.lean: The key
file's tables, the rows that a proximity test closes on the shared chain (2.9 · 2.10): WHAT STAYS OF
A MEMBER THAT RIDES ACROSS THE TEST, FOR CERTAIN, OFF THE PIECE's OWN ACCEPTANCE: its out-of-domain
(OOD) sample as the tables' reading reads it, and its committed word. General in the row: in the
seat's two letters (which group; which mask), the place and the message's number. Statements and
proofs; each proof is a row of calls; no definition.

Why. The premise «law» of the way back (`law_29`, K12Law29.lean; `law_210`, K12Law210.lean) takes
the riding member's pin behind the test and wants it in front: two premises there, hsmp and hword.
Whose is what. Called: `seat_leaves` (Johnson/Desc/K12/Coin/SamplesThrough.lean: the test leaves
each elder message's shape, mark and sample rows, and the codes); `smp₂_of_only`, `SampleAlike`,
`sampleAlike_refl` (Johnson/RunOne/KeySmOnly.lean); `piece_decides_at`
(Johnson/Desc/Plain/PieceYes.lean); `held_decide` (Johnson/Desc/Plain/PaidKeeps.lean); `out_behind'`
(Johnson/Desc/Key/KeyKeeps.lean); `wordStays` (Johnson/Desc/Sound/StringsStay.lean).
Kin. `fwd₂_seat` (Johnson/RunOne/Law/K12Fwd29.lean, the promise's half) walks the like
road to the sample inside its proof, by SmpStay, at all pins still open; it states no lemma of it.
`strsStay_of_out` (KeyKeeps.lean) has the word at all open pins at once.
What it is not, first.
  (1) `SmOnly` (the tables' reading reads of a message its shape, its mark and its sample rows
    alone) is a premise.
  (2) That the message is there in front of the test and is not the test's first mask, and that its
    tree lies below the piece's base, are premises.
  (3) It pays no field of the tables. No soundness is claimed. Nothing on hiding.
Main names.
  `sampleAlike_of_part`: from «the three fields stay» in `smpPart`'s form to `SampleAlike`'s.
  `smp_rides₂`: across an acceptance of the test inside its doors.
  `riding_stays₂`: both, across an acceptance of a piece that holds a sub-protocol alike to the
    test inside its doors: `law_29`'s | `law_210`'s hsmp and hword.

-/
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.K12.Coin.Alike
import Johnson.Desc.Key.KeyKeeps
import Johnson.Desc.Plain.PaidKeeps
import Johnson.RunOne.KeySmOnly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12RidingStays
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain (held_decide piece_decides_at)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (Alike smpPart seat_leaves)
open Johnson.RunOne.KeyRows23

/-- From «the codes stay, and under the number o the shape, the mark and the sample rows stay». -/
theorem sampleAlike_of_part (St St' : Statement) (o : Nat) (hc : St'.codes = St.codes)
    (h : (St'.oracles[o]?).map smpPart = (St.oracles[o]?).map smpPart) : SampleAlike St St' o := by
  refine ⟨hc, ?_⟩
  cases hx : St.oracles[o]? with
  | none =>
    rw [hx] at h
    cases hx' : St'.oracles[o]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some x' =>
      rw [hx'] at h
      exact nomatch h
  | some x =>
    rw [hx] at h
    cases hx' : St'.oracles[o]? with
    | none =>
      rw [hx'] at h
      exact nomatch h
    | some x' =>
      rw [hx'] at h
      have e : smpPart x' = smpPart x := Option.some.inj h
      exact Or.inr ⟨x, x', rfl, rfl, congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩

section
variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec)

/-- **The OOD sample at a seat stays across an acceptance of the test inside its doors.** -/
theorem smp_rides₂ (hSm : T.SmOnly) (g : _root_.Desc.K14.Lin → Nat)
    (mask : _root_.Desc.K14.Lin → Option Nat) (π : P12) (he : π.early = true)
    (ha : π.answers = 1) (z : P₂) (d d' : St₂) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts π : Block T12 Unit)
      K12.Seat.leave).decide d rs gs = .ok d') (j t : Nat)
    (hlt : ∀ o, orc₂ (T.arr j t) = some o → o < d.st.oracles.size ∧ mask d.loc ≠ some o) :
    T.h₂.smp (z, d') j t = T.h₂.smp (z, d) j t := by
  obtain ⟨hc, hs, _⟩ := seat_leaves g mask π he ha d d' rs gs h
  exact smp₂_of_only T hSm (z, d) (z, d') j t (fun o _ => sampleAlike_refl _ o) fun o ho =>
    sampleAlike_of_part d.st d'.st o hc (hs o (hlt o ho).1 (hlt o ho).2)

variable {XI Cl W : Type} {C : _root_.Run.PQ.CK} (F : FileDescription XI) (Fr : Frame)

/-- **What stays of a riding member across the piece's acceptance.** -/
theorem riding_stays₂ (hSm : T.SmOnly) (g : _root_.Desc.K14.Lin → Nat)
    (mask : _root_.Desc.K14.Lin → Option Nat) (π : P12) (he : π.early = true)
    (ha : π.answers = 1) (p : Piece C Fr (P₂ × St₂) Cl W) (B : Block St₂ Cl)
    (hb : p.b = held B)
    (hal : Alike (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts π : Block T12 Unit)
      K12.Seat.leave) B)
    (x y : (P₂ × St₂) × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (hout : p.ior.red.out x τ = some y)
    (j t : Nat)
    (hlt : ∀ o, orc₂ (T.arr j t) = some o → o < x.1.2.st.oracles.size ∧ mask x.1.2.loc ≠ some o)
    (hbase : j < p.base) :
    T.h₂.smp y.1 j t = T.h₂.smp x.1 j t ∧
      wordOf F (strsOf Fr y.2) j t = wordOf F (strsOf Fr x.2) j t := by
  have hd := piece_decides_at p x τ y hout
  rw [hb] at hd
  obtain ⟨e1, hB⟩ := held_decide B x.1 _ _ y.1 hd
  rw [hal.decide] at hB
  refine ⟨?_, ?_⟩
  · have e := smp_rides₂ T hSm g mask π he ha x.1.1 x.1.2 y.1.2 _ _ hB j t hlt
    have ey : y.1 = (x.1.1, y.1.2) := Prod.ext e1 rfl
    rw [ey]
    exact e
  · rw [out_behind' Fr p x y τ hout]
    exact wordStays XI F C Fr p.base p.ds x.2 τ j t hbase

end

end Johnson.RunOne.Law.K12RidingStays

#print axioms Johnson.RunOne.Law.K12RidingStays.sampleAlike_of_part
#print axioms Johnson.RunOne.Law.K12RidingStays.smp_rides₂
#print axioms Johnson.RunOne.Law.K12RidingStays.riding_stays₂
