-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/KeepsFrameAt.lean: THE CLAUSE OF keeps AT OUR OWN 52
MEMBERS OF THE KIND frame OF THE FIRST CHAIN THAT ARE NO «behind»: PAID. `keepsFrame`
(Honest/Law/NoHouse/KeepsFrame.lean) is the clause by the place. The records at these members
(Honest/Law/NoHouse/Seal.lean, FirstStill.lean, Cleared.lean) take it as a premise hKp on the letter
Kp. Here that premise's own form, at Kp's clause := `keepsFrame`.

WHAT THIS IS. Lemmas on a definition of ours and on the library's. None of the library's goals.

  `kp_out`, `kp_laid`   at a place outside the links (the front; the seal) and at a link's piece 0
  («laid»): a state without a mark stands in the clause with itself: by the clause's text
  `hearN_le`, `clearPlace_arm`   «cleared»'s place falls into the clause's last arm, at whatever
  list of sorts
  `flag_at`   AT THE HEAD: the row's clear is the library's `clearWith` at letters whose flag «a row
              is left» is `P1L20.bearing l`: the steps of the library's `P1L20.clear_by_sort`
              (Johnson/P1L20R/RoomFold.lean), which starts from a yes of the member's step, taken
              from the row itself: `clear_with_flag`, `plans_hold` (FrameSits.lean), `kind_of_sort`
              (FrameFold.lean)
  `kp_cleared`   AT THE HEAD, at each of the 25 links: f.clear s = .ok t and no mark at t give the
                 clause at take := `P1L20.bearing`: `Tied.clearedGives`, then `keepsCleared_of`

WHERE «NO MARK» COMES FROM. `kp_out` and `kp_laid` TAKE «no mark» AT THE STATE AS A PREMISE. At
«laid» a yes of the member's step holds it (the seat's guard on the mark). AT THE FRONT IT DOES NOT:
the front's sub-protocol asks nothing (the library's `IM.front_of`: its yes is «the state is handed
on», and no more): it is a bare sub-protocol without a guard on the mark, so the mark behind does
not follow from its yes alone: whoever goes ONE STEP BACK from a reached state, outside the thread,
does not get the clause there (Honest/Law/NoHouse/KeepsFrame.lean's words on «behind the batching»):
in the record it comes of the thread's own clause «no mark» in front. At the seal: whether its
clauses hold «no mark» has not been read. `kp_cleared` takes «no mark behind», which the seat's
guard at «cleared» gives.

Limits. THE FULL SIZE ALONE, and the format's second hash function alone, as the head. The library's head
has a member at the name under four premises on the public files (the seal's
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of our files calls it. Nothing
on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame
import Johnson.P1L20R.RoomFold
import Johnson.P1K2R.SitsDoor
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (hearN)
open Johnson.Desc.First.Walk (LinkPub clearWith)
open Johnson.Desc.First.Walk.Tied (ClearedRec clearedGives)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 Where a yes hands the state on -/

/-- Outside the links: the front; the seal. -/
theorem kp_out (links : List ModelPart) (take : Nat → Bool) {p : Place} (hp : p.link = none) :
    ∀ s : S, s.failed = none → keepsFrame links take p s s :=
  fun s h0 => (keepsFrame_out links take hp s s).2 ⟨rfl, h0⟩

/-- At a link's piece 0: «laid». -/
theorem kp_laid (links : List ModelPart) (take : Nat → Bool) {p : Place} {l : Nat}
    (hp : p.link = some l) (h0 : p.piece = 0) :
    ∀ s : S, s.failed = none → keepsFrame links take p s s :=
  fun s h1 => (keepsFrame_laid links take hp h0 s s).2 ⟨rfl, h1⟩

/-! ## 2 «cleared» -/

/-- A segment has at most nine hearing members. -/
theorem hearN_le (links : List ModelPart) (m : Nat) : hearN links m ≤ 9 := by
  unfold hearN kindsBeforeBatching
  cases (links[m]?).getD ModelPart.layers <;> simp

/-- «cleared»'s place falls into the clause's last arm. -/
theorem clearPlace_arm (links : List ModelPart) (take : Nat → Bool) (l : Nat) (s t : S) :
    keepsFrame links take (P1L20.clearPlace l) s t ↔ keepsCleared (take l) s t := by
  have h9 := hearN_le links l
  refine keepsFrame_cleared links take (p := P1L20.clearPlace l) rfl ?_ ?_ s t
  · show 13 + 2 * VerifiableInference.Desc.First.shift (IM.subAt l) ≠ 0
    omega
  · show 13 + 2 * VerifiableInference.Desc.First.shift (IM.subAt l) ≠ hearN links l + 2
    omega

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **The row's clear, with the flag by the link's sort.** -/
theorem flag_at {l : Nat} (hl : l < 25) {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) :
    ∃ (X : LinkPub) (counts : S → Except String Unit)
      (left : S → Option OnBytes.Model.WsForkOut), X.fv = P1L20.bearing l ∧
      f.clear = clearWith X counts left (Johnson.Desc.First.Walk.Seat.rowOf Zp.p.X Zp.first) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨X, counts, left, X', e1, hX', hkk, -, -, hflag⟩ := P1L20.clear_with_flag hfs hf
    (P1L20.plans_hold h.scope h.reads O (P1K2.flat_planOk O h.laid.planOk) hfs hl hf)
  refine ⟨X, counts, left, ?_, e1⟩
  have hsub := P1L20.kind_of_sort h.scope h.reads O hl hX'
  unfold P1L20.bearing
  rcases hflag with ⟨g1, g2⟩ | ⟨g1, g2, -⟩
  · rw [hkk] at g1
    rw [g1] at hsub
    rw [g2, ← hsub]
    decide
  · rw [hkk] at g1
    rw [g2]
    have : IM.subAt l ≠ ModelPart.attention := by
      rw [← hsub]
      unfold ProofFile.subOf
      by_cases h0 : X'.kind = 0
      · simp [h0]
      · simp [h0, g1]
    simp [this]

/-- **THE CLAUSE AT «LINK l: CLEARED»**, at each of the 25 links, at take := the library's «link l
leaves a row». It is the premise hKp of the record there, at this clause. -/
theorem kp_cleared (links : List ModelPart) {l : Nat} (hl : l < 25)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs)
    (hf : fs[l]? = some f) :
    ∀ s t : S, f.clear s = .ok t → t.failed = none →
      keepsFrame links P1L20.bearing (P1L20.clearPlace l) s t := by
  intro s t e h0
  obtain ⟨X, counts, left, hfv, hcl⟩ := flag_at h hl hfs hf
  rw [hcl] at e
  rw [clearPlace_arm, ← hfv]
  exact keepsCleared_of (clearedGives X counts left _ _ s t e) h0

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.kp_out
#print axioms ProofFile.Honest.FirstThread.kp_laid
#print axioms ProofFile.Honest.FirstThread.hearN_le
#print axioms ProofFile.Honest.FirstThread.clearPlace_arm
#print axioms ProofFile.Honest.FirstThread.flag_at
#print axioms ProofFile.Honest.FirstThread.kp_cleared
