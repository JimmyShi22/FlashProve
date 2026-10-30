-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.DescN
/-
Johnson/Loose/H2K12/FirstSeatForm.lean:
OVER THE FILES BELOW IT, IN WHICH chainBy JOINS BY THE SEGMENT AND THE NAME: THE
PROXIMITY TEST's SUB-PROTOCOL AS IT SITS AT THE FIRST CHAIN's PLACE F:2 (⟨1, none, 2, K12⟩), AND ITS
WAY OUT: K12's files' own matter. OF ProofFile's TEXTS IT READS guardMark ALONE
(Johnson/Desc/ProofFile/Frames1.lean), of Johnson/Desc/SeatGuard.lean seatSame.

chainBy joins by the segment AND the name, F:2 stands in no segment, and it is
shown that nothing is joined there (parts_first_cut_alone, in SitsInPure.lean).
FirstJ HAS ONE ARM; FirstOut SAYS THE SAME OF J AND PINS leave TO outCore same.
NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  ebind_ok             if a bind returns a value so do both parts (the library has the same
      statement as ProofFile.Law.exBind_ok: kept under this name for its callers).
  guardS · firstCore p nm · firstCore_sits | _keeps     the kind's sub-protocol as partsAt lays it;
      it sits behind leaveFinish and the mark's guard.
  FirstJ p J           what stands at F:2: J = firstCore p nm for some name nm.
  outCore · outCore_ok · FirstOut same p J leave     the way out, written: J = firstCore p nm for
      some name nm, and leave = outCore same.
  firstJ_sitsCore      the entry sits, behind outCore same.
  firstJ_sits          the same in the shape
      («there is a way out …»), which the callers' patterns count.
  descN_atL            where (descN …).runEnd accepts: AtCut at the first chain's cut, the cut
      being a premise.
WHAT IS NOT HERE: that the first chain IS cut so (H2K12/SitsInPure.lean: pureZ_sits).
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)

universe u v w

theorem ebind_ok {ε : Type u} {α : Type v} {β : Type w} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### the lot's block as it is laid -/

/-- The mark's guard: what ProofFile.guardMark binds behind a decision. -/
def guardS (t : First.S) : Except String First.S :=
  (ProofFile.guardMark (roundlessBlock "" 1 none 0 .ok : Block First.S ProofFile.Cl)).decide t [] []

/-- K12's lot's block as partsAt lays it at its spot: at the fold's claims, behind the mark's guard,
under the spot's name. -/
def firstCore (p : P12) (nm : String) : Block First.S ProofFile.Cl :=
  { ProofFile.guardMark ((atFinish p).retype (Cl' := ProofFile.Cl)) with name := nm }

theorem firstCore_sits (p : P12) (nm : String) :
    Sits (firstCore p nm) (proximityTestKind guardedProximityTestParts p : Blk') enterFinish
      (fun s t => (leaveFinish s t).bind guardS) :=
  ((sits_inside enterFinish (proximityTestKind guardedProximityTestParts p : Blk') leaveFinish).retype (Cl'' := ProofFile.Cl)).behind
    (firstCore p nm) (fun _ t => guardS t) rfl (fun _ _ _ => rfl) id

theorem firstCore_keeps (p : P12) (nm : String) :
    H2K.Made.Keeps (firstCore p nm) (proximityTestKind guardedProximityTestParts p : Blk') := ⟨rfl, rfl⟩

/-- What stands at a12: the kind's sub-protocol as laid, under some name. (Over the
files below it, in which chainBy joins so, nothing is joined behind
it: chainBy joins by the segment and the name, and a12 stands in no segment.) -/
def FirstJ (p : P12) (J : Block First.S ProofFile.Cl) : Prop := ∃ nm, J = firstCore p nm

/-- The way out of the entry: leaveFinish, the mark's guard, the guard on the reply's seat. -/
def outCore (same : First.S → First.S → Bool) (s : First.S) (t : T12) : Except String First.S :=
  ((leaveFinish s t).bind guardS).bind (seatSame same s)

theorem guardS_ok (m m' : First.S) : guardS m = .ok m' ↔ m' = m ∧ m.failed = none := by
  show (match m.failed with
    | none => (Except.ok m : Except String First.S)
    | some w => _) = .ok m' ↔ _
  split
  · rename_i h
    constructor
    · intro e; cases e; exact ⟨rfl, h⟩
    · rintro ⟨rfl, _⟩; rfl
  · rename_i w h
    constructor
    · intro e; cases e
    · rintro ⟨_, e⟩; rw [h] at e; cases e

theorem seatSame_ok {S : Type} (same : S → S → Bool) (s m m' : S) :
    seatSame same s m = .ok m' ↔ m' = m ∧ same s m = true := by
  unfold seatSame
  split
  · rename_i h
    constructor
    · intro e; cases e; exact ⟨rfl, h⟩
    · rintro ⟨rfl, _⟩; rfl
  · rename_i h
    constructor
    · intro e; cases e
    · rintro ⟨_, e⟩; exact absurd e h

/-- THE VERIFIER's STATE BEHIND IS leaveFinish's OWN: no mark; the reply's seat as in front. -/
theorem outCore_ok (same : First.S → First.S → Bool) (s : First.S) (t : T12) (s' : First.S) :
    outCore same s t = .ok s' ↔
      leaveFinish s t = .ok s' ∧ s'.failed = none ∧ same s s' = true := by
  unfold outCore
  constructor
  · intro h
    obtain ⟨m, h1, h2⟩ := ebind_ok h
    obtain ⟨m0, h3, h4⟩ := ebind_ok h1
    obtain ⟨rfl, hf⟩ := (guardS_ok _ _).1 h4
    obtain ⟨rfl, hs⟩ := (seatSame_ok same _ _ _).1 h2
    exact ⟨h3, hf, hs⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h1]
    show (guardS s').bind _ = _
    rw [(guardS_ok s' s').2 ⟨rfl, h2⟩]
    exact (seatSame_ok same s s' s').2 ⟨rfl, h3⟩

/-- What stands at a12, and its way out: outCore. -/
def FirstOut (same : First.S → First.S → Bool) (p : P12) (J : Block First.S ProofFile.Cl)
    (leave : First.S → T12 → Except String First.S) : Prop :=
  ∃ nm, J = firstCore p nm ∧ leave = outCore same

/-- The entry sits, behind outCore same. -/
theorem firstJ_sitsCore (same : First.S → First.S → Bool) (p : P12) (J : Block First.S ProofFile.Cl)
    (hJ : FirstJ p J) :
    Sits (firstEntry same J) (proximityTestKind guardedProximityTestParts p : Blk') enterFinish (outCore same) := by
  obtain ⟨nm, rfl⟩ := hJ
  exact firstEntry_sits same (firstCore_sits p nm)

/-- The same, in the shape that the callers' patterns count. «There is leave» is dress alone:
FirstOut pins leave to outCore same. -/
theorem firstJ_sits (same : First.S → First.S → Bool) (p : P12) (J : Block First.S ProofFile.Cl)
    (hJ : FirstJ p J) :
    ∃ leave, FirstOut same p J leave ∧
      Sits (firstEntry same J) (proximityTestKind guardedProximityTestParts p : Blk') enterFinish leave := by
  obtain ⟨nm, e⟩ := hJ
  exact ⟨_, ⟨nm, e, rfl⟩, firstJ_sitsCore same p J ⟨nm, e⟩⟩

/-- AT THE FIRST CHAIN's FINISH. -/
theorem descN_atL (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N :
                    H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (same : First.S → First.S → Bool)
    (pre l : List (Block First.S ProofFile.Cl)) (J : Block First.S ProofFile.Cl)
    (hb : c.blocksInOrder = pre ++ firstEntry same J :: l) (hJ : FirstJ (pL N) J)
    (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
    (e : (descN o mk guardedProximityTestParts Z N c).S₁ × (descN o mk guardedProximityTestParts Z N c).S₂ ×
      (descN o mk guardedProximityTestParts Z N c).S₃)
    (h : (descN o mk guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e) :
    ∃ leave, AtCut X (pL N) 0 pre (firstEntry same J) l enterFinish leave
        ((descN o mk guardedProximityTestParts Z N c).start₁ ((descN o mk guardedProximityTestParts Z N c).pub x)) e.1 (withEmptySealRound v₁)
          ∧
      FirstOut same (pL N) J leave := by
  obtain ⟨leave, hl, hs⟩ := firstJ_sits same (pL N) J hJ
  exact ⟨leave, run_atCut1 X (pL N) (descN o mk guardedProximityTestParts Z N c) x v₁ v₂ v₃ e h pre _ l _ _ hb hs,
    hl⟩

end H2K.JointK

#print axioms H2K.JointK.outCore_ok
#print axioms H2K.JointK.firstJ_sitsCore
#print axioms H2K.JointK.firstJ_sits
#print axioms H2K.JointK.descN_atL
