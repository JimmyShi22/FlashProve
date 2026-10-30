-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Quiet.lean: THE FALL SEATED AT THE MEMBER THAT REFUSES: K9's share as a
test ON THE STATE AS IT STANDS in front of the frame's member "behind the batching", which has no
round. Definitions with code, statements and proofs on the verifier's text; `#guard` lines at the toy
of Honest/K9/Toy.lean. No prover is in this file, and no goal is stated.

  `quietPlace p`      the place of that member: the piece behind the batching's, of the kind "frame"
                      (`Link.blocksInOrder`, Johnson/Desc/Block.lean)
  `k4FreeShare`       K4's own "free-slot", which at a layers' segment runs in that member: its condition
                      as it stands in K4's text, at the state's ledger and at the merge's slot in
                      what the own rounds returned; silent at another sort of state, and at a layers'
                      state at which the own rounds have returned nothing (K4's run refuses there: no
                      test on values)
  `quietFallTest`     the test there: of the state in front of the member; it reads no challenge. IT
                      NAMES THE VERIFIER's BOOLS THAT IT HOLDS: K9's share (`freeSlotShare`,
                      Honest/K9/Fall.lean); K4's, where a number of slots is given for it; then
                      another kind's (K8's, a parameter)
  `batFall_is`        the test at the batching's round (`batFallTest`) is: the share in front, or the
                      test here, without K4's share, at the state behind the batching: ONE TEXT, TWO
                      SEATS
  `quietFallAt`       at segment l of the proof file's description: K9's number of slots off the public
                      parameters, as `k9Tests` reads it
  `quiet_few`         the count of Honest/K9/FallGoodOf.lean, said of this seat: at most n * (the plan's number of
                      claims - 1) readings of a chi at which the batching says yes and K9's share, WITH OR
                      WITHOUT K4's AT THE SAME NUMBER OF SLOTS, speaks at the state behind
  `guardMark_bare`, `quiet_few_of`, `quiet_few_marked`   THE THEOREMS OF THESE FILES ARE AT K9's BARE
                      BATCHING; the description's own member at that place is wrapped by its makers
                      (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean, and more). A wrapping that only
                      refuses more leaves the bound: the counted set shrinks: stated for any such
                      member, and at `guardMark`
  `k4Free_eq`, `k4Free_of_slotsFree`   AT A LAYERS' SEGMENT THE SECOND "free-slot" (K4's run behind the
                      batching) ASKS THE SAME BOOL: K4's condition at (n, the merge's slot, the ledger)
                      is `slotsFree n` of the state: so where K9's share is silent K4's is too
                      (`k4Share_silent`), AT THE SAME NUMBER n AND THE SAME STATE
  `k4Run_silent`      AGAINST K4's OWN RUN AT ITS SEAT: where the run "free-slot" of K4's block at the first chain's
                      type of states returns, K4's share at that block's number of slots is silent: so where the share
                      speaks, the run refuses (`freeSlotAtS_test`, Johnson/Desc/First/K4/RunsAtC.lean). AT
                      `K4.blockAtS p`: the run that stands in a seated link's list is tied to another form of
                      K4's block (`blockAtC`): that step is not taken here; the theorem is called by no line
Limits. The test asks K9's Bool, K4's, then the other kind's: the member's own order is K9's tests and
counts, the smallness test's first run, K4's, the smallness test's tests: which name speaks can
differ, not whether one of these three does, at one state. No line runs `quietFallAt`: it wants a public
part (`Pub`). That K4's number of slots is K9's (two readings of the plan), and that the run which
stands in front of K4's (the smallness test's) leaves the ledger and what the own rounds returned, is
not shown here. "SILENT JUST WHERE THAT MEMBER SAYS YES" IS THE TOY's TRUTH: the toy's member has no run
behind its tests. The other way round at K4's run (what the own rounds returned is there, the share is
silent, so the run says yes) is not shown. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallGoodOfToy
import Johnson.Desc.First.K4.RunsAtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where batch mergeOf tAtS)

/-- The place of the frame's member behind the batching. -/
def quietPlace (p : Where) : Place := ⟨p.chain, some p.link, p.piece + 1, .frame⟩

/-- K4's own "free-slot", as a share. used: K4's number of slots. -/
def k4FreeShare (used : Nat) (s : S) : Option String :=
  match s.here with
  | .lay a =>
    match a.own with
    | some o =>
      if OnBytes.Desc.First.K4.freeSlotOk used o.wo.sFv a.F then none else some "K4.free-slot"
    | none => none
  | _ => none

/-- **The fall's test at the member that refuses.** It reads no challenge. k4: K4's number of slots,
at a layers' segment; `none` at the other sorts. -/
def quietFallTest (n : Nat) (k4 : Option Nat) (other : S → Option String) (s : S)
    (_ : List Fmt.Drawn) : Option String :=
  ((freeSlotShare n s).or (k4.bind fun u => k4FreeShare u s)).or (other s)

/-- One text, two seats. -/
theorem batFall_is {Cl : Type} (b : Block S Cl) (n : Nat)
    (front : S → List Fmt.Drawn → Option String) (other : S → Option String) (s : S)
    (ds : List Fmt.Drawn) :
    batFallTest b n front other s ds =
      (front s ds).or ((behindBat b s ds).bind fun s₁ => quietFallTest n none other s₁ []) := by
  unfold batFallTest quietFallTest
  congr 1
  cases behindBat b s ds with
  | none => rfl
  | some s₁ =>
    show (freeSlotShare n s₁).or (other s₁) = ((freeSlotShare n s₁).or none).or (other s₁)
    cases freeSlotShare n s₁ <;> rfl

/-- At segment l of the proof file's description. Nothing is tested where the public parameters have no
plan for the segment. -/
def quietFallAt (Z : Pub) (l : Nat) (k4 : Option Nat) (other : S → Option String) (s : S)
    (ds : List Fmt.Drawn) : Option String :=
  (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).bind fun w =>
    quietFallTest w.2.2.filled k4 other s ds

/-- K4's condition is K9's, at the merge's slot as an option. -/
theorem k4Free_eq (n sFv : Nat) (F : Fork) :
    OnBytes.Desc.First.K4.freeSlotOk n sFv F =
      VerifiableInference.Desc.First.Door.freeSlotOk n (some sFv) F := by
  unfold OnBytes.Desc.First.K4.freeSlotOk VerifiableInference.Desc.First.Door.freeSlotOk
  congr 1
  funext j
  have e : (j == sFv) = (some sFv == some j) := by
    by_cases h : j = sFv
    · subst h; simp
    · have h' : sFv ≠ j := fun e => h e.symm
      simp [h, h']
  rw [e]

/-- At a layers' state with what the own rounds returned: K4's Bool is `slotsFree`. -/
theorem k4Free_of_slotsFree (n : Nat) (s : S) (a : VerifiableInference.Desc.First.LayOwn)
    (o : OnBytes.Model.Layer.Own) (hs : s.here = .lay a) (ho : a.own = some o) :
    OnBytes.Desc.First.K4.freeSlotOk n o.wo.sFv a.F = slotsFree n s := by
  rw [k4Free_eq]
  unfold slotsFree
  simp [tAtS, S.fork?, S.tl?, mergeOf, hs, ho]

/-- **At K9's own number K4's share adds nothing**: where K9's share is silent, so is K4's. -/
theorem k4Share_silent (n : Nat) (s : S) (h : freeSlotShare n s = none) : k4FreeShare n s = none := by
  have hf : slotsFree n s = true := by
    unfold freeSlotShare at h
    cases hq : slotsFree n s with
    | true => rfl
    | false => rw [hq] at h; exact nomatch h
  unfold k4FreeShare
  cases hs : s.here with
  | lay a =>
    cases ho : a.own with
    | none => simp only [ho]
    | some o =>
      simp only [ho, k4Free_of_slotsFree n s a o hs ho, hf, if_true]
  | between => rfl
  | att _ => rfl
  | head _ => rfl
  | fin _ => rfl
  | mem _ => rfl

/-- **Against K4's own run at its seat**: where it returns, K4's share is silent. -/
theorem k4Run_silent {p : OnBytes.Desc.First.K4.Par} {run : S → Except String S}
    (hr : (OnBytes.Desc.First.K4.blockAtS p).after.lookup "free-slot" = some run) {s s' : S}
    (h : run s = .ok s') : k4FreeShare p.hp.used s = none := by
  obtain ⟨a, o, ho, ht, hw⟩ := OnBytes.Desc.First.K4.freeSlotAtS_test hr h
  unfold k4FreeShare
  rw [hw.1]
  simp only [ho, ht, if_true]

/-- **The count, said of this seat**: with K4's share left out, or asked at K9's own number. -/
theorem quiet_few (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p g s x₀ = some y₀) (hb : goodAt n y₀ = true)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ (x : E) (s₁ : S), Reading.gl.val x = y ∧
      (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok s₁ ∧
      (quietFallTest n k4 (fun _ => none) s₁ []).isSome = true) ≤
        n * (y₀.2.1.F.planClaimsF - 1) := by
  refine le_trans (Prob.cnt_mono fun y hy => ?_) (batFall_few_bool p g s laws n x₀ y₀ h₀ hb)
  obtain ⟨x, s₁, rfl, hd, hq⟩ := hy
  refine ⟨x, rfl, ?_⟩
  have hbe : behindBat (batch atS p g) s [drawnOne x] = some s₁ := by
    show ((batch atS p g).decide s [⟨[], drawnOne x⟩] []).toOption = some s₁
    rw [hd]
    rfl
  rw [batFall_is, hbe]
  show (quietFallTest n none (fun _ => none) s₁ []).isSome = true
  -- K9's own share speaks: else K4's, at the same number, would be silent too
  cases hf : freeSlotShare n s₁ with
  | some m =>
    unfold quietFallTest
    rw [hf]
    rfl
  | none =>
    exfalso
    have h4 : (k4.bind fun u => k4FreeShare u s₁) = none := by
      rcases hk with rfl | rfl
      · rfl
      · exact k4Share_silent n s₁ hf
    unfold quietFallTest at hq
    rw [hf, h4] at hq
    exact nomatch hq

/-- A yes of the member with the guard on marks is a yes of the bare member, to the same state. -/
theorem guardMark_bare (b : Block S ProofFile.Cl) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (guardMark b).decide s rs gs = .ok t) :
    b.decide s rs gs = .ok t := by
  obtain ⟨u, hu, h2⟩ := bind_ok (x := b.decide s rs gs)
    (f := fun t => match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) h
  cases hf : u.failed with
  | none =>
    simp only [hf] at h2
    rw [hu, Except.ok.inj h2]
  | some m =>
    simp only [hf] at h2
    exact nomatch h2

/-- **The count at a member that refuses more**: b': any member whose yes, from s, is a yes of K9's bare
batching to the same state: as the description's makers wrap it. The counted set only shrinks. -/
theorem quiet_few_of {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p g s x₀ = some y₀) (hb : goodAt n y₀ = true)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ (x : E) (s₁ : S), Reading.gl.val x = y ∧
      b'.decide s [⟨[], drawnOne x⟩] [] = .ok s₁ ∧
      (quietFallTest n k4 (fun _ => none) s₁ []).isSome = true) ≤
        n * (y₀.2.1.F.planClaimsF - 1) :=
  le_trans (Prob.cnt_mono fun _ hy => by
    obtain ⟨x, s₁, e, hd, hq⟩ := hy
    exact ⟨x, s₁, e, hb' _ _ hd, hq⟩) (quiet_few p g s laws n x₀ y₀ h₀ hb k4 hk)

/-- At the batching with the guard on marks. -/
theorem quiet_few_marked (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p g s x₀ = some y₀) (hb : goodAt n y₀ = true)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ (x : E) (s₁ : S), Reading.gl.val x = y ∧
      (guardMark (batch atS p g)).decide s [⟨[], drawnOne x⟩] [] = .ok s₁ ∧
      (quietFallTest n k4 (fun _ => none) s₁ []).isSome = true) ≤
        n * (y₀.2.1.F.planClaimsF - 1) :=
  quiet_few_of p g s laws n x₀ y₀ h₀ hb k4 hk _ fun rs t h => guardMark_bare _ s t rs [] h

namespace Toy

-- the place is the description's own member's
#guard quietPlace pw == (at_ 3).place
#guard (at_ 3).rounds.isEmpty
-- over 24 values: at the state behind the batching the test is silent just where that member says yes
#guard (List.range 24).all fun c =>
  ((behind held c.toUInt64).toOption.map fun s₁ =>
    (quietFallTest 2 none (fun _ => none) s₁ []).isNone == ((at_ 3).decide s₁ [] []).toOption.isSome)
    == some true
#guard ((behind held 1).toOption.bind fun s₁ => quietFallTest 2 none (fun _ => none) s₁ [])
  == some "K9.free-slot"
#guard ((behind held 5).toOption.bind fun s₁ => quietFallTest 2 none (fun _ => some "another's") s₁ [])
  == some "another's"
-- K4's share: at another number of slots than K9's it can speak where K9's is silent (three slots
-- asked where two have a coefficient); at K9's own number it adds nothing; no merge laid: silent
#guard ((behind held 1).toOption.bind fun s₁ =>
  quietFallTest 2 (some 3) (fun _ => none) (withMerge 1 s₁) []) == some "K4.free-slot"
#guard ((behind held 1).toOption.bind fun s₁ =>
  quietFallTest 2 (some 2) (fun _ => none) (withMerge 1 s₁) []) == none
#guard ((behind held 5).toOption.bind fun s₁ => k4FreeShare 2 (withMerge 1 s₁))
  == some "K4.free-slot"
#guard ((behind held 1).toOption.bind fun s₁ => k4FreeShare 3 s₁) == none
-- K4's Bool at the toy's states with a merge: the same answers as K9's share
#guard (behind held 1).toOption.map (fun s => (s.fork?.map fun F =>
  OnBytes.Desc.First.K4.freeSlotOk 2 1 F) == some (slotsFree 2 (withMerge 1 s))) == some true
#guard (behind held 5).toOption.map (fun s => (s.fork?.map fun F =>
  OnBytes.Desc.First.K4.freeSlotOk 2 1 F) == some (slotsFree 2 (withMerge 1 s))) == some true
#guard (behind held 5).toOption.bind (fun s => s.fork?.map fun F =>
  OnBytes.Desc.First.K4.freeSlotOk 2 1 F) == some false

end Toy

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFall_is
#print axioms ProofFile.Honest.K9.quiet_few
#print axioms ProofFile.Honest.K9.k4Free_eq
#print axioms ProofFile.Honest.K9.k4Free_of_slotsFree
#print axioms ProofFile.Honest.K9.k4Share_silent
#print axioms ProofFile.Honest.K9.k4Run_silent
#print axioms ProofFile.Honest.K9.guardMark_bare
#print axioms ProofFile.Honest.K9.quiet_few_of
#print axioms ProofFile.Honest.K9.quiet_few_marked
#print axioms ProofFile.Honest.K9.quietPlace
#print axioms ProofFile.Honest.K9.k4FreeShare
#print axioms ProofFile.Honest.K9.quietFallTest
#print axioms ProofFile.Honest.K9.quietFallAt
