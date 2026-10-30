-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LooksAtFrame.lean: THE SMALLNESS TEST's SECOND FALL IN THE HONEST SIDE's FRAME: TWO
MORE OF THE FOUR TESTS OF `ShareLive` (Johnson/P1K8R/ShareLiveOf.lean: `planesLive`, `digitsLive`:
on what the lookup on the digits has heard) HOLD AT THE STATES THAT THE FRAME's FIELD hP' HANDS,
WHERE THE LOOKUP's TWO MARKS AND THE FIT's MARKS HAVE BEEN SILENT. UNDER THE DESCRIPTION's HEAD.
Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `elems_of_quiet`   general: fit_of_quiet (Johnson/Desc/ProofFile/Honest/Law/CoverFit.lean),
      drawsFit_elems (CoverBelow.lean)
  `good_of_quiet`   general: `quiet_at_member` (Johnson/P1K8R/SymbolsAtFrame.lean), mark_silent
      (CoverFit.lean); the marks: `markK3`, `markOut`
      (Johnson/Desc/ProofFile/Honest/K3/Good/Mark.lean)
  **`step_handed`**, **`two_handed`**   general: what the field hands, as the lookup's own last
      step from a reached state, with both tests' yes at its rounds' challenges:
      `last_step_at_walk`, `last_two_at_walk` (Johnson/P1K8R/LastStepAtWalk.lean), reach_of_fold
      (Johnson/Top/H0/Walk/Reach.lean)
  **`looks_below_handed`**   l < 24: `step_handed`, `live_below_no`
      (Johnson/P1K8R/LiveAtNumber.lean)
  **`looks_head_handed`**   the head's segment: `two_handed`, `live_at_head_no`
Limits. TWO OF FOUR TESTS. The description's head h is a hypothesis; the full size alone. That the
walk returns, that its start obeys the frame's law (no field of `FirstAsks` hands that; at the
frame's authors' own choice their letter_starts and letter_tree say it), that the marks named are
among those asked and that they have been silent are premises: the chance that they speak is the
marks' own stated numbers' matter, not this file's. It is not laid into a member of `FirstAsks`
here. Nothing says that any state is reached. It stands over the files of the kind "lookup" on the
honest side.
The letter front: the list of columns that `ChainProgress.start` takes last; any list, where it stands.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.LastStepAtWalk
import Johnson.P1K8R.LiveAtNumber
import Johnson.Desc.ProofFile.Honest.K3.Good.Mark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (okRoundsE)
open Johnson.Desc.First.Walk.Tied (Reach StepYes reach_of_fold)
open ProofFile.Honest (Lay ChainProgress Mid Step walk roundsOf Mark markOf marksQuiet mark_silent walk_len
  drawsFit drawsFit_elems fit_of_quiet fitMarks)
open ProofFile.Honest.K3 (goodK3 goodK3Out LFace)
open ProofFile.Honest.K3.Good (markK3 markOut)
open P5J (AtMgA TS)

section
variable {T Cl : Type}

/-- Where the fit's marks at a list's members are among the marks asked and these have been silent,
the words of the challenges' elements are below the prime. -/
theorem elems_of_quiet (ms : List Mark) (A : List (Block T Cl))
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (fr : List Fmt.Drawn) (hn : fr.length = (A.flatMap (·.rounds)).length)
    (hq : marksQuiet ms A [] fr = true) : ∀ D ∈ fr,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
  refine drawsFit_elems _ _ (fit_of_quiet A ms ?_ A [] fr (fun _ hc => hc) hn hq)
  intro mk hmk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hmk
  exact hfit d hd

/-- **What the silence of the lookup's two marks says of its own challenges**: both tests say yes.
own: the stretch of the challenges that is the member's own. -/
theorem good_of_quiet (ms : List Mark) (A₁ A₂ : List (Block T Cl)) (blk : Block T Cl) (f : LFace)
    (h3 : markK3 blk.place f ∈ ms) (ho : markOut blk.place f ∈ ms) (fr : List Fmt.Drawn)
    (hq : marksQuiet ms (A₁ ++ blk :: A₂) [] fr = true) :
    goodK3 f ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true ∧
      goodK3Out f ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true := by
  have hs := quiet_at_member ms A₁ A₂ blk [] fr hq
  have hs' : (markOf ms blk.place ([] ++ fr.take (A₁.flatMap (·.rounds)).length)
      ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length)).isSome = false := by
    cases hc : markOf ms blk.place ([] ++ fr.take (A₁.flatMap (·.rounds)).length)
      ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) with
    | none => rfl
    | some _ =>
      rw [hc] at hs
      cases hs
  constructor
  · have hs3 : (markOf ms (markK3 blk.place f).place
        ([] ++ fr.take (A₁.flatMap (·.rounds)).length)
        ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length)).isSome = false := hs'
    have h := mark_silent h3 hs3
    have h' : (if goodK3 f ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true
      then none else some "K3: a sample at which a slot may die") = none := h
    by_cases hb : goodK3 f
      ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true
    · exact hb
    · rw [if_neg hb] at h'
      cases h'
  · have hso : (markOf ms (markOut blk.place f).place
        ([] ++ fr.take (A₁.flatMap (·.rounds)).length)
        ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length)).isSome = false := hs'
    have h := mark_silent ho hso
    have h' : (if goodK3Out f
      ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true
      then none else some "K3: a sample at which another kind's weight may die") = none := h
    by_cases hb : goodK3Out f
      ((fr.drop (A₁.flatMap (·.rounds)).length).take blk.rounds.length) = true
    · exact hb
    · rw [if_neg hb] at h'
      cases h'

/-- **WHAT THE FRAME's FIELD HANDS, AS THE LOOKUP's OWN LAST STEP.** flat: a chain's sub-protocols;
blk: the lookup's, at number n; A: the n + 1 sub-protocols in front of b. Where the lookup's two
marks and the fit's marks at A's members are among those asked and have been silent at fr, and the
walk over A's rounds at fr returns z with the verifier's state s': s' is what blk's own step returns
from a state sj that is reached at n, at rounds whose words are below the prime and at whose
challenges both of the lookup's tests say yes. -/
theorem step_handed {P W Y : Type} (flat : List (Block T Cl)) (start : P → T) (zp : P) {n : ℕ}
    {blk : Block T Cl} (hblk : flat[n]? = some blk) (ms : List Mark) (f : LFace)
    (h3 : markK3 blk.place f ∈ ms) (ho : markOut blk.place f ∈ ms)
    {A t : List (Block T Cl)} {b : Block T Cl} (hall : flat = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = n + 1) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress T Cl W Y} {s' : T}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn} {front : List Desc.OpenedColumn}
    (hm : m₀.isSome = true) (ha : ChainProgress.start L flat m₀ (some (start zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ (sj : T) (R : List Fmt.RoundView) (c : List Desc.OpenedColumn), R.length = blk.rounds.length ∧
      blk.step 0 sj R c = .ok (s', c.length) ∧ okRoundsE R = true ∧
      goodK3 f (R.map (·.drawn)) = true ∧ goodK3Out f (R.map (·.drawn)) = true ∧
      Reach 0 flat start n (zp, sj) := by
  have hlt : n < A.length := by omega
  have hA8 : A[n]? = some blk := by
    rw [hall, List.getElem?_append_left hlt] at hblk
    exact hblk
  obtain ⟨hi, e8⟩ := List.getElem?_eq_some_iff.1 hA8
  have hsp : A = A.take n ++ [blk] := by
    conv_lhs => rw [← List.take_append_drop n A, List.drop_eq_getElem_cons hi, e8]
    rw [List.drop_eq_nil_of_le (by omega)]
  have htk : A.take n = flat.take n := by
    rw [hall, List.take_append_of_le_length (Nat.le_of_lt hlt)]
  have hd := elems_of_quiet ms A hfit fr hn hq
  have hl' : ss.length = ((A.take n ++ [blk]).flatMap (·.rounds)).length := by
    rw [← hsp, ← walk_len L ss fr a z hz]
    exact hn
  have ha' : ChainProgress.start L (A.take n ++ blk :: b :: t) m₀ (some (start zp)) front = .ok a := by
    have e : A.take n ++ blk :: b :: t = flat := by
      rw [hall]
      conv_rhs => rw [hsp]
      rw [List.append_assoc]
      rfl
    rw [e]
    exact ha
  obtain ⟨sj, r₁, c₁, R, c, g1, g2, g3, g4, g5⟩ :=
    last_step_at_walk L _ t blk b hm ha' hpos hz hl' hd hv
  rw [hft] at g1 g3
  rw [htk] at g1
  have hq' := hq
  rw [hsp] at hq'
  obtain ⟨k1, k2⟩ := good_of_quiet ms _ [] blk f h3 ho fr hq'
  rw [← g5] at k1 k2
  have hle : n ≤ flat.length := by
    rw [hall, List.length_append]
    omega
  exact ⟨sj, R, c, g2, g3, g4, k1, k2, reach_of_fold n hle sj _ r₁ _ c₁ g1⟩

/-- **The like where one more sub-protocol, b₁, stands between the lookup and b.** -/
theorem two_handed {P W Y : Type} (flat : List (Block T Cl)) (start : P → T) (zp : P) {n : ℕ}
    {blk b₁ : Block T Cl} (hblk : flat[n]? = some blk) (h11 : flat[n + 1]? = some b₁)
    (ms : List Mark) (f : LFace)
    (h3 : markK3 blk.place f ∈ ms) (ho : markOut blk.place f ∈ ms)
    {A t : List (Block T Cl)} {b : Block T Cl} (hall : flat = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = n + 2) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress T Cl W Y} {s' : T}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn} {front : List Desc.OpenedColumn}
    (hm : m₀.isSome = true) (ha : ChainProgress.start L flat m₀ (some (start zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ (sj sk : T) (R : List Fmt.RoundView) (c : List Desc.OpenedColumn), R.length = blk.rounds.length ∧
      blk.step 0 sj R c = .ok (sk, c.length) ∧ okRoundsE R = true ∧
      goodK3 f (R.map (·.drawn)) = true ∧ goodK3Out f (R.map (·.drawn)) = true ∧
      StepYes 0 b₁ sk s' ∧ Reach 0 flat start n (zp, sj) := by
  have hA5 : A[n]? = some blk := by
    rw [hall, List.getElem?_append_left (by omega)] at hblk
    exact hblk
  have hA6 : A[n + 1]? = some b₁ := by
    rw [hall, List.getElem?_append_left (by omega)] at h11
    exact h11
  obtain ⟨hi5, e5⟩ := List.getElem?_eq_some_iff.1 hA5
  obtain ⟨hi6, e6⟩ := List.getElem?_eq_some_iff.1 hA6
  have hsp : A = A.take n ++ [blk, b₁] := by
    conv_lhs => rw [← List.take_append_drop n A, List.drop_eq_getElem_cons hi5, e5,
      List.drop_eq_getElem_cons hi6, e6]
    rw [List.drop_eq_nil_of_le (by omega)]
  have htk : A.take n = flat.take n := by
    rw [hall, List.take_append_of_le_length (by omega)]
  have hd := elems_of_quiet ms A hfit fr hn hq
  have hl' : ss.length = ((A.take n ++ [blk, b₁]).flatMap (·.rounds)).length := by
    rw [← hsp, ← walk_len L ss fr a z hz]
    exact hn
  have ha' : ChainProgress.start L (A.take n ++ blk :: b₁ :: b :: t) m₀ (some (start zp)) front = .ok a := by
    have e : A.take n ++ blk :: b₁ :: b :: t = flat := by
      rw [hall]
      conv_rhs => rw [hsp]
      rw [List.append_assoc]
      rfl
    rw [e]
    exact ha
  obtain ⟨sj, sk, r₁, c₁, R, c, g1, g2, g3, g4, g5, g6⟩ :=
    last_two_at_walk L _ t blk b₁ b hm ha' hpos hz hl' hd hv
  rw [hft] at g1 g3 g6
  rw [htk] at g1
  have hq' := hq
  rw [hsp] at hq'
  obtain ⟨k1, k2⟩ := good_of_quiet ms _ [b₁] blk f h3 ho fr hq'
  rw [← g5] at k1 k2
  have hle : n ≤ flat.length := by
    rw [hall, List.length_append]
    omega
  exact ⟨sj, sk, R, c, g2, g3, g4, k1, k2, g6, reach_of_fold n hle sj _ r₁ _ c₁ g1⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W Y : Type}
include h

/-- **BELOW THE HEAD's SEGMENT: TWO MORE OF `ShareLive`'s FOUR TESTS AT THE STATES THAT THE FRAME's
FIELD hP' HANDS, FROM THE SILENCE OF THE LOOKUP's TWO MARKS.** ms: the marks asked; among them the
two marks of the lookup on the digits at this segment, at the face of the public part's own built
segment (h3, ho), and the fit's marks at A's members (hfit). A: the sub-protocols in front of the
batching b. L: the walk's lay, at first tree 0; a: where the walk starts, under the frame's own law
on its start, from the description's first state. -/
theorem looks_below_handed {l : ℕ} (hl : l < 24) {X : LinkH}
    (hX : Zp.p.built.links[l]? = some X) (ms : List Mark) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[borderOf l true]? = some blk)
    (h3 : markK3 blk.place (K3.faceOf X.tl.f9) ∈ ms)
    (ho : markOut blk.place (K3.faceOf X.tl.f9) ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * l + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ tl, s'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  have hA' : A.length = borderOf l true + 1 := by
    rw [hA]
    exact (border_next hl).symm
  obtain ⟨sj, R, c, g2, g3, g4, k1, k2, hr⟩ := step_handed cF.blocksInOrder (ProofFile.startS Zp) zp hblk ms
    (K3.faceOf X.tl.f9) h3 ho hall hfit hA' hpos L hft hm ha hn hq hz hv
  exact (live_below_no h l hl hX hblk g2 g3 g4 k1 k2 hr).2

/-- **The like at the head's segment**, where the merge b₁ stands between the lookup on the digits
and the batching. -/
theorem looks_head_handed {X : LinkH} (hX : Zp.p.built.links[24]? = some X) (ms : List Mark)
    {blk b₁ : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf 24 true]? = some blk)
    (h11 : cF.blocksInOrder[346]? = some b₁)
    (h3 : markK3 blk.place (K3.faceOf X.tl.f9) ∈ ms)
    (ho : markOut blk.place (K3.faceOf X.tl.f9) ∈ ms)
    {A t : List (Block TS ProofFile.Cl)} {b : Block TS ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a z : ChainProgress TS ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : TS}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true) {front : List Desc.OpenedColumn}
    (ha : ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) front = .ok a)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a = .ok z) (hv : z.ver = some s') :
    ∃ tl, s'.tl? = some tl ∧ planesLive tl = true ∧ digitsLive tl = true := by
  have hA' : A.length = borderOf 24 true + 2 := hA
  have h11' : cF.blocksInOrder[borderOf 24 true + 1]? = some b₁ := h11
  obtain ⟨sj, sk, R, c, g2, g3, g4, k1, k2, g6, hr⟩ := two_handed cF.blocksInOrder (ProofFile.startS Zp) zp hblk
    h11' ms (K3.faceOf X.tl.f9) h3 ho hall hfit hA' hpos L hft hm ha hn hq hz hv
  exact (live_at_head_no h hX hblk h11 g2 g3 g6 g4 k1 k2 hr).2

end

end P1K8

#print axioms P1K8.elems_of_quiet
#print axioms P1K8.good_of_quiet
#print axioms P1K8.step_handed
#print axioms P1K8.two_handed
#print axioms P1K8.looks_below_handed
#print axioms P1K8.looks_head_handed
