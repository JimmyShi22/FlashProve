-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK9.lean: kind K9's blocks at the first chain's record (the batching draw,
the adding of claims, the batching, the one equation) hand RecAll on; and so what closes a segment,
block by block and as one block (Johnson/Desc/First/Batch/Kind.lean, AtS.lean, Place.lean).

These blocks read and write the record through the lens K9.atS: the segment's book-keeping L, its
ledger F, the statement and the rows owed.
  atS_get: the part's L is the open link's record, its statement the record's.
  atS_set_rec: laying back a part whose L holds a frame with FramePub and whose statement has the
    plan's codes gives RecAll.
  door_keeps: the door leaves L; the statement behind it has the same codes (by the library's
    takeMaskP_grows and addRowP_grows, Johnson/Desc/GrowsGround.lean).
  drawAlone_rec, oneEquation_rec: Whole (RecRel cs sh).
  adds_rec, batch_rec: Decides (RecRel cs sh), for every function of claims that is
    FnCl (RecRel cs sh): the form in which Johnson/Desc/FoldKeeps.lean's LinkKeeps asks it.
  closeOf_rec, joint_rec: with closing_rec and shut_rec (Johnson/Goal/Meaning/RecK10.lean).
Not claimed: that the other kinds' runs of claims are FnCl (RecRel cs sh).
OBJECT: the makers' blocks and steps that are named above. USER: the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border), at the letters cs and sh: it asks
Decides (RecRel cs sh) of every block of a list; that list is not laid yet. Which maker stands
at which place of a seated text is not said here.
-/
import Johnson.Goal.Meaning.RecK10
import Johnson.Desc.GrowsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides FnCl)
open VerifiableInference.Desc.K9

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

theorem there_some {α : Type} {n : String} {o : Option α} {x : α} (h : there n o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => exact congrArg some (Except.ok.inj h)

/-- What the lens reads. -/
theorem atS_get {s : S} {p : K9.Part} (h : atS.get? s = some p) :
    s.link? = some p.L ∧ p.d.st = s.st := by
  simp only [atS] at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        cases hu : usedOf s with
        | none => simp [hL, hF, ht, hu] at h
        | some u =>
          simp only [hL, hF, ht, hu, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩

/-- The open link's own copy. -/
theorem link_frame {s : S} (R : RecAll cs sh s) {L : LinkCtx} (h : s.link? = some L) :
    FramePub sh L.check.frame := by
  have k := R.live
  unfold S.live at k
  rw [h] at k
  exact k

/-- What the lens writes. -/
theorem atS_set_rec {s : S} (R : RecAll cs sh s) {p : K9.Part}
    (hL : FramePub sh p.L.check.frame) (hc : p.d.st.codes = cs) : RecAll cs sh (atS.set s p) :=
  ⟨hc, (recAll_putFork (recAll_putLink R hL) p.F).frames, R.ok⟩

theorem takeN_codes {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (y : List Nat × St X), takeN o n d acc = .ok y → y.2.st.codes = d.st.codes
  | 0, d, acc, y, h => by
    cases h
    rfl
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact (takeN_codes o n x.2 _ y h).trans
      (Ground.takeMaskP_grows d x.2 o x.1 (there_some hx)).1

theorem asRow_codes {X : Type} {Rw : ReqRows} {f : ReqFrame} {q : Equation} {d : St X}
    {y : Row × St X} (h : asRow Rw f q d = .ok y) : y.2.st.codes = d.st.codes := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    rfl
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_codes o _ d [] x hx

/-- The door leaves the segment's book-keeping, and the codes. -/
theorem door_keeps {X : Type} {owed : RowsOwed} {laid : Option Nat} {L : LinkCtx} {F : Fork}
    {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    o.L = L ∧ o.d.st.codes = d.st.codes := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact ⟨rfl, (Ground.addRowP_grows y.2 d' _ y.1 (there_some hd)).1.trans (asRow_codes hy)⟩

theorem drawn_L {rows : Nat} {chi : E} {owed : RowsOwed} {used : Nat} {L : LinkCtx} {F : Fork}
    {o : Drawn} (h : drawnClean rows chi owed used L F = .ok o) : o.L.check = L.check := by
  unfold drawnClean at h
  obtain ⟨o', h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  unfold drawn at h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  cases h1
  rfl

/-- **The batching draw.** -/
theorem drawAlone_dec (p : Where) : Decides (RecRel cs sh) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h R
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨chi, _, h⟩ := bindE h
    obtain ⟨o, ho, h⟩ := bindE h
    cases h
    obtain ⟨g1, g2⟩ := atS_get (there_some hq)
    refine atS_set_rec R ?_ ?_
    · show FramePub sh o.L.check.frame
      rw [drawn_L ho]
      exact link_frame R g1
    · show q.d.st.codes = cs
      rw [g2]
      exact R.codes
  · cases h

theorem drawAlone_rec (p : Where) : Whole (RecRel cs sh) (drawAlone (Cl := Cl) atS p) :=
  ⟨drawAlone_dec p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **Claims made and added.** -/
theorem adds_rec (p : Where) (piece : Nat) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (RecRel cs sh) claims) :
    Decides (RecRel cs sh) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h R
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  have R1 : RecAll cs sh x.2 := hcl s x hx R
  obtain ⟨g1, g2⟩ := atS_get (there_some hq)
  refine atS_set_rec R1 (link_frame R1 g1) ?_
  show q.d.st.codes = cs
  rw [g2]
  exact R1.codes

/-- **The batching**, in the form in which LinkKeeps asks it. -/
theorem batch_rec (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (RecRel cs sh) claims) : Decides (RecRel cs sh) (batch atS p claims) := by
  intro s rs gs s' h R
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact adds_rec p p.piece "the segment's" hcl t₁ [] [] s' h (drawAlone_dec p s rs gs t₁ h1 R)

/-- **The one equation.** -/
theorem oneEquation_dec (p : Where) : Decides (RecRel cs sh) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h R
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨g1, g2⟩ := atS_get (there_some hq)
  obtain ⟨d1, d2⟩ := door_keeps ho
  refine atS_set_rec R ?_ ?_
  · show FramePub sh o.L.check.frame
    rw [d1]
    exact link_frame R g1
  · show o.d.st.codes = cs
    rw [d2, g2]
    exact R.codes

theorem oneEquation_rec (p : Where) : Whole (RecRel cs sh) (oneEquation (Cl := Cl) atS p) :=
  ⟨oneEquation_dec p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **What closes a segment, block by block.** -/
theorem closeOf_rec (p : Where) (P : Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, Decides (RecRel cs sh) b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_dec (Cl := Cl) p
  · exact (closing_rec P).1
  · exact (shut_rec p _).1

/-- **The same as one block.** -/
theorem joint_rec (p : Where) (P : Close.Par) : Decides (RecRel cs sh) (joint (Cl := Cl) p P) :=
  fun s rs gs s' h =>
    Keeps.andThen_decides (RecRel cs sh) (recRel_trans cs sh)
      s!"the one equation and the closing of segment {p.link}" _ _
      (Keeps.andThen_decides (RecRel cs sh) (recRel_trans cs sh) "the one equation and the closing"
        _ _ (oneEquation_dec (Cl := Cl) p) (closing_rec P).1)
      (shut_rec p (P.piece + 1)).1 s rs gs s' h

#print axioms drawAlone_rec
#print axioms batch_rec
#print axioms oneEquation_rec
#print axioms closeOf_rec
#print axioms joint_rec

end Meaning.K2
