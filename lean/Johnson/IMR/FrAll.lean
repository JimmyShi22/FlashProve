-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrAll.lean: "EVERY COPY OF THE FRAME BEHIND HAS THE CARRIED ROWS OF
A COPY IN FRONT": a relation on the first chain's state, and that every maker of the proof file's
seat but the closing keeps it. It goes beside Johnson/Goal/Meaning/RecAll.lean's RecAll, proof for
proof: there the property of a copy is FramePub; here it is a letter.
  Carr Φ: a property of a frame that reads its carried rows alone.
  EachF Φ s: Φ at every copy of the frame that s holds (framesIn s). EachF.walk, EachF.live.
  FR s t: for every such Φ: EachF Φ s → EachF Φ t.
  The writers of Johnson/Desc/First/State.lean; the links' frames (framesOf_fr); kind K1's three;
  the batching's parts, the one equation, the shutting; ef_of_quiet, whole_fr: a Quiet step.
NOT HERE: the closing (it makes new rows); kind K2's five (Johnson/IMR/FrK2.lean).
OBJECT: the makers that ProofFile.onlineDescription's value lays. USER: Johnson/IMR/RowsSent.lean.
No soundness.
-/
import Johnson.IMR.RecSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.K9
open Johnson.Desc.First.Walk

/-- A property of a frame that reads its carried rows alone. -/
def Carr (Φ : ReqFrame → Prop) : Prop := ∀ f f', Φ f → f'.rows = f.rows → Φ f'

/-- Φ at every copy of the frame that the state holds. -/
def EachF (Φ : ReqFrame → Prop) (s : S) : Prop := ∀ f ∈ framesIn s, Φ f

/-- Every property of the carried rows that all copies in front have, all copies behind have. -/
def FR (s t : S) : Prop := ∀ Φ, Carr Φ → EachF Φ s → EachF Φ t

theorem ef_refl (s : S) : FR s s := fun _ _ h => h

theorem ef_trans' (a b c : S) (h : FR a b) (k : FR b c) : FR a c :=
  fun Φ K x => k Φ K (h Φ K x)

variable {Φ : ReqFrame → Prop} {s : S} {Cl : Type}

theorem EachF.walk (R : EachF Φ s) : Φ s.check.frame := R _ List.mem_cons_self

theorem EachF.live (R : EachF Φ s) : Φ s.live.frame := by
  unfold S.live S.link?
  have F := R
  unfold EachF framesIn at F
  split
  · rename_i L hL
    split at hL
    · cases hL
      rename_i a ha
      rw [ha] at F
      exact F _ (by simp)
    · cases hL
      rename_i a ha
      rw [ha] at F
      exact F _ (by simp)
    · rename_i a ha
      rw [ha] at F
      split at hL
      · cases hL
        exact F _ (by simp)
      · cases hL
    · cases hL
  · exact R.walk

theorem ef_same {s' : S} (R : EachF Φ s) (hf : ∀ f ∈ framesIn s', f ∈ framesIn s) : EachF Φ s' :=
  fun f hm => R f (hf f hm)

theorem ef_more {s' : S} (R : EachF Φ s) (hf : ∀ f ∈ framesIn s', f ∈ framesIn s ∨ Φ f) :
    EachF Φ s' := fun f hm => (hf f hm).elim (R f) id

/-! ## State.lean's writers -/

theorem ef_mark (R : EachF Φ s) (name : String) : EachF Φ (s.mark name) := by
  refine ef_same R ?_
  unfold S.mark
  split <;> simp [framesIn]

theorem ef_unmarked {s' : S} (R : EachF Φ s) (h : s.unmarked = .ok s') : EachF Φ s' := by
  unfold S.unmarked at h
  split at h
  · cases h
    exact R
  · cases h

local macro "staysF" R:term "," d:ident : tactic =>
  `(tactic| (refine ef_same $R ?_ <;> unfold $d <;> repeat' split) <;>
    simp_all [framesIn, S.mark] <;> (repeat' split) <;> simp_all)

theorem ef_putFork (R : EachF Φ s) (F : Fork) : EachF Φ (s.putFork F) := by
  staysF R, S.putFork

theorem ef_enterMem (R : EachF Φ s) : EachF Φ s.enterMem := by
  staysF R, S.enterMem

theorem ef_enterHead (R : EachF Φ s) (tl : HTailF2) : EachF Φ (s.enterHead tl) := by
  staysF R, S.enterHead

theorem ef_enterFin (R : EachF Φ s) : EachF Φ s.enterFin := by
  staysF R, S.enterFin

theorem ef_openHead (R : EachF Φ s) : EachF Φ s.openHead := by
  staysF R, S.openHead

theorem ef_putLink (R : EachF Φ s) {L : LinkCtx} (hL : Φ L.check.frame) :
    EachF Φ (s.putLink L) := by
  refine ef_more R ?_
  unfold S.putLink
  repeat' split
  all_goals simp_all [framesIn]

theorem ef_enterLay (R : EachF Φ s) {L : LinkCtx} (hL : Φ L.check.frame) (F : Fork) (tl : HTailF2) :
    EachF Φ (s.enterLay L F tl) := by
  unfold S.enterLay
  split
  · refine ef_more R ?_
    simp_all [framesIn]
  · exact ef_mark R _

theorem ef_enterAtt (R : EachF Φ s) {L : LinkCtx} (hL : Φ L.check.frame) (F : Fork) (tl : HTailF2) :
    EachF Φ (s.enterAtt L F tl) := by
  unfold S.enterAtt
  split
  · refine ef_more R ?_
    simp_all [framesIn]
  · exact ef_mark R _

theorem ef_putLive (R : EachF Φ s) {c : ChainCheck} (hc : Φ c.frame) : EachF Φ (s.putLive c) := by
  unfold S.putLive
  split
  · exact ef_putLink R hc
  · refine ef_more R fun f hf => ?_
    unfold framesIn at hf ⊢
    rcases List.mem_cons.1 hf with rfl | hf
    · exact Or.inr hc
    · exact Or.inl (List.mem_cons_of_mem _ hf)

theorem ef_leaveLink (R : EachF Φ s) : EachF Φ s.leaveLink := by
  unfold S.leaveLink
  split
  · refine ef_more R fun f hf => ?_
    have e : f = s.live.frame := by simpa [framesIn] using hf
    rw [e]
    exact Or.inr R.live
  · exact ef_mark R _

theorem ef_out (R : EachF Φ s) (o : Proof.LinksResult) : EachF Φ { s with out := o } :=
  ef_same R fun _ h => h

/-! ## A Quiet step -/

theorem ef_of_quiet {s t : S} (q : Quiet s t) : FR s t := fun _ _ R => ef_same R q.1.2.1

theorem whole_fr {b : Block S Cl} (W : Whole Quiet b) : Whole FR b :=
  whole_mono (fun _ _ => ef_of_quiet) W

/-! ## The links' frames -/

theorem layFront_fr (l : Nat) : Fn FR (layFront l) := fun s t h _ _ R => by
  rw [(Law.layFront_ok h).1]
  exact R

theorem openAtt_fr (P : AttPar) : Fn FR (openAtt P) := fun s t h _ _ R => by
  obtain ⟨hB, -, -, -, hl, -⟩ := Law.openAtt_ok h
  unfold openAtt at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterAtt_ok (L := a.L) (F := a.F) (tl := a.tl) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact ef_unmarked (ef_enterAtt (ef_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem openLay_fr (P : LayPar) : Fn FR (openLay P) := fun s t h _ _ R => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLay_ok h
  unfold openLay at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact ef_unmarked (ef_enterLay (ef_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem openLayZero_fr (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn FR (openLayZero P fvs kCol) := fun s t h _ _ R => by
  obtain ⟨hB, -, -, -, -, hl, -⟩ := Law.openLayZero_ok h
  unfold openLayZero at h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨-, -, h⟩ := bindE h
  obtain ⟨a, -, h⟩ := bindE h
  have e := ((S.unmarked_ok _ _).1 h).1
  have hB' : ({ s with out := a.out } : S).atBetween = true := hB
  have k := (Law.enterLay_ok (L := a.L) (F := a.F) (tl := P.tl₀) hB').1
  rw [e, hl] at k
  have eL : a.L.check = s.check := by rw [← Option.some.inj k]
  exact ef_unmarked (ef_enterLay (ef_out R a.out) (by rw [eL]; exact R.walk) _ _) h

theorem clearWith_fr (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) : Fn FR (clearWith X counts left row) :=
  fun s t h Φ _ R => by
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · exact ef_unmarked (ef_leaveLink R) h
    · split at h
      · cases h
      · rename_i r os _
        have R' : EachF Φ
            ({ s with out := pendingKept s.out r, st := { s.st with oracles := os } } : S) :=
          ef_same R fun _ hm => hm
        exact ef_unmarked (ef_leaveLink R') h
  · cases h

theorem tailHead_fr (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    Fn FR (Close.tailHead X lay lin) := clearWith_fr _ _ _ _

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_fr {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn FR f.lay ∧ Fn FR f.opened ∧ Fn FR f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨layFront_fr l, fun s t k _ _ R => by cases k; exact R, tailHead_fr _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_fr 0, openLayZero_fr _ _ _, clearWith_fr _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_fr l, openAtt_fr _, clearWith_fr _ _ _ _⟩
      · cases e
        exact ⟨layFront_fr l, openLay_fr _, clearWith_fr _ _ _ _⟩

/-! ## Kind K1 -/

theorem sendAtS_fr (P : K1.Par) : Whole FR (sendAtS (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h _ _ R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  refine ef_same R ?_
  simp only [sendAtS] at h
  split at h
  · rename_i a ha
    split at h
    · obtain ⟨y, -, rfl⟩ := Keeps.emap_ok h
      intro f hf
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
    · cases h
  · cases h

theorem commitAtS_fr (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole FR (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h Φ K R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    have hfr : SamePub L.check.frame y.held.L.check.frame := by
      simp only [commitOwn] at hy
      split at hy
      · split at hy
        · cases hy
        · obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hy
          exact commitStep_frame hx
      · cases hy
    have hLive : Φ L.check.frame := by
      have k := R.live
      unfold S.live at k
      rw [hL] at k
      exact k
    have R1 : EachF Φ (laid s y.held.w) := ef_same R fun _ hm => hm
    exact ef_putFork (ef_putLink R1 (K _ _ hLive hfr.2.2.1)) y.held.F
  · cases h

theorem firstAtS_fr (q : Params.First) (gp : GPar) : Whole FR (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h Φ K R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  have hf := K _ _ R.walk (firstOwn_frame h1).2.2.1
  intro f hm
  unfold framesIn at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact hf
  · exact R f (List.mem_cons_of_mem _ hm)

theorem laterAt_fr (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole FR (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_fr _ link moment arrays

/-! ## The batching, the one equation, the shutting -/

theorem link_fr (R : EachF Φ s) {L : LinkCtx} (h : s.link? = some L) : Φ L.check.frame := by
  have k := R.live
  unfold S.live at k
  rw [h] at k
  exact k

theorem atS_set_fr (R : EachF Φ s) {p : K9.Part} (hL : Φ p.L.check.frame) : EachF Φ (atS.set s p) :=
  ef_putFork (ef_putLink R hL) p.F

theorem drawAlone_fr (p : Where) : Decides FR (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h Φ _ R
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨chi, _, h⟩ := bindE h
    obtain ⟨o, ho, h⟩ := bindE h
    cases h
    obtain ⟨g1, g2⟩ := atS_get (there_some hq)
    refine atS_set_fr R ?_
    show Φ o.L.check.frame
    rw [drawn_L ho]
    exact link_fr R g1
  · cases h

theorem oneEquation_fr (p : Where) : Whole FR (oneEquation (Cl := Cl) atS p) := by
  refine ⟨fun s rs gs s' h Φ _ R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨g1, g2⟩ := atS_get (there_some hq)
  obtain ⟨d1, d2⟩ := door_keeps ho
  refine atS_set_fr R ?_
  show Φ o.L.check.frame
  rw [d1]
  exact link_fr R g1

theorem shut_fr (p : K9.Where) (piece : Nat) : Whole FR (K9.shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h Φ _ R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  have hl : s.link? = some L := by
    cases e : s.link? with
    | none =>
      rw [e] at hL
      cases hL
    | some L' =>
      rw [e] at hL
      exact congrArg some (Except.ok.inj hL)
  have k : Φ L.check.frame := link_fr R hl
  exact ef_putLink R (L := K9.closed L L.check.frame) k

#print axioms framesOf_fr
#print axioms commitAtS_fr
#print axioms firstAtS_fr
#print axioms drawAlone_fr
#print axioms oneEquation_fr
#print axioms shut_fr

end Meaning.K2
