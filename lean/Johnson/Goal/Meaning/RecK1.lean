-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK1.lean: kind K1's three blocks at the first chain's record hand RecAll on
(Johnson/Goal/Meaning/RecAll.lean; RecRel, Johnson/Goal/Meaning/RecRel.lean).

The codes: by the kind's own laws (Johnson/Desc/K1/KeepsAtS.lean: the three blocks keep every
relation that the ground's plain functions keep) at the relation Grows, whose first clause is
"the same codes". The copies of the frame: by the blocks' texts: a sending writes the frame's fields
group, moment, own, plain, mask, atStart and next, never shape or groups.
  joinOwn_frame: joinOwnP leaves the frame's shape and groups.
  laterOwn_frame, firstOwn_frame: so do the two decisions on the state of the calls.
  commitStep_frame: so the link's own copy behind a commitment.
  sendAtS_rec, commitAtS_rec, firstAtS_rec: Whole (RecRel cs sh) of the three blocks.
Not claimed: anything on another kind's blocks.
OBJECT: the makers' blocks and steps that are named above. USER: the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border), at the letters cs and sh: it asks
Decides (RecRel cs sh) of every block of a list; that list is not laid yet. Which maker stands
at which place of a seated text is not said here.
-/
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.GroundKeeps
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.Keeps (Whole Decides)
open VerifiableInference.Desc.Ground (groundKeeps_grows By)
open VerifiableInference.Desc.K1

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

/-- The two frames have one shape, the same groups, the same carried rows and one link. -/
def SamePub (f f' : ReqFrame) : Prop :=
  f'.shape = f.shape ∧ f'.groups = f.groups ∧ f'.rows = f.rows ∧ f'.link = f.link

theorem FramePub.of_same {f f' : ReqFrame} (h : FramePub sh f) (e : SamePub f f') :
    FramePub sh f' := h.carry e.1 e.2.1 e.2.2.1 e.2.2.2

theorem joinOwn_frame {L : Type} {G : Desc.Plain.Ground L} {p : GPar} {d d' : DState L}
    {f f' : ReqFrame} {sent : List ReqMessage} {ids : Array Nat}
    (h : joinOwnP G p d f sent ids = some (f', d')) : SamePub f f' := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨x, -, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

theorem laterOwn_frame {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {w w' : DState Unit}
    {rs : List Fmt.RoundView} (h : laterOwn P owed c w rs = .ok (c', w')) : SamePub c.frame c'.frame := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i y hj
            cases h
            have k := joinOwn_frame (f' := y.1) (d' := y.2) hj
            exact ⟨k.1, k.2.1, k.2.2.1, k.2.2.2⟩

theorem firstOwn_frame {P : K1.Par} {owed : Option Nat} {c c' : ChainCheck} {d d' : DState Unit}
    {rs : List Fmt.RoundView} (h : firstOwn P owed c d rs = .ok (c', d')) : SamePub c.frame c'.frame := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨g, d₁⟩, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨ids, d₂⟩, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨mask, _, h⟩ := bindE h
  obtain ⟨⟨f₂, d₃⟩, hj, h⟩ := bindE h
  cases h
  have k := joinOwn_frame (Keeps.named_ok hj)
  exact ⟨k.1, k.2.1, k.2.2.1, k.2.2.2⟩

/-- The link's own copy behind a commitment. -/
theorem commitStep_frame {P : K1.Par} {owed : Option Nat} {ts : List Nat}
    {x y : L3.St (DState Unit)} {rs : List Fmt.RoundView}
    (h : L3.commitStep (laterOwn P owed) ts x rs = .ok y) :
    SamePub x.L.check.frame y.L.check.frame := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨check, w⟩, h1, h⟩ := bindE h
  obtain ⟨⟨L, F⟩, h2, h⟩ := bindE h
  cases h
  unfold L3.commitBehind at h2
  obtain ⟨F', _, h2⟩ := bindE h2
  split at h2
  · cases h2
    exact laterOwn_frame h1
  · cases h2

/-- The codes behind a block that grows the statement. -/
theorem codes_of_grows {b : Block S Cl} (G : Decides (By Grows fun s : S => s.st) b) {s s' : S}
    {rs gs} (h : b.decide s rs gs = .ok s') : s'.st.codes = s.st.codes := (G s rs gs s' h).1

/-- **W's sending, at the record.** -/
theorem sendAtS_rec (P : K1.Par) : Whole (RecRel cs sh) (sendAtS (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have hc := codes_of_grows (Rel.sendAtS_keeps groundKeeps_grows P) h
  refine same_frames R hc ?_
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

/-- **A segment's later moment, at the record.** -/
theorem commitAtS_rec (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole (RecRel cs sh) (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have hc := codes_of_grows (Rel.commitAtS_keeps groundKeeps_grows P link moment arrays) h
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
    have hLive : FramePub sh L.check.frame := by
      have k := R.live
      unfold S.live at k
      rw [hL] at k
      exact k
    have e : (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st = y.held.w.st := by
      rw [Rel.putFork_st, Rel.putLink_st]
      rfl
    rw [e] at hc
    have R1 : RecAll cs sh (laid s y.held.w) := same_frames R hc fun _ hm => hm
    exact recAll_putFork (recAll_putLink R1 (hLive.of_same hfr)) y.held.F
  · cases h

/-- **The first segment's opening, at the record.** -/
theorem firstAtS_rec (q : Params.First) (gp : GPar) :
    Whole (RecRel cs sh) (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have hc := codes_of_grows (Rel.firstAtS_keeps groundKeeps_grows q gp) h
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  have hf := R.walk.of_same (firstOwn_frame h1)
  refine ⟨hc.trans R.codes, fun f hm => ?_, R.ok⟩
  unfold framesIn at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact hf
  · exact R.frames f (List.mem_cons_of_mem _ hm)

#print axioms sendAtS_rec
#print axioms commitAtS_rec
#print axioms firstAtS_rec

end Meaning.K2
