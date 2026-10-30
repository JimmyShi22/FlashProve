-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawReadyAtt.lean: THE SMALLNESS TEST AT AN ATTENTION LINK: WHEREVER THE FOLD
OVER THE BLOCKS IN FRONT OF THE DRAW GOES ON, THE BLOCK OF THE DRAW SAYS YES: FROM WHAT EACH OF
THESE BLOCKS OWES.

At a layers' link and at the head's the step that closes the list of tables lays the place's own
parameter (Johnson/Desc/First/K8/LawReadyText.lean). AT AN ATTENTION LINK IT DOES NOT: its text
(Johnson/Desc/First/Att/ReadsO.lean: `readsAtO`) closes THE CARRIED RECORD of the smallness test.
So there the record that the link's frame laid must come through the blocks in front unturned in
what the draw's tests read:
  `Ready.Closes c`: what such a closing block gives: it leaves `keep` (five fields of the carried
    record); where its decision goes on the mark "closed" stands behind it; if no count waited in
    front, none waits behind.
  `attO_closes`: **every block `readsAtO W l g` has it**: by `K5Law.reads_next_o`
    (Johnson/Desc/First/Att/Claims/ReadsNextO.lean) and the make of `closeFuns`.
  `Closes.behind`, `Closes.guards`, `Closes.under`: it passes to the step joined behind a block with
    `LeavesFront`, to a guarded block (`Guards`, Johnson/Desc/First/K8/LawSeated.lean), and along
    `Block.Under` (a yes of c is the same yes of b): what a seat's block has.
  `fold_readings_att`, `ready_of_fold_att`: **the assembly over the frame's fold**: pre and post:
    blocks with `LeavesFront`; c with `Closes`: wherever the fold over them goes on from a record s0
    at which the smallness test's record is tl0 and no count waits, all nine clauses of `MeansAtS`
    hold behind it, if tl0 is undrawn and has the place's numbers and the closed list behind the
    fold has the place's shapes. `ready_at_att`: the same at any c under `readsAtO W l g`
    joined behind a block own.
Statements and proofs.
Limits. `LeavesFront` is shown of no block here: each is owed for its own block. THE FOLD BEGINS
BEHIND THE LAYING OF THE RECORD: that the link's frame lays the plan's record there and leaves no
count waiting is the frame's. The six facts on tl0 are facts on public numbers: none is shown at a
value. THAT THE CLOSED LIST HAS THE PLACE'S SHAPES (`tabs p`) IS A PREMISE ON THE RECORD BEHIND THE
FOLD: a law on the tables that the step makes. Of completeness's kind: no error term; nothing on
soundness.

-/
import Johnson.Desc.First.K8.LawReadyText
import Johnson.Desc.First.Att.Claims.ReadsNextO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- What a block that closes the carried record's list gives. -/
def Closes {Cl : Type} (c : Block S Cl) : Prop :=
  c.Leaves keep ∧ c.Lays closedAt (fun _ => some true) ∧ KeepsWaits c

/-- What `L3.closeStep` returns, written out. -/
theorem closeStep_tl {funs : Array HFun} {x c : L3.St Unit} (h : L3.closeStep funs x = .ok c) :
    c.tl = { x.tl with funClosed := true, funs := funs } := by
  unfold L3.closeStep HTailF2.closeFuns at h
  cases hx : x.tl.funClosed with
  | true => simp [hx] at h
  | false =>
    simp only [hx, Bool.false_eq_true, if_false] at h
    cases h
    rfl

/-- A yes of the step at the state. -/
theorem attO_yes (A : Attention.Plan) (s s' : S) (h : Att.readsAtSO A s = .ok s') :
    ∃ tl funs, s.tl? = some tl ∧ s'.tl? = some { tl with funClosed := true, funs := funs } ∧
      s'.rowsOwed = s.rowsOwed := by
  obtain ⟨a, _, _, _, t, c, ha, _, _, _, _, hc, rfl⟩ := K5Law.reads_next_o A s s' h
  refine ⟨a.tl, (Att.tabsBack t).funs, ?_, ?_, rfl⟩
  · simp [S.tl?, ha]
  · have e := closeStep_tl hc
    simp only [S.tl?]
    rw [e]

/-- **Every block `readsAtO W l g` has `Closes`.** -/
theorem attO_closes {Cl : Type} (W : Verify.Public) (l g : Nat) (z : Block S Cl)
    (hz : Att.readsAtO (Cl := Cl) W l g = some z) : Closes z := by
  unfold Att.readsAtO at hz
  cases hA : W.A[g]? with
  | none => simp [hA] at hz
  | some A =>
    simp only [hA, Option.map_some, Option.some.injEq] at hz
    subst hz
    refine ⟨fun s rs gs s' hd => ?_, fun s rs gs s' hd => ?_, fun s rs gs s' hd hw => ?_⟩
    · obtain ⟨tl, funs, h1, h2, _⟩ := attO_yes A s s' hd
      unfold keep
      rw [h1, h2]
      rfl
    · obtain ⟨tl, funs, _, h2, _⟩ := attO_yes A s s' hd
      unfold closedAt
      rw [h2]
      rfl
    · obtain ⟨_, _, _, _, h3⟩ := attO_yes A s s' hd
      unfold S.noneWaits at hw ⊢
      rw [h3]
      exact hw

/-- Joined behind a block with `LeavesFront`. -/
theorem Closes.behind {Cl : Type} {q : Block S Cl} (h : Closes q) (own : Block S Cl)
    (ho : LeavesFront own) (name : String) : Closes (Block.andThen name own q) := by
  refine ⟨leavesAndThen S Cl _ keep name own q ho.1 h.1, fun s rs gs s' H => ?_,
    fun s rs gs s' H hw => ?_⟩
  · obtain ⟨t, _, H⟩ :=
      bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) H
    exact h.2.1 _ _ _ _ H
  · obtain ⟨t, ht, H⟩ :=
      bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) H
    exact h.2.2 _ _ _ _ H (ho.2.2 _ _ _ _ ht hw)

theorem Closes.guards {Cl : Type} {c b : Block S Cl} (h : Closes b) (g : Guards c b) : Closes c :=
  ⟨g.leaves h.1, g.lays h.2.1, h.2.2.guards g⟩

theorem Closes.under {Cl Cl' : Type} {c : Block S Cl'} {b : Block S Cl} (h : Closes b)
    (u : c.Under b) : Closes c :=
  ⟨leaves_of_under u h.1, fun s rs gs s' hd => h.2.1 s rs gs s' (u s rs gs s' hd), h.2.2.under u⟩

/-- The three readings behind the fold. -/
theorem fold_readings_att {Cl : Type} (pre : List (Block S Cl)) (c : Block S Cl)
    (post : List (Block S Cl)) (hm : ∀ b ∈ pre, LeavesFront b) (hc : Closes c)
    (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S) (rs : List Fmt.RoundView)
    (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out) :
    keep out.1 = keep s0 ∧ closedAt out.1 = some true ∧
      (s0.noneWaits = true → out.1.noneWaits = true) := by
  refine ⟨?_, ?_, ?_⟩
  · refine foldLeaves S Cl _ keep ft (pre ++ c :: post) s0 rs cols out (fun b hb => ?_) H
    rcases List.mem_append.1 hb with h | h
    · exact (hm b h).1
    · rcases List.mem_cons.1 h with h | h
      · rw [h]
        exact hc.1
      · exact (hp b h).1
  · exact foldLays S Cl _ closedAt (fun _ => some true) ft pre c post s0 rs cols out hc.2.1
      (fun b h => (hp b h).2.1) H
  · refine foldKeeps (fun s : S => s.noneWaits = true) ft (pre ++ c :: post) s0 rs cols out
      (fun b hb => ?_) H
    rcases List.mem_append.1 hb with h | h
    · exact (hm b h).2.2
    · rcases List.mem_cons.1 h with h | h
      · rw [h]
        exact hc.2.2
      · exact (hp b h).2.2

/-- **The assembly over the frame's fold, where the closing step closes the carried record.** -/
theorem ready_of_fold_att {Cl : Type} (p : Par) (pre : List (Block S Cl)) (c : Block S Cl)
    (post : List (Block S Cl)) (hm : ∀ b ∈ pre, LeavesFront b) (hc : Closes c)
    (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S) (rs : List Fmt.RoundView)
    (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out)
    (tl0 : HTailF2) (h0 : s0.tl? = some tl0) (hw : s0.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s', MeansAtS p out.1 r s' := by
  obtain ⟨hk, hcl, hn⟩ := fold_readings_att pre c post hm hc hp ft s0 rs cols out H
  refine means_of_values p out.1 tl0 ?_ hcl (hn hw) c1 c2 d e e' f t r
  rw [hk]
  unfold keep
  rw [h0]
  rfl

/-- The same at an attention link's step as it is seated. -/
theorem ready_at_att (p : Par) (W : Verify.Public) (l g : Nat) (z own c : Block S Unit)
    (hz : Att.readsAtO (Cl := Unit) W l g = some z) (ho : LeavesFront own) (name : String)
    (gd : c.Under (Block.andThen name own z)) (pre post : List (Block S Unit))
    (hm : ∀ b ∈ pre, LeavesFront b) (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out)
    (tl0 : HTailF2) (h0 : s0.tl? = some tl0) (hw : s0.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s', MeansAtS p out.1 r s' :=
  ready_of_fold_att p pre c post hm (((attO_closes W l g z hz).behind own ho name).under gd) hp ft
    s0 rs cols out H tl0 h0 hw c1 c2 d e e' f t r

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.attO_yes
#print axioms VerifiableInference.Desc.First.K8.Ready.attO_closes
#print axioms VerifiableInference.Desc.First.K8.Ready.Closes.behind
#print axioms VerifiableInference.Desc.First.K8.Ready.fold_readings_att
#print axioms VerifiableInference.Desc.First.K8.Ready.ready_of_fold_att
#print axioms VerifiableInference.Desc.First.K8.Ready.ready_at_att
