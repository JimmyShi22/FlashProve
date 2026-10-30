-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/TailOpen.lean: what the program has done with the part of a key file or a proof file
behind its first chain, if the reading returns and the decision says yes: every step of
`Proof.readTail` and `Proof.tailRefusal` as a named fact, down to calls of `Proof.readPlace`,
`tableKey`, the dry runs, the descriptions' makers and the strict reader, which stay closed here.

"The program" is the Lean program `verify-on-bytes`. A key file and a proof file hold three chains.
`Proof.readTail` (OnBytes/Proof/Tail.lean) reads what stands behind the first: the place in the
binding tree, the shared chain, the second chain. `Proof.tailRefusal` decides on the two later
chains' views. This file proves no more than what these two texts say, as one statement each, so
that a tie from the program's yes to another verifier's yes can begin at named facts.

`TailFacts` lists the facts of a reading that has returned:
  - the first chain is the one that was handed in, and it has a seal;
  - the place was read behind the first chain, under the shared chain's digest of the public files
    and the first chain's seal;
  - the table's key is made of the table, at the number 0;
  - the shared chain's rounds come from a dry run of its block at that key; its description is made
    of them, the table and the binding tree's root as read;
  - the strict reader has read the shared chain under that description, from the byte behind the
    place, in the session as the caller left it;
  - the shared chain has a seal;
  - the second chain's rounds come from the rounds of its block at what the dry run of the first
    chain's block and the dry run of the shared chain's block have returned, with both chains' trees
    named by root and start as read; its description is made of them, both seals, and the number of
    its first own tree;
  - the strict reader has read the second chain under that description, from the byte behind the
    shared chain, in the session that the shared chain's reading left: one record of vertices.
`TailYes` lists the facts of a decision that said yes: the shared chain's block accepts its view and
returns an end; the second chain's block, at what the first chain's block has returned on its view
and at that end, accepts its view.

Main definitions: `TailFacts`, `TailYes`.
Main theorems: `readTail_open`, `tailRefusal_open`.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.Tie.KeyFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- The facts of a tail's reading that has returned r, from the session s to the session s'. -/
structure TailFacts (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    (s s' : Session) (r : TailRead) (seal1 seal2 : ByteArray) (rounds2 : Params.Rounds)
    (end2 : SharedEnd) (spec2 : Fmt.SpecX) (s2 : Session) (rounds3 : Params.Rounds)
    (spec3 : Fmt.SpecX) : Prop where
  first_eq : r.first = first
  seal_first : first.seal = some seal1
  place_read : readPlace p.binding p.shared.given.cfg seal1 b first.next = some r.place
  key_made :
    tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index p.table 0 = some r.key
  shared_dry : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (rounds2, end2)
  shared_spec : p.shared.describe p.lab₂ p.table r.place.root rounds2 = some spec2
  shared_read : readIn spec2 b r.place.next s = some (r.shared, s2)
  seal_shared : r.shared.seal = some seal2
  second_rounds :
    (secondBlock p.lin dry.lin (end2.goesOn r.shared)).rounds (secondStart p dry first) =
      some rounds3
  second_spec : p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first) = some spec3
  second_read : readIn spec3 b r.shared.next s2 = some (r.second, s')

/-- **What `readTail` has done if it returns.** -/
theorem readTail_open (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    (s s' : Session) (r : TailRead) (h : readTail p dry first b s = .ok (r, s')) :
    ∃ seal1 seal2 rounds2 end2 spec2 s2 rounds3 spec3,
      TailFacts p dry first b s s' r seal1 seal2 rounds2 end2 spec2 s2 rounds3 spec3 := by
  unfold readTail at h
  obtain ⟨seal1, t1, h1, g1⟩ := bind_ok _ _ _ _ _ h
  obtain ⟨e1, rfl⟩ := need_ok _ _ _ _ _ h1
  obtain ⟨place, t2, h2, g2⟩ := bind_ok _ _ _ _ _ g1
  obtain ⟨e2, rfl⟩ := need_ok _ _ _ _ _ h2
  obtain ⟨key, t3, h3, g3⟩ := bind_ok _ _ _ _ _ g2
  obtain ⟨e3, rfl⟩ := need_ok _ _ _ _ _ h3
  obtain ⟨⟨rounds2, end2⟩, t4, h4, g4⟩ := bind_ok _ _ _ _ _ g3
  obtain ⟨e4, rfl⟩ := need_ok _ _ _ _ _ h4
  dsimp only at g4
  obtain ⟨spec2, t5, h5, g5⟩ := bind_ok _ _ _ _ _ g4
  obtain ⟨e5, rfl⟩ := need_ok _ _ _ _ _ h5
  obtain ⟨shared, s2, h6, g6⟩ := bind_ok _ _ _ _ _ g5
  have e6 := readNamed_ok _ _ _ _ _ _ _ h6
  obtain ⟨seal2, t7, h7, g7⟩ := bind_ok _ _ _ _ _ g6
  obtain ⟨e7, rfl⟩ := need_ok _ _ _ _ _ h7
  obtain ⟨rounds3, t8, h8, g8⟩ := bind_ok _ _ _ _ _ g7
  obtain ⟨e8, rfl⟩ := need_ok _ _ _ _ _ h8
  obtain ⟨spec3, t9, h9, g9⟩ := bind_ok _ _ _ _ _ g8
  obtain ⟨e9, rfl⟩ := need_ok _ _ _ _ _ h9
  obtain ⟨second, t10, h10, g10⟩ := bind_ok _ _ _ _ _ g9
  have e10 := readNamed_ok _ _ _ _ _ _ _ h10
  injection g10 with hr
  have hr1 : (⟨first, place, key, shared, second⟩ : TailRead) = r := congrArg (·.1) hr
  have hr2 : t10 = s' := congrArg (·.2) hr
  subst hr1
  subst hr2
  exact ⟨_, _, _, _, _, _, _, _, ⟨rfl, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩⟩

/-- The facts of a decision on a tail's two views that said yes. real: what the first chain's block
has returned on the first chain's view. -/
structure TailYes (p : TailPublic) (real : FirstEnd) (r : TailRead) (end2 : SharedEnd) : Prop where
  shared_yes : (sharedBlock p.lin r.key).runOn (sharedStart p) r.shared.view = .ok end2
  second_yes :
    (secondBlock p.lin real.lin (end2.goesOn r.shared)).runOn (secondStart p real r.first)
      r.second.view = .ok ()

/-- If `judge` returns a value, the block's run on the view has returned it. -/
theorem judge_ok {α : Type} (front : String) (b : Blk α) (s : Start) (v : Fmt.View) (a : α)
    (h : judge front b s v = .ok a) : b.runOn s v = .ok a := by
  unfold judge at h
  split at h
  · rename_i a' ha
    injection h with h'
    rw [ha, h']
  · cases h

/-- **What `tailRefusal` has found if it says yes.** -/
theorem tailRefusal_open (p : TailPublic) (real : FirstEnd) (r : TailRead)
    (h : tailRefusal p real r = none) : ∃ end2, TailYes p real r end2 := by
  unfold tailRefusal at h
  split at h
  · cases h
  · rename_i end2 h2
    split at h
    · cases h
    · rename_i h3
      exact ⟨end2, judge_ok _ _ _ _ _ h2, judge_ok _ _ _ _ _ h3⟩

end OnBytes.TieK
