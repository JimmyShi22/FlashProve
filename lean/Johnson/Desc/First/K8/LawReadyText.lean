-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawReadyText.lean: THE SMALLNESS TEST: BEHIND THE STEP THAT CLOSES THE LIST OF
TABLES, AS ITS TEXT STANDS IN THIS LIBRARY, THE BLOCK OF THE DRAW SAYS YES: FROM "NO COUNT WAITS" IN
FRONT, SIX FACTS ON THE PLACE'S OWN PARAMETER, AND THE CLOSED LIST'S SHAPES.

THE TEXT OF THAT STEP IN THIS LIBRARY (Johnson/Desc/K8/ReadsQuiet.lean: `layers P`, `head P`) closes
THE PLAN'S RECORD, a public parameter of its place (`P.tl`, `P.hp.tl`), and LAYS the outcome over
whatever the carried record held. So the blocks in front of it need not keep any field of the
carried record of the smallness test (`Ready.keep`, `Ready.closedAt` of
Johnson/Desc/First/K8/LawReadyRow.lean are owed by blocks BEHIND it alone):
  `Ready.ClosesFrom tl0 c`: where the decision of c goes on, the record of the smallness test
    behind it is tl0 with the mark "closed" laid and some list in the list's place; and if no count
    waited in front, none waits behind.
  `layers_closesFrom`, `head_closesFrom`: **the two blocks of ReadsQuiet.lean have it**, at their
    places' own parameters: by `layers_ok`, `head_ok`, `closed_ok`, `layers_frame`, `head_frame`
    (Johnson/Desc/K8/ReadsQuietLaws.lean).
  `means_of_closesFrom`: right behind such a block, if no count waited in front of it and tl0 is
    undrawn and has the place's numbers, all nine clauses of `MeansAtS` hold at every round.
  `Ready.KeepsWaits b`: ALL THAT A BLOCK IN FRONT OF THE CLOSING THEN OWES: if no count waited in
    front of it, none waits behind.
  `foldKeeps`: a fold over blocks each of which keeps a property of the record keeps it.
  `ClosesFrom.behind`, `ClosesFrom.guards`, `KeepsWaits.guards`, `LeavesFront.guards`: THE STEP IS
    SEATED BEHIND THE SENDING'S BLOCK, by `Block.andThen` (`behind`,
    Johnson/Desc/K8/ReadsQuietAt.lean), AND A SEAT MAY LAY A GUARD BEHIND A BLOCK'S DECISION
    (`Guards`, Johnson/Desc/First/K8/LawSeated.lean): the laws pass to the joined and to the guarded
    block. `ClosesFrom.under`, `KeepsWaits.under`, `LeavesFront.under`: AND ALONG `Block.Under`
    (Johnson/Desc/Sound/HearsOnce.lean: a yes of c is the same yes of b): THAT IS WHAT A SEAT'S
    BLOCK HAS, whatever guards it lays and however it joins them.
  `ready_of_fold_text`: **the assembly over the frame's fold**: pre: blocks with `KeepsWaits`; c
    with `ClosesFrom tl0`; post: blocks with `LeavesFront`: wherever the fold over them goes on from
    a record at which no count waits, all nine clauses hold behind it. `seated_step_of_fold_text`:
    and the step of the block of the draw AS IT IS SEATED goes on there, where the record bears no
    mark. `ready_at_layers`, `ready_at_head`: the same at ANY c under the step joined behind a
    block own with `KeepsWaits`.
Statements and proofs.
Limits. THE LAYERS' LINKS AND THE HEAD'S LINK: ReadsQuiet.lean has no block for an attention link.
`KeepsWaits` and `LeavesFront` are shown of no block here. THAT THE LIST WHICH THE STEP CLOSES HAS
THE PLACE'S SHAPES (`tabs p`) IS A PREMISE ON THE RECORD BEHIND THE FOLD: it is a law on what the
link's own rounds returned (at a layers' link) or on the head's tables. The six facts on tl0 are
facts on public numbers: none is shown at a value; that the place's parameter is the plan's record
is the seat's. Of completeness's kind: no error term; nothing on soundness.

-/
import Johnson.Desc.First.K8.LawReadyEnds
import Johnson.Desc.First.K8.LawSeated
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.K8.ReadsQuietAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes.Model
open VerifiableInference.Desc.K8 (ReadsQuiet.layers ReadsQuiet.head ReadsQuiet.PG ReadsQuiet.PH)

/-- A fold over blocks each of which keeps a property of the record keeps it. -/
theorem foldKeeps {T Cl : Type} (P : T → Prop) (ft : Nat) :
    ∀ (bs : List (Block T Cl)) (s : T) (rs : List Fmt.RoundView) (cols : List Col)
      (out : T × List Fmt.RoundView × List Col),
      (∀ b ∈ bs, ∀ s rs gs s', b.decide s rs gs = .ok s' → P s → P s') →
      foldBlocks ft bs s rs cols = .ok out → P s → P out.1
  | [], s, rs, cols, out, _, H, hp => by
    have e : (s, rs, cols) = out := Except.ok.inj H
    rw [← e]
    exact hp
  | b :: l, s, rs, cols, out, hb, H, hp => by
    obtain ⟨s', k, hst, H'⟩ := foldConsOk H
    obtain ⟨gs, hd⟩ := stepOk hst
    exact foldKeeps P ft l s' _ _ out (fun c hc => hb c (List.mem_cons_of_mem _ hc)) H'
      (hb b List.mem_cons_self _ _ _ _ hd hp)

/-- What the step that closes the list does, as its text stands: it lays tl0, closed. -/
def ClosesFrom {Cl : Type} (tl0 : HTailF2) (c : Block S Cl) : Prop :=
  ∀ s rs gs s', c.decide s rs gs = .ok s' →
    (∃ funs, s'.tl? = some { tl0 with funClosed := true, funs := funs }) ∧
      (s.noneWaits = true → s'.noneWaits = true)

/-- **The block at a layers' link has it**, at its place's own parameter. -/
theorem layers_closesFrom (P : ReadsQuiet.PG) : ClosesFrom P.tl (ReadsQuiet.layers P) := by
  intro s rs gs s' h
  obtain ⟨a, own, tl', _, _, hc, e⟩ := VerifiableInference.Desc.K8.ReadsQuiet.layers_ok h
  obtain ⟨_, e', _, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  refine ⟨⟨own.funs, ?_⟩, fun hw => ?_⟩
  · rw [e, e']
    rfl
  · have er := (VerifiableInference.Desc.K8.ReadsQuiet.layers_frame h).1
    unfold S.noneWaits at hw ⊢
    rw [er]
    exact hw

/-- **The block at the head's link has it**, at its place's own parameter. -/
theorem head_closesFrom (P : ReadsQuiet.PH) : ClosesFrom P.hp.tl (ReadsQuiet.head P) := by
  intro s rs gs s' h
  obtain ⟨a, cov, x, t, tl', _, ho, _, _, _, hc, e⟩ :=
    VerifiableInference.Desc.K8.ReadsQuiet.head_ok h
  obtain ⟨_, e', _, _⟩ := VerifiableInference.Desc.K8.ReadsQuiet.closed_ok hc
  refine ⟨⟨t.funs, ?_⟩, fun hw => ?_⟩
  · rw [e, e']
    simp [S.tl?, ho]
  · have er := (VerifiableInference.Desc.K8.ReadsQuiet.head_frame h).1
    unfold S.noneWaits at hw ⊢
    rw [er]
    exact hw

/-- From the readings' values: the five fields are tl0's, the mark stands, no count waits. -/
theorem means_of_values (p : Par) (s : S) (tl0 : HTailF2)
    (hk : keep s = some (tl0.NM, tl0.mats, tl0.tau, tl0.cfF, tl0.foldDrawn))
    (hc : closedAt s = some true) (hw : s.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, s.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s', MeansAtS p s r s' := by
  unfold keep at hk
  unfold closedAt at hc
  cases ht : s.tl? with
  | none => rw [ht] at hc; simp at hc
  | some tl =>
    rw [ht] at hk hc
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk hc
    obtain ⟨k1, k2, k3, k4, k5⟩ := hk
    refine ⟨_, tl, ht, hc, (nothingOwed_atS s).1 hw, ⟨by rw [k4]; exact c1, by rw [k5]; exact c2⟩,
      by rw [k1]; exact d, by rw [k2]; exact e, by rw [k2]; exact e', by rw [k3]; exact f, t tl ht,
      rfl⟩

/-- Such a block lays the two readings. -/
theorem ClosesFrom.lays {Cl : Type} {tl0 : HTailF2} {c : Block S Cl} (h : ClosesFrom tl0 c) :
    c.Lays keep (fun _ => some (tl0.NM, tl0.mats, tl0.tau, tl0.cfF, tl0.foldDrawn)) ∧
      c.Lays closedAt (fun _ => some true) := by
  refine ⟨fun s rs gs s' hd => ?_, fun s rs gs s' hd => ?_⟩
  · obtain ⟨⟨funs, ht⟩, _⟩ := h s rs gs s' hd
    unfold keep
    rw [ht]
    rfl
  · obtain ⟨⟨funs, ht⟩, _⟩ := h s rs gs s' hd
    unfold closedAt
    rw [ht]
    rfl

/-- Right behind such a block. -/
theorem means_of_closesFrom {Cl : Type} (p : Par) (tl0 : HTailF2) (c : Block S Cl)
    (h : ClosesFrom tl0 c) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : c.decide s rs gs = .ok s') (hw : s.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s'', MeansAtS p s' r s'' :=
  means_of_values p s' tl0 (h.lays.1 s rs gs s' hd) (h.lays.2 s rs gs s' hd)
    ((h s rs gs s' hd).2 hw) c1 c2 d e e' f t r

/-- All that a block in front of the closing then owes. -/
def KeepsWaits {Cl : Type} (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → s.noneWaits = true → s'.noneWaits = true

/-- The step joined behind a block that keeps "no count waits". -/
theorem ClosesFrom.behind {Cl : Type} {tl0 : HTailF2} {q : Block S Cl} (h : ClosesFrom tl0 q)
    (own : Block S Cl) (ho : KeepsWaits own) (name : String) :
    ClosesFrom tl0 (Block.andThen name own q) := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ :=
    bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) H
  exact ⟨(h _ _ _ _ H).1, fun hw => (h _ _ _ _ H).2 (ho _ _ _ _ ht hw)⟩

theorem ClosesFrom.guards {Cl : Type} {tl0 : HTailF2} {c b : Block S Cl} (h : ClosesFrom tl0 b)
    (g : Guards c b) : ClosesFrom tl0 c := fun s rs gs s' hd => h s rs gs s' (g.yes hd)

theorem KeepsWaits.guards {Cl : Type} {c b : Block S Cl} (h : KeepsWaits b) (g : Guards c b) :
    KeepsWaits c := fun s rs gs s' hd => h s rs gs s' (g.yes hd)

theorem LeavesFront.guards {Cl : Type} {c b : Block S Cl} (h : LeavesFront b) (g : Guards c b) :
    LeavesFront c :=
  ⟨g.leaves h.1, g.leaves h.2.1, fun s rs gs s' hd => h.2.2 s rs gs s' (g.yes hd)⟩

/-- The three along `Block.Under` (a yes of c is the same yes of b), whatever the two blocks' types
of claims: so to a block as a seat lays it, with whatever guards. -/
theorem ClosesFrom.under {Cl Cl' : Type} {tl0 : HTailF2} {c : Block S Cl'} {b : Block S Cl}
    (h : ClosesFrom tl0 b) (u : c.Under b) : ClosesFrom tl0 c :=
  fun s rs gs s' hd => h s rs gs s' (u s rs gs s' hd)

theorem KeepsWaits.under {Cl Cl' : Type} {c : Block S Cl'} {b : Block S Cl} (h : KeepsWaits b)
    (u : c.Under b) : KeepsWaits c := fun s rs gs s' hd => h s rs gs s' (u s rs gs s' hd)

theorem LeavesFront.under {Cl Cl' : Type} {c : Block S Cl'} {b : Block S Cl} (h : LeavesFront b)
    (u : c.Under b) : LeavesFront c :=
  ⟨leaves_of_under u h.1, leaves_of_under u h.2.1,
    fun s rs gs s' hd => h.2.2 s rs gs s' (u s rs gs s' hd)⟩

/-- **The assembly over the frame's fold, at the text as it stands.** -/
theorem ready_of_fold_text {Cl : Type} (p : Par) (tl0 : HTailF2) (pre : List (Block S Cl))
    (c : Block S Cl) (post : List (Block S Cl)) (hpre : ∀ b ∈ pre, KeepsWaits b)
    (hc : ClosesFrom tl0 c) (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out) (hw : s0.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p) (r : Fmt.RoundView) :
    ∃ s', MeansAtS p out.1 r s' := by
  have hk := foldLays S Cl _ keep _ ft pre c post s0 rs cols out hc.lays.1
    (fun b h => (hp b h).1) H
  have hcl := foldLays S Cl _ closedAt _ ft pre c post s0 rs cols out hc.lays.2
    (fun b h => (hp b h).2.1) H
  have hn := foldKeeps (fun s : S => s.noneWaits = true) ft (pre ++ c :: post) s0 rs cols out
    (fun b hb => by
      rcases List.mem_append.1 hb with h | h
      · exact hpre b h
      · rcases List.mem_cons.1 h with h | h
        · rw [h]
          exact fun s rs gs s' hd => (hc s rs gs s' hd).2
        · exact (hp b h).2.2) H hw
  exact means_of_values p out.1 tl0 hk hcl hn c1 c2 d e e' f t r

/-- And the step of the block of the draw AS IT IS SEATED (any cd with `Seats`) goes on behind the
fold, on every round that passes the frame's test, where the record behind the fold bears no
mark. -/
theorem seated_step_of_fold_text {Cl : Type} (p : Par) (tl0 : HTailF2) (pre : List (Block S Cl))
    (c : Block S Cl) (post : List (Block S Cl)) (hpre : ∀ b ∈ pre, KeepsWaits b)
    (hc : ClosesFrom tl0 c) (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out) (hw : s0.noneWaits = true)
    (c1 : tl0.cfF.size = 0) (c2 : tl0.foldDrawn = 0) (d : tl0.NM = p.ks.length)
    (e : tl0.mats.toList.map (·.k) = p.ks) (e' : tl0.mats.toList.map (·.m) = p.ms)
    (f : tl0.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p)
    (cd : Block S Cl) (g : Seats cd (approximateRangeProofDrawKind atS p)) (hm : out.1.failed = none)
    (ft' : Nat) (r : Fmt.RoundView) (cols' : List Col) (hf : roundsFit [round p] [r] = true) :
    ∃ s', cd.step ft' out.1 [r] cols' = .ok (s', 0) := by
  obtain ⟨s', h⟩ := ready_of_fold_text p tl0 pre c post hpre hc hp ft s0 rs cols out H hw c1 c2 d
    e e' f t r
  exact ⟨s', (step_seats_iff p cd g ft' out.1 s' 0 [r] cols').2 ⟨r, rfl, hf, h, rfl, hm⟩⟩

/-- The same at a layers' link: c is under the step joined behind the sending's block own. -/
theorem ready_at_layers {Cl : Type} (p : Par) (P : ReadsQuiet.PG) (own : Block S Unit)
    (c : Block S Cl) (ho : KeepsWaits own)
    (g : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.layers P)))
    (pre post : List (Block S Cl))
    (hpre : ∀ b ∈ pre, KeepsWaits b) (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out)
    (hw : s0.noneWaits = true) (c1 : P.tl.cfF.size = 0) (c2 : P.tl.foldDrawn = 0)
    (d : P.tl.NM = p.ks.length) (e : P.tl.mats.toList.map (·.k) = p.ks)
    (e' : P.tl.mats.toList.map (·.m) = p.ms) (f : P.tl.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p)
    (r : Fmt.RoundView) : ∃ s', MeansAtS p out.1 r s' :=
  ready_of_fold_text p P.tl pre c post hpre
    (((layers_closesFrom P).behind own ho own.name).under g) hp ft s0 rs cols out H hw c1 c2 d e
    e' f t r

/-- The same at the head's link. -/
theorem ready_at_head {Cl : Type} (p : Par) (P : ReadsQuiet.PH) (own : Block S Unit)
    (c : Block S Cl) (ho : KeepsWaits own)
    (g : c.Under (VerifiableInference.Desc.K8.ReadsQuiet.behind own (ReadsQuiet.head P)))
    (pre post : List (Block S Cl))
    (hpre : ∀ b ∈ pre, KeepsWaits b) (hp : ∀ b ∈ post, LeavesFront b) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out)
    (hw : s0.noneWaits = true) (c1 : P.hp.tl.cfF.size = 0) (c2 : P.hp.tl.foldDrawn = 0)
    (d : P.hp.tl.NM = p.ks.length) (e : P.hp.tl.mats.toList.map (·.k) = p.ks)
    (e' : P.hp.tl.mats.toList.map (·.m) = p.ms) (f : P.hp.tl.tau = p.tau)
    (t : ∀ tl, out.1.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p)
    (r : Fmt.RoundView) : ∃ s', MeansAtS p out.1 r s' :=
  ready_of_fold_text p P.hp.tl pre c post hpre
    (((head_closesFrom P).behind own ho own.name).under g) hp ft s0 rs cols out H hw c1 c2 d e e'
    f t r

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.foldKeeps
#print axioms VerifiableInference.Desc.First.K8.Ready.layers_closesFrom
#print axioms VerifiableInference.Desc.First.K8.Ready.head_closesFrom
#print axioms VerifiableInference.Desc.First.K8.Ready.means_of_closesFrom
#print axioms VerifiableInference.Desc.First.K8.Ready.ready_of_fold_text
#print axioms VerifiableInference.Desc.First.K8.Ready.seated_step_of_fold_text
#print axioms VerifiableInference.Desc.First.K8.Ready.ready_at_layers
#print axioms VerifiableInference.Desc.First.K8.Ready.ready_at_head
