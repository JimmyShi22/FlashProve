-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldHeardProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/FoldHeard.lean, each under its statement's name with a small first letter.

How. Readings of Block.lean's texts where they go on (`bindOk`, `mapOk`, `stepOk`, `foldConsOk`,
`chainAtOk`);
then inductions on the list of blocks. At the end: `FileDescription.Hears.pull`, `mapTok`: the record at
another type of instances; of tokens.

Beside: Johnson/Desc/Sound/FoldLaw.lean (of the rule of composition's files) reads the same texts as
equations (`Block.step_eq`, `foldBlocks_ok`, `chainAt_toOption`); the readings here are one-way, and
import Block.lean alone.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-! ## 1 Block.lean's texts, where they go on -/

/-- Where two steps in a row go on, the first went on, and the second at its value. -/
theorem bindOk {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- The like for `map`. -/
theorem mapOk {ε α β : Type} {x : Except ε α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-- What a list of pairs gives under a name stands in the list under that name. -/
theorem memOfLookup {β : Type} : ∀ (l : List (String × β)) (a : String) (b : β),
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => nomatch h
  | (k, v) :: l, a, b, h => by
    rw [List.lookup_cons] at h
    split at h
    next hk =>
      have e₁ : a = k := eq_of_beq hk
      have e₂ : v = b := Option.some.inj h
      rw [e₁, ← e₂]
      exact List.mem_cons_self
    next => exact List.mem_cons_of_mem _ (memOfLookup l a b h)

section
variable {S Cl α : Type}

/-- Where a block's step goes on, its decision went on, at the step's rounds without their sealed
digests, and gave the step's record. -/
theorem stepOk {ft : Nat} {b : Block S Cl} {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {s' : S}
    {k : Nat} (H : b.step ft s rs cols = .ok (s', k)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨_, _, H⟩ := bindOk H
  obtain ⟨t, ht, H⟩ := bindOk H
  have e : t = s' := congrArg Prod.fst (Except.ok.inj H)
  exact ⟨_, e ▸ ht⟩

/-- Where the fold over a list with a first block goes on: that block's step went on at the first
rounds, as many as it declares, and the fold over the other blocks goes on from there. -/
theorem foldConsOk {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (H : foldBlocks ft (b :: l) s rs cols = .ok out) :
    ∃ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok out := by
  simp only [foldBlocks, List.splitAt_eq] at H
  split at H
  next => exact nomatch H
  next =>
    split at H
    next => exact nomatch H
    next s' k hst => exact ⟨s', k, hst, H⟩

/-- Where a chain's fold goes on, the fold over its blocks ended there with nothing left over. -/
theorem chainAtOk {name : String} {ft : Nat} {bs : List (Block S Cl)} {s e : S} {v : Fmt.View}
    (H : chainAt name ft bs s v = .ok e) :
    foldBlocks ft bs s v.rounds v.opened = .ok (e, [], []) := by
  unfold chainAt at H
  split at H
  next => exact nomatch H
  next =>
    split at H
    next s' heq => exact (Except.ok.inj H) ▸ heq
    next => exact nomatch H
    next => exact nomatch H

end

/-! ## 2 The fold's laws -/

theorem foldLeaves : FoldLeaves := by
  intro S Cl α h ft bs
  induction bs with
  | nil =>
    intro s rs cols out _ H
    have e : (s, rs, cols) = out := Except.ok.inj H
    rw [← e]
  | cons b l ih =>
    intro s rs cols out hb H
    obtain ⟨s', k, hst, H'⟩ := foldConsOk H
    obtain ⟨gs, hd⟩ := stepOk hst
    rw [ih s' _ _ out (fun c hc => hb c (List.mem_cons_of_mem _ hc)) H']
    exact hb b List.mem_cons_self _ _ _ _ hd

theorem foldLays : FoldLays := by
  intro S Cl α h rd ft pre b post
  induction pre with
  | nil =>
    intro s rs cols out hl hp H
    obtain ⟨s', k, hst, H'⟩ := foldConsOk (l := post) H
    obtain ⟨gs, hd⟩ := stepOk hst
    rw [foldLeaves S Cl α h ft post s' _ _ out hp H', hl _ _ _ _ hd]
    simp [shownAt]
  | cons p l ih =>
    intro s rs cols out hl hp H
    obtain ⟨s', k, _, H'⟩ := foldConsOk (l := l ++ b :: post) H
    rw [ih s' _ _ out hl hp H']
    simp [shownAt, List.drop_drop]

theorem chainLays : ChainLays := by
  intro S Cl α h rd name ft pre b post s e v hl hp H
  exact foldLays S Cl α h rd ft pre b post s v.rounds v.opened (e, [], []) hl hp (chainAtOk H)

/-! ## 3 `Leaves` of blocks that Block.lean's makers make -/

theorem leavesLift : LeavesLift := by
  intro S T Cl α h get set b hs t rs gs t' H
  obtain ⟨s, _, e⟩ := mapOk (x := b.decide (get t) rs gs) H
  rw [← e, hs]

theorem leavesLiftPart : LeavesLiftPart := by
  intro S T Cl α h get? set b hs t rs gs t' H
  obtain ⟨p, _, H⟩ := bindOk (x := named "the part is not there" (get? t)) H
  obtain ⟨s, _, e⟩ := mapOk H
  rw [← e, hs]

theorem leavesLiftIn : LeavesLiftIn := by
  intro S T Cl α h get set b hg hb t rs gs t' H
  obtain ⟨s, hs, e⟩ := mapOk (x := b.decide (get t) rs gs) H
  rw [← e]
  show h (get (set t s)) = _
  rw [hg]
  exact hb _ _ _ _ hs

theorem laysLiftIn : LaysLiftIn := by
  intro S T Cl α h rd get set b hg hb t rs gs t' H
  obtain ⟨s, hs, e⟩ := mapOk (x := b.decide (get t) rs gs) H
  rw [← e]
  show h (get (set t s)) = _
  rw [hg]
  exact hb _ _ _ _ hs

theorem leavesAndThen : LeavesAndThen := by
  intro S Cl α h name p q hp hq s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  rw [hq _ _ _ _ H, hp _ _ _ _ ht]

theorem leavesInside : LeavesInside := by
  intro S T Cl α h enter b leave hl s rs gs s' H
  obtain ⟨t, _, H⟩ := bindOk (x := enter s) H
  obtain ⟨t', _, H⟩ := bindOk H
  exact hl _ _ _ H

theorem leavesQuiet : LeavesQuiet := by
  intro S Cl α h name chain link piece f hf s rs gs s' H
  exact hf _ _ H

theorem leavesAfterIn : LeavesAfterIn := by
  intro S Cl α h bs order hb s
  suffices G : ∀ (o : List (Nat × String)) (acc : Except String S),
      (∀ x, acc = .ok x → h x = h s) → ∀ s',
      o.foldl (fun acc o => acc.bind fun x =>
        (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind
          fun run =>
          match run x with
          | .ok y => .ok y
          | .error e => .error (o.2 ++ ": " ++ e)) acc = .ok s' → h s' = h s from
    fun s' H => G order (.ok s) (fun x e => (Except.ok.inj e) ▸ rfl) s' H
  intro o
  induction o with
  | nil => intro acc ha s' H; exact ha s' H
  | cons o l ih =>
    intro acc ha s' H
    refine ih _ ?_ s' H
    intro y hy
    obtain ⟨x, hx, hy⟩ := bindOk hy
    obtain ⟨run, hrun, hy⟩ := bindOk hy
    have hmem : ∃ b ∈ bs, (o.2, run) ∈ b.after := by
      cases hb' : bs[o.1]? with
      | none => rw [hb'] at hrun; exact nomatch hrun
      | some b =>
        rw [hb'] at hrun
        cases hl : b.after.lookup o.2 with
        | none =>
          have : named (o.2 ++ ": no such run") (b.after.lookup o.2) = .ok run := hrun
          rw [hl] at this; exact nomatch this
        | some r =>
          have : named (o.2 ++ ": no such run") (b.after.lookup o.2) = .ok run := hrun
          rw [hl] at this
          have e : r = run := Except.ok.inj this
          exact ⟨b, List.mem_of_getElem? hb', e ▸ memOfLookup _ _ _ hl⟩
    obtain ⟨b, hbm, hc⟩ := hmem
    cases hr : run x with
    | error e => rw [hr] at hy; exact nomatch hy
    | ok z =>
      rw [hr] at hy
      have e : z = y := Except.ok.inj hy
      rw [← e, hb b hbm _ hc x z hr]
      exact ha x hx

theorem leavesLink : LeavesLink := by
  intro S Cl α h L hlay hhear hbatch hafter hclose hclear b hb
  unfold Link.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.cons_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · exact fun s rs gs s' H => hlay _ _ H
  · exact hhear b hb
  · exact hbatch
  · intro s rs gs s' H
    have H' : L.runBehind s = .ok s' := H
    unfold Link.runBehind at H'
    split at H'
    · exact leavesAfterIn S Cl α h L.hear L.orderAfter hafter _ _ H'
    · exact nomatch H'
  · exact hclose b hb
  · exact fun s rs gs s' H => hclear _ _ H

theorem leavesChain : LeavesChain := by
  intro S Cl α h c h₁ hf hl hk h₂ b hb
  unfold Chain.blocksInOrder at hb
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | ((⟨p, hp, rfl⟩ | ⟨L, hL, hb⟩) | ⟨p, hp, rfl⟩) | rfl
  · exact fun s rs gs s' H => h₁ s rs gs s' H
  · exact fun s rs gs s' H => hf p hp s rs gs s' H
  · exact hl L hL b hb
  · exact fun s rs gs s' H => hk p hp s rs gs s' H
  · exact fun s rs gs s' H => h₂ s rs gs s' H

/-! ## 4 A description that hears the reply -/

theorem saidOfEnds : SaidOfEnds := by
  intro Xi F Tok asked rd H x s v₁ e₁ e₂ e₃ hc hf
  rw [H.cut] at hc
  have := chainLays F.S₁ F.Cl (Option Tok) H.heard rd _ 0 H.pre H.blk H.post s e₁ (withEmptySealRound v₁)
    H.lays H.leaves hc
  unfold FileDescription.Hears.said
  rw [← this]
  exact H.fins x e₁ e₂ e₃ hf

/-- A description that hears the reply, laid at another type of instances (`FileDescription.pull`): the
same reading, cut and laws; what is asked is read along the map. -/
def FileDescription.Hears.pull {Xi Xi' : Type} {F : FileDescription Xi} {Tok : Type} {asked : Xi → Tok}
    {rd : List Fmt.RoundView → Option Tok} (f : Xi' → Xi) (H : F.Hears asked rd) :
    (F.pull f).Hears (fun x => asked (f x)) rd where
  heard := H.heard
  pre := H.pre
  blk := H.blk
  post := H.post
  cut := H.cut
  lays := H.lays
  leaves := H.leaves
  fins := fun x e₁ e₂ e₃ h => H.fins (f x) e₁ e₂ e₃ h

/-- The record at another type of tokens, along a reading g of a token: what was heard and what the
rounds name are read by THE SAME g; hg: what is asked reads as asked'. So where the last test
compares what was heard and what is asked as they are written, nothing is asked of how else a token
could be written. -/
def FileDescription.Hears.mapTok {Xi : Type} {F : FileDescription Xi} {Tok Tok' : Type} {asked : Xi → Tok}
    {rd : List Fmt.RoundView → Option Tok} (g : Tok → Option Tok') (asked' : Xi → Tok')
    (hg : ∀ x, g (asked x) = some (asked' x)) (H : F.Hears asked rd) :
    F.Hears asked' fun rs => (rd rs).bind g where
  heard := fun s => (H.heard s).bind g
  pre := H.pre
  blk := H.blk
  post := H.post
  cut := H.cut
  lays := fun s rs gs s' h => congrArg (·.bind g) (H.lays s rs gs s' h)
  leaves := fun c hc s rs gs s' h => congrArg (·.bind g) (H.leaves c hc s rs gs s' h)
  fins := fun x e₁ e₂ e₃ h => (congrArg (·.bind g) (H.fins x e₁ e₂ e₃ h)).trans (hg x)

/-- It names the same token. -/
theorem FileDescription.Hears.pull_said {Xi Xi' : Type} {F : FileDescription Xi} {Tok : Type} {asked : Xi → Tok}
    {rd : List Fmt.RoundView → Option Tok} (f : Xi' → Xi) (H : F.Hears asked rd) (v : Fmt.View) :
    (H.pull f).said v = H.said v := rfl

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.foldLeaves
#print axioms VerifiableInference.Desc.foldLays
#print axioms VerifiableInference.Desc.chainLays
#print axioms VerifiableInference.Desc.leavesLift
#print axioms VerifiableInference.Desc.leavesLiftPart
#print axioms VerifiableInference.Desc.leavesLiftIn
#print axioms VerifiableInference.Desc.laysLiftIn
#print axioms VerifiableInference.Desc.leavesAndThen
#print axioms VerifiableInference.Desc.leavesInside
#print axioms VerifiableInference.Desc.leavesQuiet
#print axioms VerifiableInference.Desc.leavesAfterIn
#print axioms VerifiableInference.Desc.leavesLink
#print axioms VerifiableInference.Desc.leavesChain
#print axioms VerifiableInference.Desc.saidOfEnds
