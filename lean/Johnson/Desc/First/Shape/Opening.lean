-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Opening.lean: THE FIRST SEGMENT's OPENING (the kind K1, at link 0's first
place) AS A MEMBER OF THE FIRST CHAIN, ON THE CHAIN's SHAPE: one step, and its two laws at the
block's own decision (K1.firstSegmentOpening, Johnson/Desc/K1/First.lean). General laws; nothing is evaluated.

  `othersOf`, `firstStepG`, **`firstOwn_carries`**: K1.firstOwn: the walk's and the frame's tests,
    the new group (Ground.Sh.newGroupS), the sending (sendCore, SendCore.lean), the joinings
    (joinAllS, Joining.lean), the new state of the calls: behind a yes the step returns the shapes
    behind.
  `bind_ex`, `firstG`, **`firstOwn_returns`**: the sending's Bool at the core with the new group,
    then the step: where it returns, K1.firstOwn, at the count of rows owed as K1.owedOf reads it
    (0 rows owed is none), returns on two rounds in which no seed's factor is 0 and round 2 holds
    as many answers as the place counts.
  `between_iff`, `openLaid`, **`openG`**, `openStepG`, **`open_carries_strong`**,
    **`open_carries`**, **`open_returns`**: the same at the member: it stands between two links,
    reads and writes the walk's own state of the calls, the core and the debt of rows.

Limits. The bare block: in a description the quiet step that enters link 0 is laid behind it by
Block.andThen; that step, the guard on the mark and the comparison of the reply are not in it. The
two premises on the rounds stand as in SendCore.lean. The converse of open_returns fails by the
sending's tests on the plan alone. No state is shown at which openG returns. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Shape.Commit
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState GPar groundG)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)

/-- What the first prover's message holds, off the frame's shape. -/
def othersOf (f : FrameSh) : Array OracleNotice :=
  ReqFrame.notices (f.blank.atMoment 0) ++ #[foldMaskNotice (f.blank.foldShape f.link {})] ++
    f.shape.atStart.toArray

/-- K1.firstOwn behind its sending's guards, on shapes. -/
def firstStepG (P : K1.Par) (c : CheckSh) (a : CoreSh) : Option (CheckSh × CoreSh) :=
  if !c.inLink && decide (c.link < c.links) && (c.frame.next == .first) && (c.frame.link == 0) &&
      (othersOf c.frame == P.sent) && (c.frame.groups[c.frame.link]?).isSome &&
      ((c.frame.shape.link[c.frame.link]?).any fun L => L.plain == 0) then
    (Ground.Sh.newGroupS a c.frame.shape.code c.frame.shape.maskCode).bind fun x =>
      let ids := idsAt P x.2.st.oracles.length
      let n := (c.frame.blank.atMoment 0).length
      if ids.size == (othersOf c.frame).size && n == (ids.extract 0 n).size then
        (ids[n]?).bind fun mask =>
          (joinAllS x.1 (zipT (c.frame.blank.atMoment 0) (ids.extract 0 n).toList)
            (sendCore P x.2)).map fun h' =>
            ({ c with
                frame := { c.frame with
                  group := x.1, moment := 1, own := #[] ++ ids.extract 0 n, plain := 0
                  mask := some mask, atStart := c.frame.atStart ++ ids.extract (n + 1) ids.size
                  next := .laterOrClose }
                sent := ids.extract 0 n, inLink := true, moments := 1 }, h')
      else none
  else none

/-- **"Carries" at the opening's own decision**: behind a yes the step returns the shapes behind. -/
theorem firstOwn_carries (P : K1.Par) (owed : Option Nat) (c : ChainCheck) (d : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : K1.firstOwn P owed c d rs = .ok y) :
    firstStepG P (checkSh c) (coreSh (coreOf d)) = some (checkSh y.1, coreSh (coreOf y.2)) := by
  unfold K1.firstOwn at h
  dsimp only at h
  obtain ⟨_, a1, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, a2, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, a3, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨Lk, a4, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨Gk, a5, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨_, a6, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, a7, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (K1.bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, a8, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨mask, a9, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  have a1 := (K1.need_ok _ _ _).1 a1
  have a2 := (K1.need_ok _ _ _).1 a2
  have a3 := (K1.need_ok _ _ _).1 a3
  have a4 := (K1.named_ok _ _ _).1 a4
  have a5 := (K1.named_ok _ _ _).1 a5
  have a6 := (K1.need_ok _ _ _).1 a6
  have h1 := (K1.named_ok _ _ _).1 h1
  have a7 := (K1.need_ok _ _ _).1 a7
  have a8 := (K1.need_ok _ _ _).1 a8
  have a9 := (K1.named_ok _ _ _).1 a9
  have h3 := (K1.named_ok _ _ _).1 h3
  obtain ⟨hi, hcore, -, -⟩ := send_core h2
  have hi' : ids = idsAt P d₁.st.oracles.size := hi
  subst hi'
  have hN := Ground.Sh.newGroup_carries d d₁ _ _ g h1
  unfold Send.joinOwnP at h3
  split at h3
  · rename_i hlen
    obtain ⟨d', hd, he⟩ := Option.map_eq_some_iff.1 h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hJ := joinAll_core P.gp g (zipT (c.frame.atMoment 0)
      ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length).toList) d₂
    rw [hd] at hJ
    unfold firstStepG
    have hcond : (!(checkSh c).inLink && decide ((checkSh c).link < (checkSh c).links) &&
        ((checkSh c).frame.next == .first) && ((checkSh c).frame.link == 0) &&
        (othersOf (checkSh c).frame == P.sent) &&
        ((checkSh c).frame.groups[(checkSh c).frame.link]?).isSome &&
        (((checkSh c).frame.shape.link[(checkSh c).frame.link]?).any fun L => L.plain == 0)) =
        true := by
      have b5 : (c.frame.groups[c.frame.link]?).isSome = true := by rw [a5]; rfl
      have b4 : ((c.frame.shape.link[c.frame.link]?).any fun L => L.plain == 0) = true := by
        rw [a4]; exact a7
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨by simpa [Bool.and_eq_true] using a1, a2⟩, a3⟩, a6⟩, b5⟩, b4⟩
    rw [if_pos hcond]
    show (Ground.Sh.newGroupS (coreSh (coreOf d)) c.frame.shape.code c.frame.shape.maskCode).bind
      _ = _
    rw [hN]
    have hz : (coreSh (coreOf d₁)).st.oracles.length = d₁.st.oracles.size :=
      Ground.Sh.orc_size d₁.st
    simp only [Option.bind_some, hz]
    have hc2 : ((idsAt P d₁.st.oracles.size).size == (othersOf (checkSh c).frame).size &&
        ((checkSh c).frame.blank.atMoment 0).length ==
          ((idsAt P d₁.st.oracles.size).extract 0
            ((checkSh c).frame.blank.atMoment 0).length).size) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨a8, hlen⟩
    rw [if_pos hc2]
    have a9' : (idsAt P d₁.st.oracles.size)[((checkSh c).frame.blank.atMoment 0).length]? =
        some mask := a9
    rw [a9']
    simp only [Option.bind_some]
    rw [← hcore]
    show Option.map _ (joinAllS g (zipT (c.frame.atMoment 0)
      ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length).toList)
      (coreSh (coreOf d₂))) = _
    rw [← hJ]
    rfl
  · cases h3

/-- A bind returns where its first half returns and its second returns behind that. -/
theorem bind_ex {α β : Type} (x : Except String α) (f : α → Except String β) (a : α)
    (h1 : x = .ok a) (h2 : ∃ b, f a = .ok b) : ∃ b, (x >>= f) = .ok b := by
  obtain ⟨b, hb⟩ := h2
  exact ⟨b, (K1.bind_ok _ _ _).2 ⟨a, h1, hb⟩⟩

/-- **The opening's own decision on shapes**: the sending's Bool at the core with the new group,
then the step. -/
def firstG (P : K1.Par) (owed : Option Nat) (c : CheckSh) (a : CoreSh) :
    Option (CheckSh × CoreSh) :=
  (Ground.Sh.newGroupS a c.frame.shape.code c.frame.shape.maskCode).bind fun x =>
    if sendB P owed x.2 then firstStepG P c a else none

/-- **"Returns" at the opening's own decision**, at the count as K1.owedOf reads it (0 rows owed is
none). -/
theorem firstOwn_returns (P : K1.Par) (owed : Option Nat) (c : ChainCheck) (d : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (y : CheckSh × CoreSh)
    (hg : firstG P owed (checkSh c) (coreSh (coreOf d)) = some y)
    (hz : ∀ x ∈ K1.seedsOf P r₁, isZeroE x.2 = false)
    (hn : (K1.answersIn r₂).length = P.answers) :
    ∃ out, K1.firstOwn P (owed.filter (· != 0)) c d [r₁, r₂] = .ok out := by
  unfold firstG at hg
  obtain ⟨x, hx, hg⟩ := Option.bind_eq_some_iff.1 hg
  obtain ⟨⟨g, d₁⟩, h1⟩ := Ground.Sh.newGroup_returns d _ _ x hx
  have hN : Ground.Sh.newGroupS (coreSh (coreOf d)) c.frame.shape.code c.frame.shape.maskCode =
      some (g, coreSh (coreOf d₁)) := Ground.Sh.newGroup_carries d d₁ _ _ g h1
  have hx' : Ground.Sh.newGroupS (coreSh (coreOf d)) c.frame.shape.code c.frame.shape.maskCode =
      some x := hx
  rw [hN] at hx'
  obtain rfl := Option.some.inj hx'
  split at hg
  · rename_i hB
    obtain ⟨⟨ids, d₂⟩, h2⟩ := send_returns P owed d₁ r₁ r₂ hB hz hn
    obtain ⟨hi, hcore, -, -⟩ := send_core h2
    have hi' : ids = idsAt P d₁.st.oracles.size := hi
    subst hi'
    have hzz : (coreSh (coreOf d₁)).st.oracles.length = d₁.st.oracles.size :=
      Ground.Sh.orc_size d₁.st
    unfold firstStepG at hg
    split at hg
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨⟨⟨⟨⟨b1, b1'⟩, b2⟩, b3⟩, b6⟩, b5⟩, b4⟩ := hcond
      have hg' := hg
      rw [show Ground.Sh.newGroupS (coreSh (coreOf d)) (checkSh c).frame.shape.code
        (checkSh c).frame.shape.maskCode = some (g, coreSh (coreOf d₁)) from hN] at hg'
      simp only [Option.bind_some, hzz] at hg'
      split at hg'
      · rename_i hc2
        simp only [Bool.and_eq_true] at hc2
        obtain ⟨mask, hm, hg'⟩ := Option.bind_eq_some_iff.1 hg'
        obtain ⟨h', hj, -⟩ := Option.map_eq_some_iff.1 hg'
        rw [← hcore] at hj
        have hJ := joinAll_core P.gp g (zipT (c.frame.atMoment 0)
          ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length).toList) d₂
        have hj' : joinAllS g (zipT (c.frame.atMoment 0)
            ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length).toList)
            (coreSh (coreOf d₂)) = some h' := hj
        rw [hj'] at hJ
        obtain ⟨d₃, hd3, -⟩ := Option.map_eq_some_iff.1 hJ
        obtain ⟨Lk, hLk, hpl⟩ : ∃ Lk, c.frame.shape.link[c.frame.link]? = some Lk ∧
            (Lk.plain == 0) = true := by
          have b4' : ((c.frame.shape.link[c.frame.link]?).any fun L => L.plain == 0) = true := b4
          cases hL : c.frame.shape.link[c.frame.link]? with
          | none => rw [hL] at b4'; cases b4'
          | some Lk => rw [hL] at b4'; exact ⟨Lk, rfl, b4'⟩
        obtain ⟨Gk, hGk⟩ := Option.isSome_iff_exists.1
          (show (c.frame.groups[c.frame.link]?).isSome = true from b5)
        unfold K1.firstOwn
        dsimp only
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2
          (by simp only [Bool.and_eq_true]; exact ⟨b1, b1'⟩)) ?_
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2 b2) ?_
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2 b3) ?_
        refine bind_ex _ _ Lk ((K1.named_ok _ _ _).2 hLk) ?_
        refine bind_ex _ _ Gk ((K1.named_ok _ _ _).2 hGk) ?_
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2 b6) ?_
        refine bind_ex _ _ (g, d₁) ((K1.named_ok _ _ _).2 h1) ?_
        dsimp only
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2 hpl) ?_
        refine bind_ex _ _ (_, d₂) h2 ?_
        dsimp only
        refine bind_ex _ _ () ((K1.need_ok _ _ _).2 hc2.1) ?_
        refine bind_ex _ _ mask ((K1.named_ok _ _ _).2 hm) ?_
        have hjo : ∃ z, Send.joinOwnP groundG P.gp d₂
            { c.frame with
              group := g, moment := 1, own := #[], plain := [], keptBefore := c.frame.keptBefore
              mask := some mask
              atStart := c.frame.atStart ++ (idsAt P d₁.st.oracles.size).extract
                ((c.frame.atMoment 0).length + 1) (idsAt P d₁.st.oracles.size).size }
            (c.frame.atMoment 0)
            ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length) = some z := by
          have hl : ((c.frame.atMoment 0).length ==
              ((idsAt P d₁.st.oracles.size).extract 0 (c.frame.atMoment 0).length).size) = true :=
            hc2.2
          unfold Send.joinOwnP
          rw [if_pos hl, hd3]
          exact ⟨_, rfl⟩
        obtain ⟨z, hz'⟩ := hjo
        exact bind_ex _ _ z ((K1.named_ok _ _ _).2 hz') ⟨_, rfl⟩
      · cases hg'
    · cases hg
  · cases hg

/-! ## The member: the first segment's opening at the first chain's state -/

theorem between_iff (s : S) : s.atBetween = ((chainSh s).here == 0) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> (try (rename_i a; cases hO : a.opened)) <;>
    simp [S.atBetween, chainSh, ChainSh.mk, ChainSh.here, hereNo, *]

/-- What the opening's yes lays. -/
def openLaid (a : ChainSh) (y : CheckSh × CoreSh) : ChainSh :=
  ((a.setCore y.2).setRowsOwed none).setCheck y.1

/-- **The first segment's opening on the chain's shape.** -/
def openG (P : K1.Par) (a : ChainSh) : Option ChainSh :=
  if a.here == 0 then (firstG P a.rowsOwed a.check a.core).map (openLaid a) else none

/-- The same behind the sending's Bool. -/
def openStepG (P : K1.Par) (a : ChainSh) : Option ChainSh :=
  if a.here == 0 then (firstStepG P a.check a.core).map (openLaid a) else none

/-- **"Carries" at the member, in the strong form but for the sending's tests on the plan.** -/
theorem open_carries_strong (q : Params.First) (gp : GPar) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Unit) q gp).decide s rs gs = .ok s') :
    openStepG (K1.firstPar q gp) (chainSh s) = some (chainSh s') := by
  unfold K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, a1, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, h1, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  have a1 := (K1.need_ok _ _ _).1 a1
  rw [between_iff] at a1
  unfold openStepG
  rw [if_pos a1]
  have := firstOwn_carries _ _ _ _ _ _ h1
  rw [show firstStepG (K1.firstPar q gp) (chainSh s).check (chainSh s).core =
    some (checkSh c, coreSh (coreOf d)) from this]
  rfl

/-- **"Carries" at the member.** -/
theorem open_carries (q : Params.First) (gp : GPar) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (h : (K1.firstSegmentOpening (Cl := Unit) q gp).decide s rs gs = .ok s')
    (hg : openG (K1.firstPar q gp) (chainSh s) = some t) : t = chainSh s' := by
  have hs := open_carries_strong q gp h
  unfold openG at hg
  unfold openStepG at hs
  split at hg
  · rename_i h0
    rw [if_pos h0] at hs
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hg
    unfold firstG at hy
    obtain ⟨x, -, hy⟩ := Option.bind_eq_some_iff.1 hy
    split at hy
    · rw [hy] at hs
      exact Option.some.inj hs
    · cases hy
  · cases hg

/-- **"Returns" at the member.** -/
theorem open_returns (q : Params.First) (gp : GPar) {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {t : ChainSh}
    (hg : openG (K1.firstPar q gp) (chainSh s) = some t)
    (hz : ∀ x ∈ K1.seedsOf (K1.firstPar q gp) r₁, isZeroE x.2 = false)
    (hn : (K1.answersIn r₂).length = (K1.firstPar q gp).answers) :
    ∃ s', (K1.firstSegmentOpening (Cl := Unit) q gp).decide s [r₁, r₂] gs = .ok s' ∧ chainSh s' = t := by
  have hg0 := hg
  unfold openG at hg
  split at hg
  · rename_i h0
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hg
    obtain ⟨out, ho⟩ := firstOwn_returns (K1.firstPar q gp) s.rowsOwed s.check (K1.stateOf s ())
      r₁ r₂ y hy hz hn
    have hd : (K1.firstSegmentOpening (Cl := Unit) q gp).decide s [r₁, r₂] gs =
        .ok { K1.laid s out.2 with check := out.1 } := by
      unfold K1.firstSegmentOpening
      dsimp only
      refine (K1.bind_ok _ _ _).2 ⟨(), (K1.need_ok _ _ _).2 (by rw [between_iff]; exact h0), ?_⟩
      exact (K1.bind_ok _ _ _).2 ⟨out, ho, rfl⟩
    exact ⟨_, hd, (open_carries q gp hd hg0).symm⟩
  · cases hg

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.bind_ex
#print axioms VerifiableInference.Desc.First.Shape.firstOwn_carries
#print axioms VerifiableInference.Desc.First.Shape.firstOwn_returns
#print axioms VerifiableInference.Desc.First.Shape.between_iff
#print axioms VerifiableInference.Desc.First.Shape.open_carries_strong
#print axioms VerifiableInference.Desc.First.Shape.open_carries
#print axioms VerifiableInference.Desc.First.Shape.open_returns
