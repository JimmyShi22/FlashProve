-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/ChainF.lean: THE FIRST CHAIN's SHAPE WITH THE MAKES OF ITS STATEMENT's
ROWS BESIDE IT, AND K1's THREE BLOCKS ON THE MAKES. General laws; nothing is evaluated.

What it is for. A closing's and a switch's guards read the makes of the statement's rows
(Rows.lean, FoldMake.lean, Forms.lean), which Chain.lean's shape does not hold. They go BESIDE that
shape, as a second factor, so that no statement on chainSh turns: a member that leaves the
statement owes nothing new (quiet_carries); a member that turns it owes one small law more: formsOf
t.st as a function of chainSh s and formsOf s.st (pair_carries).

  1 `ChainF` := ChainSh × FormsSh, `chainF`, `quietF`, `pairF`, **`pair_carries`**,
    `quiet_carries`.
  2 `putLink_st`, `putFork_st`.
  3 `joinAll_forms`, `laterOwn_forms`, **`commit_forms`**: behind a yes of K1.commitAtS on two
    rounds: formsOf t.st = sendForms P ‹the number of messages in front, off the shape› (formsOf
    s.st).
  4 **`sendW_forms`** (K1.sendAtS), `openForms`, **`first_forms`** (K1.firstSegmentOpening: a new group
    without a row, then the sending).

Limits. Each of the three laws speaks of a yes on TWO rounds. The other members that turn the
statement (the code switch, the one equation, the closing, the clearing of a link, the head's
front, the memory's rows, the proximity test) have no such law in this file. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Shape.Commit
import Johnson.Desc.First.Shape.SendForms
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState GPar groundG)

/-! ## 1 The shape with the rows' makes beside it -/

/-- The first chain's shape, and beside it the makes of its statement's rows. -/
abbrev ChainF : Type := ChainSh × FormsSh

def chainF (s : S) : ChainF := (chainSh s, formsOf s.st)

/-- A step that reads and turns no row's make. -/
def quietF (g : ChainSh → Option ChainSh) (x : ChainF) : Option ChainF := (g x.1).map (·, x.2)

/-- A step on the shape with an update of the makes beside it. -/
def pairF (g : ChainSh → Option ChainSh) (f : ChainSh → FormsSh → FormsSh) (x : ChainF) :
    Option ChainF :=
  (g x.1).map (·, f x.1 x.2)

/-- From "carries" on the shape and a law on the makes to "carries" on the pair. -/
theorem pair_carries {g : ChainSh → Option ChainSh} {f : ChainSh → FormsSh → FormsSh} {s t : S}
    {u : ChainF} (hc : ∀ v, g (chainSh s) = some v → v = chainSh t)
    (hf : formsOf t.st = f (chainSh s) (formsOf s.st)) (h : pairF g f (chainF s) = some u) :
    u = chainF t := by
  unfold pairF chainF at h
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [hc v hv, ← hf]
  rfl

theorem quiet_carries {g : ChainSh → Option ChainSh} {s t : S} {u : ChainF}
    (hc : ∀ v, g (chainSh s) = some v → v = chainSh t) (hst : t.st = s.st)
    (h : quietF g (chainF s) = some u) : u = chainF t :=
  pair_carries (f := fun _ F => F) hc (by rw [hst]) h

/-! ## 2 The layings back turn no row -/

theorem putLink_st (s : S) (L : LinkCtx) : (s.putLink L).st = s.st := by
  unfold S.putLink
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem putFork_st (s : S) (F : Fork) : (s.putFork F).st = s.st := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-! ## 3 K1's commitment -/

theorem joinAll_forms {L : Type} (p : GPar) (g : Nat) :
    ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
      Send.joinAll groundG p g l d = some d' → formsOf d'.st = formsOf d.st
  | [], d, d', h => by
    cases h
    rfl
  | x :: l, d, d', h => by
    have h' : (Ground.joinP d g x.2 (decide (0 < x.1.life))).bind (Send.joinAll groundG p g l) =
        some d' := h
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h'
    rw [joinAll_forms p g l d₁ d' h2, join_forms h1]

/-- A later moment's yes: its sending's return, and the joinings behind it turn no row. -/
theorem laterOwn_forms {P : K1.Par} {owed : Option Nat} {c : ChainCheck} {w : DState Unit}
    {rs : List Fmt.RoundView} {y : ChainCheck × DState Unit} (h : K1.laterOwn P owed c w rs = .ok y) :
    ∃ x, K1.decideSend P owed w rs = .ok x ∧ formsOf y.2.st = formsOf x.2.st := by
  unfold K1.laterOwn at h
  simp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : K1.decideSend P owed w rs with
        | error e =>
          rw [hd] at h
          cases h
        | ok x =>
          rw [hd] at h
          simp only [] at h
          refine ⟨x, rfl, ?_⟩
          split at h
          · cases h
          · rename_i z hz
            cases h
            unfold Send.joinOwnP at hz
            split at hz
            · obtain ⟨d', hj, rfl⟩ := Option.map_eq_some_iff.1 hz
              exact joinAll_forms _ _ _ _ _ hj
            · cases hz

/-- **K1's commitment on the rows' makes**: no group's rows turn; each new message has its sample
rows' makes. From the yes alone. -/
theorem commit_forms {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s t : S}
    {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Unit) P link moment arrays).decide s [r₁, r₂] gs = .ok t) :
    formsOf t.st = sendForms P (chainSh s).core.st.oracles.length (formsOf s.st) := by
  rw [show (chainSh s).core.st.oracles.length = s.st.oracles.size from Ground.Sh.orc_size s.st]
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl _ _ _
    cases hb : (K1.commitOwn (Cl := Unit) P link moment arrays).decide
        ⟨K1.owedOf s, ⟨L, F, tl, K1.stateOf s ()⟩⟩ [r₁, r₂] gs with
    | error e => simp [hb, Except.map] at h
    | ok y =>
      simp only [hb, Except.map, Except.ok.injEq] at h
      subst h
      rw [putFork_st, putLink_st]
      show formsOf y.held.w.st = _
      unfold K1.commitOwn at hb
      simp only [] at hb
      split at hb
      · split at hb
        · cases hb
        · rename_i ts
          cases hc : L3.commitStep (K1.laterOwn P (K1.owedOf s)) ts
              ⟨L, F, tl, K1.stateOf s ()⟩ [r₁, r₂] with
          | error e => simp [hc, Except.map] at hb
          | ok z =>
            simp only [hc, Except.map, Except.ok.injEq] at hb
            subst hb
            show formsOf z.w.st = _
            unfold L3.commitStep at hc
            obtain ⟨_, -, hc⟩ := (K1.bind_ok _ _ _).1 hc
            obtain ⟨cw, h1, hc⟩ := (K1.bind_ok _ _ _).1 hc
            obtain ⟨LF, -, hc⟩ := (K1.bind_ok _ _ _).1 hc
            cases hc
            obtain ⟨x, hx, e⟩ := laterOwn_forms h1
            show formsOf cw.2.st = _
            rw [e]
            exact send_forms hx
      · cases hb
  · cases h

/-! ## 4 W's sending, and the first segment's opening -/

theorem sendW_forms {P : K1.Par} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.sendAtS (Cl := Unit) P).decide s [r₁, r₂] gs = .ok t) :
    formsOf t.st = sendForms P (chainSh s).core.st.oracles.length (formsOf s.st) := by
  rw [show (chainSh s).core.st.oracles.length = s.st.oracles.size from Ground.Sh.orc_size s.st]
  simp only [K1.sendAtS] at h
  split at h
  · split at h
    · cases hx : K1.decideSend P (K1.owedOf s) (K1.stateOf s #[]) [r₁, r₂] with
      | error e =>
        simp only [K1.sendOwn] at h
        rw [hx] at h
        cases h
      | ok x =>
        simp only [K1.sendOwn] at h
        rw [hx] at h
        cases h
        exact send_forms hx
    · cases h
  · cases h

/-- The makes behind the first segment's opening: a new group without a row; the new messages'
sample rows. -/
def openForms (P : K1.Par) (n0 : Nat) (F : FormsSh) : FormsSh :=
  sendForms P n0 { F with groups := F.groups ++ [[]] }

theorem first_forms {q : Params.First} {gp : GPar} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Unit) q gp).decide s [r₁, r₂] gs = .ok t) :
    formsOf t.st =
      openForms (K1.firstPar q gp) (chainSh s).core.st.oracles.length (formsOf s.st) := by
  rw [show (chainSh s).core.st.oracles.length = s.st.oracles.size from Ground.Sh.orc_size s.st]
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, -, h⟩ := (K1.bind_ok _ _ _).1 h
  obtain ⟨cd, h1, h⟩ := (K1.bind_ok _ _ _).1 h
  cases h
  show formsOf cd.2.st = _
  unfold K1.firstOwn at h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨Lk, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨gd, hg, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨x, hx, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨_, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨mask, -, h1⟩ := (K1.bind_ok _ _ _).1 h1
  obtain ⟨fd, hj, h1⟩ := (K1.bind_ok _ _ _).1 h1
  cases h1
  have hg' : Ground.newGroupP (K1.stateOf s ()) s.check.frame.shape.code
      s.check.frame.shape.maskCode = some gd := (K1.named_ok _ _ _).1 hg
  have hj' := (K1.named_ok _ _ _).1 hj
  have e3 : formsOf fd.2.st = formsOf x.2.st := by
    unfold Send.joinOwnP at hj'
    split at hj'
    · obtain ⟨d', hjj, rfl⟩ := Option.map_eq_some_iff.1 hj'
      exact joinAll_forms _ _ _ _ _ hjj
    · cases hj'
  have e1 := newGroup_forms hg'
  have en : gd.2.st.oracles.size = s.st.oracles.size := by
    unfold Ground.newGroupP at hg'
    split at hg'
    · cases hg'
      rfl
    · cases hg'
  show formsOf fd.2.st = _
  rw [e3, send_forms hx, e1, en]
  rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sendW_forms
#print axioms VerifiableInference.Desc.First.Shape.first_forms
#print axioms VerifiableInference.Desc.First.Shape.pair_carries
#print axioms VerifiableInference.Desc.First.Shape.quiet_carries
#print axioms VerifiableInference.Desc.First.Shape.joinAll_forms
#print axioms VerifiableInference.Desc.First.Shape.laterOwn_forms
#print axioms VerifiableInference.Desc.First.Shape.commit_forms
#print axioms VerifiableInference.Desc.First.Shape.putLink_st
#print axioms VerifiableInference.Desc.First.Shape.putFork_st
