-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/Long.lean: the code switch: the old group's long symbol at a drawn
position, as a function with code of the record, the two rounds and the groups of columns; and:
where the text's decide says yes, it is there at every drawn position.

  frontAt   the front that the switch is handed, by the place's sort: at a link what firstFront
            makes of the record; at the head's link headFrontOf; at the finish finFrontOf
  oldRead   the text's own chain up to the reading of the old rows: the front; the sending; the
            arguments of the step behind it (behindArgs); the old main code; the positions
            (Positions.ofDraws at that code's log-length, of round 2's draws); readOld. It returns
            the old single rows, the positions and the array y of their symbols
  longAt    the slice of y at a position, written out (entry number i * rows + coord α at the
            position's index i; Slice.lean's sliceAt_drawn is spent in yes_long's proof), under a
            numbering coord of the typed open word's coordinates by the rows 0 … rows - 1
  read_of_switch  a yes of the switch at a front: the old rows were read, and the array has (listed
            positions) * (rows) entries: the maker's first guard, read off
  oldRead_of, YesOldRead, yes_oldRead  a yes of decideWith gives: oldRead is there; its positions
            are those of round 2's draws at the place's own log-length; y has just (listed
            positions) * (rows) entries
  YesLong, yes_long  so longAt is there at every drawn position: the clause on the long symbols of
            the hearing law, with the two rounds as arguments
The sending snd is a letter throughout.
LIMITS. coord is a letter: which coordinate of the typed open word is which row is not said here,
and an index from rows on would be read as 0. That the long symbols ARE the typed open word's is not
here.
PURE FUNCTIONS OF THE HAND-WRITTEN PROGRAM's FILES THAT THIS FILE ITSELF NAMES: Positions.ofDraws,
Positions.indexOf, SingleRows.rows, zeroE; the library's readE. The rows' maker, whose first guard
is read in read_of_switch, is the own-text swRows (Johnson/Desc/Own/SwitchRows.lean). THROUGH THE
RECORD S AND THE TEXT's OWN CALLS a walk by constants beneath these theorems, made once by program
over another state of the texts beneath, met 36 modules under
OnBytes.Iop, OnBytes.Model, OnBytes.Params and OnBytes.Proof: records and pure routines. It met no
name that runs in a context (Blk, Ctx, Chan, SubM, LinkM, StateT, EStateM, IO). No soundness is
claimed.
-/
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.K2Hears.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut readOld switchBehind switchE firstFront switchNotices)
open VerifiableInference.Desc.First.K2Hears (sliceAt sliceAt_drawn)

/-- The front that the switch is handed, by the place's sort. -/
def frontAt (p : P2) (s : S) : Option _root_.Tw.K2.Front :=
  match p.stands, s.here with
  | .link, _ => (firstFront s.st s.check.frame).toOption
  | .head, .head a =>
    (s.check.frame.groups[s.check.frame.link]?).map fun G => headFrontOf s a G.target
  | .finish, .fin a => a.G.map fun G => finFrontOf s a G
  | _, _ => none

/-- The text's own chain up to the reading of the old rows. -/
def oldRead (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : Option (SingleRows × Positions × Array E) := do
  let x ← frontAt p s
  let y ← (snd (par9 p) x.st s.book s.roots s.noneWaits (switchNotices x.T x.others) r₁ r₂).toOption
  let i := behindArgs (par9 p) x y r₂ (flat p gs)
  let c ← i.st.codes.base[i.old.code]?
  let o ← (readOld i (Positions.ofDraws c.logN i.drawn.poss)).toOption
  pure (i.old, Positions.ofDraws c.logN i.drawn.poss, o.2.2)

/-- The old group's long symbol at the position q. -/
def longAt {Aa : Type} (coord : Aa → Nat) (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (q : Nat) : Option (Aa → Cb.Gl.E) :=
  (oldRead snd p s r₁ r₂ gs).bind fun o =>
    (o.2.1.indexOf q).map fun i α => OnBytes.Slice.readE (o.2.2.getD (i * o.1.rows + coord α) zeroE)

/-- From a yes of the switch at a front: the chain behind the front. -/
theorem read_of_switch {snd : _root_.Tw.K2.SendFn} {p : P2} {s9 : _root_.Tw.K2.S9}
    {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {cols w roots}
    (h : switchE switchBehind (par9 p) snd s9 x r₁ r₂ cols = .ok (w, roots)) :
    ∃ y c Y, snd (par9 p) x.st s9.book s9.roots s9.settled (switchNotices x.T x.others) r₁ r₂ = .ok
        y ∧
      (behindArgs (par9 p) x y r₂ cols).st.codes.base[(behindArgs (par9 p) x y r₂ cols).old.code]? =
        some c ∧ c.logN = p.logN ∧
      readOld (behindArgs (par9 p) x y r₂ cols) (Positions.ofDraws c.logN r₂.drawn.poss) =
        .ok (w.book, w.opened, Y) ∧
      Y.size = (Positions.ofDraws c.logN r₂.drawn.poss).all.size * x.f.rows.rows := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨c, Y, S1, S2, S3, rows, hb⟩ := switchBehind_inv hs.hBehind
  have hn := locOk_numbers hb.hLoc
  refine ⟨y, c, Y, hs.hSend, hb.hCode, hn.2.1.symm, hb.hRead, ?_⟩
  have hr := hb.hRows
  by_contra hne
  have hg : (Y.size == (Positions.ofDraws c.logN r₂.drawn.poss).all.size * x.f.rows.rows) = false :=
      by
    simpa using hne
  have hnone : VerifiableInference.Desc.Own.swRows S3 x.f.rows x.T ((behindArgs (par9 p) x y r₂
      cols).ids.getD 0 noId)
      ((behindArgs (par9 p) x y r₂ cols).ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws c.logN r₂.drawn.poss) Y = none := by
    unfold VerifiableInference.Desc.Own.swRows
    simp [guard, hg]
  rw [show VerifiableInference.Desc.Own.swRows S3 (behindArgs (par9 p) x y r₂ cols).old (behindArgs
      (par9 p) x y r₂ cols).T
      ((behindArgs (par9 p) x y r₂ cols).ids.getD 0 noId)
      ((behindArgs (par9 p) x y r₂ cols).ids.extract 1
        (1 + (behindArgs (par9 p) x y r₂ cols).T.kept.size))
      (Positions.ofDraws c.logN (behindArgs (par9 p) x y r₂ cols).drawn.poss) Y = none from hnone]
          at hr
  cases hr

/-- The chain, where each of its steps is there. -/
theorem oldRead_of {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {c :
        Code}
    {B : TreeBook} {left : List _root_.Tw.K2.Col} {Y : Array E} (hx : frontAt p s = some x)
    (hy : snd (par9 p) x.st s.book s.roots s.noneWaits (switchNotices x.T x.others) r₁ r₂ = .ok y)
    (hc : (behindArgs (par9 p) x y r₂ (flat p gs)).st.codes.base[
      (behindArgs (par9 p) x y r₂ (flat p gs)).old.code]? = some c)
    (hr : readOld (behindArgs (par9 p) x y r₂ (flat p gs))
      (Positions.ofDraws c.logN r₂.drawn.poss) = .ok (B, left, Y)) :
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws c.logN r₂.drawn.poss, Y) := by
  have hr' : readOld (behindArgs (par9 p) x y r₂ (flat p gs))
      (Positions.ofDraws c.logN (behindArgs (par9 p) x y r₂ (flat p gs)).drawn.poss) =
        .ok (B, left, Y) := hr
  unfold oldRead
  simp only [hx, hy, Except.toOption, Option.bind_eq_bind, Option.bind_some, hc, hr']
  rfl

/-- **A yes of decide: the old rows are read**, at the positions of round 2's draws, at the place's
own
log-length; the array has one symbol for each row at each listed position. -/
def YesOldRead : Prop := ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ old Y, oldRead snd p s r₁ r₂ gs = some (old, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
    Y.size = (Positions.ofDraws p.logN r₂.drawn.poss).all.size * old.rows

theorem yes_oldRead : YesOldRead := fun snd p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨y, c, Y, hy, hc, hn, hr, hz⟩ := read_of_switch hl.hSwitch
    have hx : frontAt p s = some x := by simp [frontAt, hp, hl.hFront, Except.toOption]
    exact ⟨x.f.rows, Y, hn ▸ oldRead_of hx hy hc hr, hn ▸ hz⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨y, c, Y, hy, hc, hn, hr, hz⟩ := read_of_switch hl.hSwitch
    have hx : frontAt p s = some (headFrontOf s o G.target) := by
      simp [frontAt, hp, hl.hHere, hl.hGroup]
    exact ⟨_, Y, hn ▸ oldRead_of hx hy hc hr, hn ▸ hz⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨y, c, Y, hy, hc, hn, hr, hz⟩ := read_of_switch hl.hSwitch
    have hx : frontAt p s = some (finFrontOf s o G) := by simp [frontAt, hp, hl.hHere, hl.hLaid]
    exact ⟨_, Y, hn ▸ oldRead_of hx hy hc hr, hn ▸ hz⟩

/-- **A yes of decide: the long symbol is there at every drawn position**: it is the slice of the
array
that the text itself read, and every entry that it reads for a coordinate numbered below the number
of
rows lies inside the array: no 0 is laid in there. -/
def YesLong : Prop := ∀ (Aa : Type) (coord : Aa → Nat) snd p s r₁ r₂ gs s',
  decideWith snd p s [r₁, r₂] gs = .ok s' → ∀ q ∈ r₂.drawn.poss,
    ∃ old Y i, oldRead snd p s r₁ r₂ gs = some (old, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
      (Positions.ofDraws p.logN r₂.drawn.poss).indexOf q = some i ∧
      longAt coord snd p s r₁ r₂ gs q =
        some (fun α => OnBytes.Slice.readE (Y.getD (i * old.rows + coord α) zeroE)) ∧
      ∀ α, coord α < old.rows → i * old.rows + coord α < Y.size

theorem yes_long : YesLong := fun Aa coord snd p s r₁ r₂ gs s' h q hq => by
  obtain ⟨old, Y, ho, hz⟩ := yes_oldRead snd p s r₁ r₂ gs s' h
  obtain ⟨i, hi, hlt, _⟩ := sliceAt_drawn old.rows p.logN r₂.drawn.poss Y q hq
  refine ⟨old, Y, i, ho, hi, ?_, fun α hα => ?_⟩
  · unfold longAt
    rw [ho]
    simp only [Option.bind_some, hi, Option.map_some]
  · rw [hz]
    calc i * old.rows + coord α < i * old.rows + old.rows := Nat.add_lt_add_left hα _
      _ = (i + 1) * old.rows := (Nat.succ_mul _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hlt

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.yes_oldRead
#print axioms VerifiableInference.Desc.First.K2.yes_long
