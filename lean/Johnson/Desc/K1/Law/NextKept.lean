-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/NextKept.lean: the kind K1's three blocks at the record that the first chain
carries leave the sub-proof's ledger's next free slot as it was.

  firstAtS_fork    the first segment's opening leaves the whole ledger (it stands between two links:
                   there is none, in front and behind).
  commitAtS_fork   a segment's later moment: behind a yes the ledger is there, and its next free
                   slot is the one in front. (It writes the trees' roots into the ledger: the rest
                   is not said here.)
  sendAtS_fork     W's sending leaves the whole ledger (none, at the members' places).
Each in the form (s'.fork?).map (·.next) = (s.fork?).map (·.next) too: ..._next.

They rest on Johnson/Desc/K1/KeepsNext.lean (commitAtS_next).
What is not claimed. Nothing on the block that a seat lays around or behind one of these three.
Nothing on soundness.

-/
import Johnson.Desc.K1.KeepsNext
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

theorem fork_laid {Lc : Type} (s : S) (d : DState Lc) : (laid s d).fork? = s.fork? := rfl

/-- Where a ledger is there, the one that is put is the one that is read. -/
theorem fork_put {Lc : Type} (s : S) (d : DState Lc) (L' : LinkCtx) (F F' : Fork)
    (h : s.fork? = some F) : (((laid s d).putLink L').putFork F').fork? = some F' := by
  unfold S.fork? at h
  unfold S.fork? S.putFork S.putLink laid
  cases hh : s.here with
  | lay a => simp
  | att a => simp
  | head a =>
    rw [hh] at h
    by_cases ho : a.opened <;> simp [ho] at h ⊢
  | _ => simp [hh] at h

variable {Cl : Type}

theorem firstAtS_fork {q : Params.First} {gp : GPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') : s'.fork? = s.fork? := by
  simp only [firstSegmentOpening, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl

theorem firstAtS_next {q : Params.First} {gp : GPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') :
    (s'.fork?).map (·.next) = (s.fork?).map (·.next) := by
  rw [firstAtS_fork h]

theorem commitAtS_fork {P : Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    ∃ F F', s.fork? = some F ∧ s'.fork? = some F' ∧ F'.next = F.next := by
  obtain ⟨L, F, tl, y, _, hF, _, hs, hn⟩ := commitAtS_next h
  exact ⟨F, y.F, hF, by rw [hs]; exact fork_put s y.w y.L F y.F hF, hn⟩

theorem commitAtS_next' {P : Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    (s'.fork?).map (·.next) = (s.fork?).map (·.next) := by
  obtain ⟨F, F', h1, h2, h3⟩ := commitAtS_fork h
  rw [h1, h2, Option.map_some, Option.map_some, h3]

theorem sendAtS_fork {P : Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (sendAtS (Cl := Cl) P).decide s rs gs = .ok s') : s'.fork? = s.fork? := by
  simp only [sendAtS] at h
  cases hh : s.here with
  | mem a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · cases hb : (sendOwn (Cl := Cl) P).decide { owed := owedOf s, held := stateOf s #[] } rs
          gs with
      | error e => rw [hb] at h; cases h
      | ok y =>
        rw [hb] at h
        simp only [Except.map, Except.ok.injEq] at h
        subst h
        simp [S.fork?, hh]
    · cases h
  | _ => rw [hh] at h; cases h

end VerifiableInference.Desc.K1
