-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/LastSpot.lean: the last place of a proof file's first chain is the
seal's. Theorems only; no file of the description imports this one.
Why. `chainC` (FillCore.lean) takes the chain's last block by its position in the list of blocks,
which follows the list of places (`spotsOf`, Places.lean). To say which block that is, one has to
know the last place.
  `byPlace_end`     where the last row of the table has another place number than the row before
                    it, `byPlace` leaves it a group of its own, the last
  `spotsFrom_end`   where the last group is one row with the head "seal" and the kind "SEAL", the
                    last place is of the kind `frame` and belongs to no segment
  `spotsOf_end`     the two together; the table's last two rows are premises
  `spotsOf_cutOf_of`   the same for a table that `cutOf` returns: `cutOf_end`
                    (Johnson/Desc/First/Driver/CutEnd.lean) supplies the two rows. That the head of
                    the name "seal.behind" is "seal" is a premise there
  `spotsOf_cutOf`   the same without that premise: `head_seal` (HeadSeal.lean) pays it

-/
import Johnson.Desc.ProofFile.Places
import Johnson.Desc.ProofFile.Law.HeadSeal
import Johnson.Desc.First.Driver.CutEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.First (Cut cutOf cutOf_end endCuts)

theorem byPlace_end (m s : Cut) (h : s.place ≠ m.place) :
    ∀ pre : List Cut, ∃ G t, byPlace (pre ++ [m, s]) = G :: (t ++ [[s]])
  | [] => ⟨[m], [], by simp [byPlace, h]⟩
  | c :: pre => by
    obtain ⟨G, t, e⟩ := byPlace_end m s h pre
    rw [List.cons_append, byPlace, e]
    cases G with
    | nil => exact ⟨[c], [] :: t, rfl⟩
    | cons d g =>
      by_cases hc : (d.place == c.place && headOf d.look == headOf c.look) = true
      · exact ⟨c :: d :: g, t, if_pos hc⟩
      · exact ⟨[c], (d :: g) :: t, if_neg hc⟩

theorem kindName_seal : kindName "seal" "SEAL" = some KindName.frame := by
  simp [kindName]

theorem behindLinks_seal : behindLinks "seal" = true := by
  simp [behindLinks]

theorem spotsFrom_end (s : Cut) (hh : headOf s.look = "seal") (hk : s.kind = "SEAL") :
    ∀ (gs : List (List Cut)) (link piece : Nat) (last : String) (l : List Spot),
      spotsFrom (gs ++ [[s]]) link piece last = some l →
      ∃ l0 sp, l = l0 ++ [sp] ∧ sp.place.kind = KindName.frame ∧ sp.place.link = none
  | [], link, piece, last, l, h => by
    rw [List.nil_append] at h
    simp only [spotsFrom, hh, hk, kindName_seal, behindLinks_seal, Option.bind_some,
      Option.map_some] at h
    rw [if_neg (by decide)] at h
    cases h
    exact ⟨[], _, rfl, rfl, rfl⟩
  | [] :: gs, link, piece, last, l, h => by
    rw [List.cons_append, spotsFrom] at h
    exact spotsFrom_end s hh hk gs link piece last l h
  | (c :: g) :: gs, link, piece, last, l, h => by
    rw [List.cons_append, spotsFrom] at h
    try dsimp only at h
    obtain ⟨k, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l', hl', h⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l0, sp, rfl, h1, h2⟩ := spotsFrom_end s hh hk gs _ _ _ l' hl'
    split at h
    · exact ⟨_ :: _ :: _ :: l0, sp, h.symm, h1, h2⟩
    · exact ⟨_ :: l0, sp, h.symm, h1, h2⟩

/-- Where the table of steps ends in the rows `m`, `s`, of different place numbers, and `s` has the
head "seal" and the kind "SEAL": the last of the chain's places is of the kind `frame` and belongs
to no segment. -/
theorem spotsOf_end {pre : List Cut} {m s : Cut} {l : List Spot} (h : s.place ≠ m.place)
    (hh : headOf s.look = "seal") (hk : s.kind = "SEAL")
    (hl : spotsOf (pre ++ [m, s]) = some l) :
    ∃ l0 sp, l = l0 ++ [sp] ∧ sp.place.kind = KindName.frame ∧ sp.place.link = none := by
  obtain ⟨G, t, e⟩ := byPlace_end m s h pre
  unfold spotsOf at hl
  rw [e] at hl
  exact spotsFrom_end s hh hk (G :: t) 0 1 "" l hl

/-- The same for a table that `cutOf` returns, through `cutOf_end`
(Johnson/Desc/First/Driver/CutEnd.lean). `hh`: the head of the seal's row's name. -/
theorem spotsOf_cutOf_of {es : List Fmt.Entry} {cs : List Cut} {l : List Spot}
    (hh : headOf "seal.behind" = "seal") (hc : cutOf es = some cs) (hl : spotsOf cs = some l) :
    ∃ l0 sp, l = l0 ++ [sp] ∧ sp.place.kind = KindName.frame ∧ sp.place.link = none := by
  obtain ⟨front, pl, q, b, rfl, _⟩ := cutOf_end hc
  have e : front ++ endCuts pl q b =
      (front ++ [⟨"M.0.front", "mFront", pl, "batPsc", 0⟩, ⟨"M.0.call", "mBatt", pl, "batPsc", b⟩,
        ⟨"M.0.quiet", "mBattQuiet", pl, "batPsc", 0⟩, ⟨"M.1.call", "mSend", q, "send", 2⟩]) ++
      [⟨"M.1.quiet", "mSendQuiet", q, "send", 0⟩, ⟨"seal.behind", "seal", q + 1, "SEAL", 0⟩] := by
    rw [List.append_assoc]
    rfl
  rw [e] at hl
  exact spotsOf_end (Nat.succ_ne_self q) hh rfl hl

/-- The same without the premise: `head_seal` (HeadSeal.lean) pays it. -/
theorem spotsOf_cutOf {es : List Fmt.Entry} {cs : List Cut} {l : List Spot}
    (hc : cutOf es = some cs) (hl : spotsOf cs = some l) :
    ∃ l0 sp, l = l0 ++ [sp] ∧ sp.place.kind = KindName.frame ∧ sp.place.link = none :=
  spotsOf_cutOf_of head_seal hc hl

end ProofFile.Law

#print axioms ProofFile.Law.spotsOf_cutOf
#print axioms ProofFile.Law.spotsOf_cutOf_of
#print axioms ProofFile.Law.byPlace_end
#print axioms ProofFile.Law.spotsFrom_end
#print axioms ProofFile.Law.spotsOf_end
