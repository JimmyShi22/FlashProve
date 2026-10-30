-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CarriedOfLend.lean: the kind "the code switch" (K2): WHAT THE
STRETCHES ARE THAT THE SWITCH's PART CARRIES: wherever the frame's lending returns, the stretch
number i that the part is handed as carried is THE RUN OF ITS OWNER's CUT THAT THE BOOK's ENTRY
NAMES, BY START AND COUNT. Three statements with their proofs; no definition. The first is general:
no kind is named in it.

  `carried_of_lend`     of the frame's `lend`: general in the list of names and counts
  `carried_of_part`     of `lendPart`, at a part of any kind: the entries are the book's that name
                        the part's address as their spender and are marked as carried (their
                        field `once` is false), in the book's order
  `carried_of_handed`   at the switch's part: of what `handed` (Honest/K2/ScriptLots.lean) hands

The equation: `Stretch.carried ds y i = (Stretch.of (look e.owner).2).cut e.start e.count`, where e
is entry number i: both sides in `Except`: the right side is the cut itself, off all that `look` has
at the owner's address.

Near: `cut_of_lend` (Honest/K1/ScriptAtLaw.lean, of other authors): the like for the part's own cut
· `lend_head`, `lend_tie` (Honest/Thread/Four/FourTie.lean, the frame's authors'): `lend_head` is
the one step: what `lend` hands over for its first entry is the cut of that entry's owner's, from
its start, and the rest is lent: `carried_of_lend` is that step walked to entry number i and said of
`Stretch.carried`. Not called: that file stands over its authors' toy thread.

Limits. AN EQUATION AT EACH VALUE OF THE RUN's COINS: nothing on how they are drawn. That an entry's
owner is the sender that the place's public data mean (`SwitchPlace.front`) is not said here: the
book says who the owner is. That the lending returns is a premise. NO LOT IS LAID. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- **Of the frame's `lend`.** -/
theorem carried_of_lend (look : Addr → (d : Due) × Cs d) :
    ∀ (ds : List (String × Due)) (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y →
      ∀ (i : Nat) (e : Ahead), l[i]? = some e →
        Stretch.carried ds y i = (Stretch.of (look e.owner).2).cut e.start e.count
  | [], [], _, _, i, e, he => by simp at he
  | [], _ :: _, _, h, _, _, _ => by simp [lend] at h
  | _ :: _, [], _, h, _, _, _ => by simp [lend] at h
  | d :: ds, a :: l, y, h, i, e, he => by
    unfold lend at h
    by_cases h1 : (a.name != d.1) = true
    · rw [if_pos h1] at h
      cases h
    · rw [if_neg h1] at h
      by_cases h2 : (a.count != d.2) = true
      · rw [if_pos h2] at h
        cases h
      · rw [if_neg h2] at h
        have hcount : a.count = d.2 := by simpa using h2
        cases hc : (look a.owner).2.cut a.start d.2 with
        | none =>
          rw [hc] at h
          cases h
        | some x =>
          rw [hc] at h
          obtain ⟨y', hy', rfl⟩ := exMap_ok h
          cases i with
          | zero =>
            have ea : a = e := by simpa using he
            subst ea
            show Except.ok (Stretch.of x) = _
            unfold Stretch.cut Stretch.of
            rw [hcount]
            simp only [hc]
          | succ n =>
            exact carried_of_lend look ds l y' hy' n e (by simpa using he)

variable {V W X : Type}

/-- **Of `lendPart`, at a part of any kind.** -/
theorem carried_of_part (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) (c : p.Coins) (h : lendPart B rows look a p = .ok c) (i : Nat)
    (e : Ahead)
    (he : ((B.ahead.filter fun x => x.spender == a).filter (!·.once))[i]? = some e) :
    Stretch.carried p.carries c.2.2 i = (Stretch.of (look e.owner).2).cut e.start e.count := by
  unfold lendPart at h
  simp only at h
  by_cases h1 : (p.takes != dueAt rows a) = true
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    cases hc : (look a).2.cut ⟨0, 0⟩ p.takes with
    | none =>
      rw [hc] at h
      cases h
    | some own =>
      rw [hc] at h
      obtain ⟨sp, -, h'⟩ := exBind_ok h
      obtain ⟨ca, hca, rfl⟩ := exMap_ok h'
      exact carried_of_lend look p.carries _ ca hca i e he

variable {Bk : ProverCoinCounts}

/-- **At the switch's part.** -/
theorem carried_of_handed (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c) (i : Nat)
    (e : Ahead)
    (he : ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e) :
    Stretch.carried p.carries c.2.2 i =
      (Stretch.of (k.look ch e.owner).2).cut e.start e.count := by
  unfold handed at h
  cases hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [hl] at h
    cases h
  | ok c' =>
    rw [hl] at h
    have ec : c' = c := Option.some.inj h
    subst ec
    exact carried_of_part Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩ _ c' hl i e he

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.carried_of_lend
#print axioms ProofFile.Honest.K2.Law.carried_of_part
#print axioms ProofFile.Honest.K2.Law.carried_of_handed
