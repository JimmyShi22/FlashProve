-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchLent.lean: the closing of a segment (K10): a block of coins that the closing's part
carries is the very block of its owner's own coins, as a stretch (`K2.Stretch`, Honest/K2/Part.lean): the form in which the
shared text of a message's rows (`messageRows`, Honest/K2/Sending.lean) takes coins. For the field tie of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean): the closing makes a member's rows anew of a carried block; the member's sender made them
of a cut of its own coins.

  `carried_cut`      what `lend` (Honest/Frame.lean) hands for entry number n, read by `Stretch.carried`, is the cut of the
                   entry's owner's coins at the entry's start and count
  `cut_cut`          a cut of the cut from 0 on is the cut
  **`carried_is_own`**   so: where the owner's own coins are c₁ (the cut of its row from 0 on) and the sender cuts c' off c₁ at
                   the entry's start and count, the carried stretch number n is ⟨count, c'⟩
  `close_carried`    what the book gives the closing's part as carried is `lend` at the book's carrying entries for it

Limits. That an entry's owner, start and count are a given sender's address and a given message's place among its coins is
the book's matter: premises here. One look-up of coins serves both sides: nothing is said across chains.
-/
import Johnson.Desc.ProofFile.Honest.K10.Fast.Says
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K2.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Place)
open ProofFile.Honest.K2 (Stretch)

variable {V W X : Type}

/-- What `lend` hands for an entry, as a stretch: the cut of the owner's coins. -/
theorem carried_cut (look : Addr → (d : Due) × Cs d) : ∀ (ds : List (String × Due))
    (l : List Ahead) (y : CsAll ds), lend look ds l = .ok y → ∀ (n : Nat) (a : Ahead),
    l[n]? = some a →
      ∃ x : Cs a.count, (look a.owner).2.cut a.start a.count = some x ∧
        Stretch.carried ds y n = .ok ⟨a.count, x⟩
  | [], [], _, _, n, a, hn => by simp at hn
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h
  | d :: ds, e :: l, y, h, n, a, hn => by
    simp only [lend] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hcount
    split at h
    · cases h
    rename_i x hx
    cases hy : lend look ds l with
    | error _ =>
      rw [hy] at h
      cases h
    | ok y' =>
      rw [hy] at h
      cases h
      cases n with
      | zero =>
        obtain rfl : e = a := Option.some.inj hn
        have hc : e.count = d.2 := by simpa using hcount
        obtain ⟨dn, dd⟩ := d
        obtain ⟨en, eo, es, ec, ep, eb⟩ := e
        obtain rfl : ec = dd := hc
        exact ⟨x, hx, rfl⟩
      | succ m => exact carried_cut look ds l y' hy m a hn

/-- A cut of the cut from 0 on is the cut. -/
theorem cut_cut {d t a n : Due} {c : Cs d} {c₁ : Cs t} {c' : Cs n} (h1 : c.cut ⟨0, 0⟩ t = some c₁)
    (h2 : c₁.cut a n = some c') : c.cut a n = some c' := by
  unfold Cs.cut at h1 h2 ⊢
  split at h1
  · rename_i hb1
    cases h1
    split at h2
    · rename_i hb2
      cases h2
      have q1 : 0 + t.f ≤ d.f := hb1.1
      have q2 : 0 + t.e ≤ d.e := hb1.2
      have q3 := hb2.1
      have q4 := hb2.2
      rw [dif_pos ⟨by omega, by omega⟩]
      refine congrArg some ?_
      congr 1
      · funext i
        exact congrArg c.f (Fin.ext (Nat.zero_add _).symm)
      · funext i
        exact congrArg c.e (Fin.ext (Nat.zero_add _).symm)
    · cases h2
  · cases h1

/-- **A carried stretch is the sender's own cut.** -/
theorem carried_is_own {look : Addr → (d : Due) × Cs d} {ds : List (String × Due)} {l : List Ahead} {y : CsAll ds}
    (h : lend look ds l = .ok y) {n : Nat} {a : Ahead} (hn : l[n]? = some a) {t : Due} {c₁ : Cs t}
    (h1 : (look a.owner).2.cut ⟨0, 0⟩ t = some c₁) {c' : Cs a.count} (h2 : c₁.cut a.start a.count = some c') :
    Stretch.carried ds y n = .ok ⟨a.count, c'⟩ := by
  obtain ⟨x, hx, hs⟩ := carried_cut look ds l y h n a hn
  obtain rfl : x = c' := Option.some.inj (hx.symm.trans (cut_cut h1 h2))
  exact hs

/-- What the book gives the closing's part as carried. -/
theorem close_carried {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {pl : Place}
    {J : CloseJob W} {cc : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins}
    (hcc : closeCoins (V := V) (X := X) Bk rows look pl J = .ok cc) :
    lend look (closeCarries J.pub) (K12.Light.carriedOf Bk ⟨pl, 0⟩) = .ok (handSnd cc).2.2 := by
  unfold closeCoins at hcc
  cases hr : lendRow Bk rows look pl ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0 with
  | error e =>
    rw [hr] at hcc
    cases hcc
  | ok r =>
    rw [hr] at hcc
    obtain rfl : r.1 = cc := Except.ok.inj hcc
    simp only [lendRow] at hr
    cases hp : lendPart Bk rows look ⟨pl, 0⟩ (closePart (V := V) (X := X) (foldShellT true J foldWords)) with
    | error e =>
      rw [hp] at hr
      cases hr
    | ok c' =>
      rw [hp] at hr
      have e : r = (c', ()) := (Except.ok.inj hr).symm
      subst e
      exact K12.Light.carried_of_lendPart Bk rows look ⟨pl, 0⟩ _ c' hp

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.carried_cut
#print axioms ProofFile.Honest.K10.cut_cut
#print axioms ProofFile.Honest.K10.carried_is_own
#print axioms ProofFile.Honest.K10.close_carried
