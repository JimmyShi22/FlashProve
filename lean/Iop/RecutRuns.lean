-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutRuns.lean: all rounds of an arbitrary list are merged into the round after them.

The merges are by (J1) of Iop/Join.lean: two prover messages become one where the challenge between
them has one value. `XPlan.app` (Iop/RecutKit.lean) merges nothing across the border of two lists of
rounds, and a list that is given by a case distinction or as a field of a record does not unfold to
r1 :: r2 :: ... Here the plan of splits and merges (`XPlan`, Iop/Recut.lean) is made by recursion on
the list s, so nothing need be known of its form: bare messages (rounds whose challenge has one
value) before a round r become one prover message with that of r.
  `Round.into s r`: the new round ((r1 ⋈ r2) ⋈ ..) ⋈ r, where ⋈ is `Round.joinMsg`; it is r if s is
      empty. Its challenge is that of r.
  `XPlan.msgAll s ρ Q`: the plan of s ++ r :: t: the merges, and then the plan Q with the new round
      as its first round. ρ gives, for each round of s, the one value of its challenge.
  `Shape.AllUnit s ρ`: the condition that every challenge of s has the one value that ρ names.
  `Shape.Units s`, `Shape.unitRho s h`, `allUnit_unitRho`: "every verifier message of s has exactly
      one value" (every challenge), as a proposition; the values, found in the finite types by
      search (`Fintype.choose`; Lean's list of axioms under `Shape.unitRho` is propext and
      Quot.sound); so a plan needs only the proposition.
For `XPlan.msgAll` the file proves `XPlan.OK` from `Shape.AllUnit s ρ` and `Q.OK` (`msgAll_ok`),
counts splits and merges, computes `XPlan.maxRunFrom` (the first round of Q counts for `s.length`
more old rounds) and `XPlan.idx` (Iop/BatchRecut.lean) from the round r on, and carries
`XPlan.FirstOfRun` (Iop/RecutSlots.lean) over from Q, for the rounds after r.
No split is added, so there are no new further data (`XPlan.Kits`, Iop/RecutData.lean;
`XPlan.Kits.msgAll`).
-/
import Iop.RecutSlots
import Iop.RecutProofs

namespace Iop

/-! ## 1. The plan -/

def Round.intoFrom : Round → Shape → Round → Round
  | h, [], r => h.joinMsg r
  | h, b :: s, r => Round.intoFrom (h.joinMsg b) s r

/-- The round made of all rounds of s and of r. -/
def Round.into : Shape → Round → Round
  | [], r => r
  | h :: s, r => Round.intoFrom h s r

def XPlan.msgFrom :
    (h : Round) → (s : Shape) → h.Chal → Rho s → {r : Round} → {t : Shape} →
    XPlan (Round.intoFrom h s r :: t) → XPlan (h :: (s ++ r :: t))
  | h, [], u, _, r, _, Q => .msg h r u Q
  | h, b :: s, u, ρ, _, _, Q => .msg h b u (XPlan.msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q)

/-- All rounds of s are merged by (J1) into the round after them. -/
def XPlan.msgAll :
    (s : Shape) → Rho s → {r : Round} → {t : Shape} →
    XPlan (Round.into s r :: t) → XPlan (s ++ r :: t)
  | [], _, _, _, Q => Q
  | h :: s, ρ, _, _, Q => XPlan.msgFrom h s ρ.1 ρ.2 Q

/-- Every challenge of s has the one value that ρ names. -/
def Shape.AllUnit : (s : Shape) → Rho s → Prop
  | [], _ => True
  | h :: s, ρ => (∀ c : h.Chal, c = ρ.1) ∧ Shape.AllUnit s ρ.2

/-- Every challenge of s has exactly one value. -/
def Shape.Units : Shape → Prop
  | [] => True
  | r :: s => (∃! _c : r.Chal, True) ∧ Shape.Units s

/-- The one value of each challenge. -/
def Shape.unitRho : (s : Shape) → s.Units → Rho s
  | [], _ => ()
  | r :: s, h =>
      (letI : DecidableEq r.Chal := fun _ _ => isTrue (h.1.unique trivial trivial)
       Fintype.choose (fun _ : r.Chal => True) h.1, Shape.unitRho s h.2)

theorem Shape.allUnit_unitRho : ∀ (s : Shape) (h : s.Units), Shape.AllUnit s (Shape.unitRho s h)
  | [], _ => trivial
  | _ :: s, h => ⟨fun _ => h.1.unique trivial trivial, Shape.allUnit_unitRho s h.2⟩

/-! ## 2. Conditions and counts -/

theorem XPlan.msgFrom_ok :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        {Q : XPlan (Round.intoFrom h s r :: t)},
      (∀ c, c = u) → Shape.AllUnit s ρ → Q.OK → (XPlan.msgFrom h s u ρ Q).OK
  | _, [], _, _, _, _, _, hu, _, hQ => ⟨hu, hQ⟩
  | h, b :: s, _, ρ, _, _, _, hu, hs, hQ =>
    ⟨hu, XPlan.msgFrom_ok (h.joinMsg b) s ρ.1 ρ.2 hs.1 hs.2 hQ⟩

theorem XPlan.msgAll_ok :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} {Q : XPlan (Round.into s r :: t)},
      Shape.AllUnit s ρ → Q.OK → (XPlan.msgAll s ρ Q).OK
  | [], _, _, _, _, _, hQ => hQ
  | h :: s, ρ, _, _, _, hs, hQ => XPlan.msgFrom_ok h s ρ.1 ρ.2 hs.1 hs.2 hQ

theorem XPlan.cuts_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)),
      (XPlan.msgFrom h s u ρ Q).cuts = Q.cuts
  | _, [], _, _, _, _, _ => rfl
  | h, b :: s, _, ρ, _, _, Q => XPlan.cuts_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q

theorem XPlan.cuts_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} (Q : XPlan (Round.into s r :: t)),
      (XPlan.msgAll s ρ Q).cuts = Q.cuts
  | [], _, _, _, _ => rfl
  | h :: s, ρ, _, _, Q => XPlan.cuts_msgFrom h s ρ.1 ρ.2 Q

theorem XPlan.joins_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)),
      (XPlan.msgFrom h s u ρ Q).joins = Q.joins + (s.length + 1)
  | _, [], _, _, _, _, _ => rfl
  | h, b :: s, _, ρ, _, _, Q =>
    (congrArg (· + 1) (XPlan.joins_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q)).trans (Nat.add_assoc _ _ _)

theorem XPlan.joins_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} (Q : XPlan (Round.into s r :: t)),
      (XPlan.msgAll s ρ Q).joins = Q.joins + s.length
  | [], _, _, _, _ => rfl
  | h :: s, ρ, _, _, Q => XPlan.joins_msgFrom h s ρ.1 ρ.2 Q

theorem XPlan.msgFrom_noCut :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        {Q : XPlan (Round.intoFrom h s r :: t)},
      Q.NoCut → (XPlan.msgFrom h s u ρ Q).NoCut
  | _, [], _, _, _, _, _, hQ => hQ
  | h, b :: s, _, ρ, _, _, _, hQ => XPlan.msgFrom_noCut (h.joinMsg b) s ρ.1 ρ.2 hQ

theorem XPlan.msgAll_noCut :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} {Q : XPlan (Round.into s r :: t)},
      Q.NoCut → (XPlan.msgAll s ρ Q).NoCut
  | [], _, _, _, _, hQ => hQ
  | h :: s, ρ, _, _, _, hQ => XPlan.msgFrom_noCut h s ρ.1 ρ.2 hQ

theorem XPlan.maxRunFrom_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)) (w : ℕ),
      (XPlan.msgFrom h s u ρ Q).maxRunFrom w = Q.maxRunFrom (w + (s.length + 1))
  | _, [], _, _, _, _, _, _ => rfl
  | h, b :: s, _, ρ, _, _, Q, w =>
    (XPlan.maxRunFrom_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q (w + 1)).trans
      (congrArg Q.maxRunFrom (by show w + 1 + (s.length + 1) = w + (s.length + 1 + 1); omega))

theorem XPlan.maxRunFrom_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} (Q : XPlan (Round.into s r :: t)) (w : ℕ),
      (XPlan.msgAll s ρ Q).maxRunFrom w = Q.maxRunFrom (w + s.length)
  | [], _, _, _, _, _ => rfl
  | h :: s, ρ, _, _, Q, w => XPlan.maxRunFrom_msgFrom h s ρ.1 ρ.2 Q w

/-! ### Where old rounds begin -/

/-- Round number m after the merged rounds (m = 0: the round r) has the `XPlan.idx`
(Iop/BatchRecut.lean) of round m of Q's list of rounds. -/
theorem XPlan.idx_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)) (m : ℕ),
      (XPlan.msgFrom h s u ρ Q).idx (s.length + 1 + m) = Q.idx m
  | _, [], _, _, _, _, Q, m => congrArg Q.idx (by show 0 + 1 + m - 1 = m; omega)
  | h, b :: s, _, ρ, _, _, Q, m =>
      (congrArg (XPlan.msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q).idx
          (by show s.length + 1 + 1 + m - 1 = s.length + 1 + m; omega)).trans
        (XPlan.idx_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q m)

theorem XPlan.idx_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} (Q : XPlan (Round.into s r :: t)) (m : ℕ),
      (XPlan.msgAll s ρ Q).idx (s.length + m) = Q.idx m
  | [], _, _, _, Q, m => congrArg Q.idx (Nat.zero_add m)
  | h :: s, ρ, _, _, Q, m => XPlan.idx_msgFrom h s ρ.1 ρ.2 Q m

/-- A round after r is merged into the round before it only if it is so in Q. -/
theorem XPlan.firstOfRun_msgFrom :
    ∀ (h : Round) (s : Shape) (u : h.Chal) (ρ : Rho s) {r : Round} {t : Shape}
        (Q : XPlan (Round.intoFrom h s r :: t)) (m : ℕ),
      Q.FirstOfRun (m + 1) → (XPlan.msgFrom h s u ρ Q).FirstOfRun (s.length + 1 + (m + 1))
  | _, [], _, _, _, _, Q, m, hQ => by
      show (XPlan.msg _ _ _ Q).FirstOfRun (0 + 1 + (m + 1))
      rw [show 0 + 1 + (m + 1) = m + 2 by omega]
      exact hQ
  | h, b :: s, u, ρ, _, _, Q, m, hQ => by
      show (XPlan.msg h b u (XPlan.msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q)).FirstOfRun
        (s.length + 1 + 1 + (m + 1))
      rw [show s.length + 1 + 1 + (m + 1) = (s.length + 1 + m) + 2 by omega]
      have := XPlan.firstOfRun_msgFrom (h.joinMsg b) s ρ.1 ρ.2 Q m hQ
      rw [show s.length + 1 + (m + 1) = (s.length + 1 + m) + 1 by omega] at this
      exact this

theorem XPlan.firstOfRun_msgAll :
    ∀ (s : Shape) (ρ : Rho s) {r : Round} {t : Shape} (Q : XPlan (Round.into s r :: t)) (m : ℕ),
      Q.FirstOfRun (m + 1) → (XPlan.msgAll s ρ Q).FirstOfRun (s.length + (m + 1))
  | [], _, _, _, Q, m, hQ => by
      show Q.FirstOfRun (0 + (m + 1))
      rw [Nat.zero_add]
      exact hQ
  | h :: s, ρ, _, _, Q, m, hQ => XPlan.firstOfRun_msgFrom h s ρ.1 ρ.2 Q m hQ

theorem XPlan.firstOfRun_zero {s : Shape} (P : XPlan s) : P.FirstOfRun 0 := by
  induction P with
  | nil => trivial
  | keep r P ih => trivial
  | cut c P ih => trivial
  | msg r1 r2 u P ih => exact ih
  | chal r1 r2 np P ih => exact ih

theorem XPlan.firstOfRun_keepAll : ∀ (s : Shape) (n : ℕ), (XPlan.keepAll s).FirstOfRun n
  | [], _ => trivial
  | _ :: _, 0 => trivial
  | _ :: s, n + 1 => XPlan.firstOfRun_keepAll s n

theorem XPlan.firstOfRun_app_ge
    {s t : Shape} (P : XPlan s) (Q : XPlan t) (m : ℕ) (hQ : Q.FirstOfRun m) :
    (XPlan.app P Q).FirstOfRun (s.length + m) := by
  induction P with
  | nil =>
      show Q.FirstOfRun (0 + m)
      rw [Nat.zero_add]
      exact hQ
  | @keep r s P ih =>
      show (XPlan.keep r (XPlan.app P Q)).FirstOfRun (s.length + 1 + m)
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      exact ih
  | @cut r s c P ih =>
      show (XPlan.cut c (XPlan.app P Q)).FirstOfRun (s.length + 1 + m)
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      have : (XPlan.app P Q).FirstOfRun (s.length + 1 + m) := ih
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega] at this
      exact this
  | @msg r1 r2 s u P ih =>
      show (XPlan.msg r1 r2 u (XPlan.app P Q)).FirstOfRun (s.length + 1 + 1 + m)
      rw [show s.length + 1 + 1 + m = (s.length + m) + 2 by omega]
      have : (XPlan.app P Q).FirstOfRun (s.length + 1 + m) := ih
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega] at this
      exact this
  | @chal r1 r2 s np P ih =>
      show (XPlan.chal r1 r2 np (XPlan.app P Q)).FirstOfRun (s.length + 1 + 1 + m)
      rw [show s.length + 1 + 1 + m = (s.length + m) + 2 by omega]
      have : (XPlan.app P Q).FirstOfRun (s.length + 1 + m) := ih
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega] at this
      exact this

theorem XPlan.firstOfRun_app_lt {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    ∀ n, n < s.length → P.FirstOfRun n → (XPlan.app P Q).FirstOfRun n := by
  induction P with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | keep r P ih =>
      rintro (_ | n) h hP
      · trivial
      · exact ih n (Nat.lt_of_succ_lt_succ h) hP
  | cut c P ih =>
      rintro (_ | n) h hP
      · trivial
      · exact ih (n + 1) h hP
  | msg r1 r2 u P ih =>
      rintro (_ | _ | n) h hP
      · exact ih 0 (Nat.succ_pos _) hP
      · exact hP.elim
      · exact ih (n + 1) (Nat.lt_of_succ_lt_succ h) hP
  | chal r1 r2 np P ih =>
      rintro (_ | _ | n) h hP
      · exact ih 0 (Nat.succ_pos _) hP
      · exact hP.elim
      · exact ih (n + 1) (Nat.lt_of_succ_lt_succ h) hP










/-! ## 3. Further data -/

def XPlan.Kits.msgFrom :
    (h : Round) → (s : Shape) → (u : h.Chal) → (ρ : Rho s) → {r : Round} → {t : Shape} →
    {Q : XPlan (Round.intoFrom h s r :: t)} → Q.Kits → (XPlan.msgFrom h s u ρ Q).Kits
  | _, [], _, _, _, _, _, K => K
  | h, b :: s, _, ρ, _, _, _, K => XPlan.Kits.msgFrom (h.joinMsg b) s ρ.1 ρ.2 K

def XPlan.Kits.msgAll :
    (s : Shape) → (ρ : Rho s) → {r : Round} → {t : Shape} → {Q : XPlan (Round.into s r :: t)} →
    Q.Kits → (XPlan.msgAll s ρ Q).Kits
  | [], _, _, _, _, K => K
  | h :: s, ρ, _, _, _, K => XPlan.Kits.msgFrom h s ρ.1 ρ.2 K



end Iop
