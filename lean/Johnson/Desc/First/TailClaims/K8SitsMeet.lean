-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8SitsMeet.lean: WHERE THE SMALLNESS TEST's THREE RUNS SAY YES ONE
BEHIND THE OTHER, THEIR YESES MEET: the tests behind the batching are asked at just the record that
the run of claims returned, with lsTail laid; and that is what the law K08Run (EquationsBlank.lean)
asks of a later record.

Statements and proofs.
Main names:
  part_set: behind a laying of the part, the part that is read is what was laid, with the list of
    tables as it was.
  **K08SitsMeet** (a closed Prop), **k08_sits_meet**: from the three runs' yeses at carried records
    s0, s2, s3', and TWO PREMISES ON WHAT STANDS BETWEEN THEM: (between) at s2, where "K8.lsTail"
    runs, the record has the parts of s1 but for the ledger, which is G; (kept) at s3', where
    "K8.tests" runs, it has the parts of s3 but for the ledger, which is G': equations' yes at s0's
    parts, and testsP's yes at the returned record with lsTail := G's coefficients on the test's own
    slots, and at G'.
  **K08SitsRun**, **k08_sits_run**: the same in K08Run's letters: at ts := that record: blank u ts =
    blank u tl at every u; rkSelfTestP ts Fc = .ok (); Fc has the batching element of G'.
Limits. G AND G' ARE ONLY NAMES FOR THE LEDGERS THAT THE RECORD HOLDS AT THE TWO RUNS. G IS NOT, IN
GENERAL, addAll OF THE RETURNED LEDGER AND THE CLAIMS UP TO THIS RUN's: in a layers' link and in the
head's link further runs of claims stand behind "K8.equations", and one of them writes the ledger;
both runs behind the batching stand behind the whole batching. SO K08Tests AND K08AnyTests, WHICH
BIND ONE LEDGER IN «addAll F1 (look ++ cls) = some G» AND IN «testsP … G», ARE FED BY THIS AT AN
ATTENTION LINK AT MOST. The law that fits all three sorts of link is K08Run: its ts, Fc and A0 are
free. STILL OWED FOR K08Run, AND NOT SAID HERE: that G' has the batching element of the ledger at
s0; a ledger A0 with the returned ledger's frame, batching element and plan's number, one
coefficient a slot, and addAll A0 (look ++ cls) = some G'' (another ledger again); Fits; ReadsRaw;
the rows' number; UnitRow and the places' bound. THE TWO PREMISES ARE LETTERS HERE: (between) speaks
of the other kinds' runs of claims behind ours and of the step that adds; (kept) of whatever runs
between the two runs behind the batching (in a layers' link: "free-slot"). From yeses alone.

-/
import Johnson.Desc.First.TailClaims.K8Sits
import Johnson.Desc.First.TailClaims.EquationsBlank

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

theorem funs_putTl (s : S) (tl : HTailF2) : S.funs? (s.putTl tl) = S.funs? s := by
  cases h : s.here with
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.funs?, S.putTl, h, ho]
    · simp [S.funs?, S.putTl, h, ho]
  | _ => simp [S.funs?, S.putTl, h]

theorem funs_putFork (s : S) (F : Fork) : S.funs? (s.putFork F) = S.funs? s := by
  cases h : s.here with
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.funs?, S.putFork, h, ho]
    · simp [S.funs?, S.putFork, h, ho]
  | _ => simp [S.funs?, S.putFork, h]

/-- The list of tables is read beside the record and the ledger: a laying of these two leaves it. -/
theorem funs_set (s : S) (x : HTailF2 × Fork) : S.funs? (tlForkP.set s x) = S.funs? s := by
  show S.funs? ((s.putTl x.1).putFork x.2) = S.funs? s
  rw [funs_putFork, funs_putTl]

/-- Behind a laying of the part, the part that is read is what was laid, with the list of tables as
it was. -/
theorem part_set {s : S} {q : K8Part} (h : partOf s = some q) (q' : K8Part) :
    partOf (k8PartP.set s q') = some ⟨q'.tl, q.funs, q'.F⟩ := by
  unfold partOf k8PartP at h ⊢
  simp only at h ⊢
  obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨fs, hf, rfl⟩ := Option.map_eq_some_iff.1 h2
  rw [tlForkP_lawful.get_set s (q'.tl, q'.F) x hx, funs_set, hf]
  rfl

/-- **The three yeses meet.** -/
def K08SitsMeet : Prop :=
  ∀ (p : K8.ParW) (runE : Nat → S → Except String (List Claim × S))
    (runL runT : S → Except String S),
    ("K8.equations", runE) ∈ (K8.whole p).claims → ("K8.lsTail", runL) ∈ (K8.whole p).after →
    ("K8.tests", runT) ∈ (K8.whole p).after →
    ∀ (front : Nat) (s0 s1 s2 s3 s3' s4 : S) (cls : List Claim) (G G' : Fork),
      runE front s0 = .ok (cls, s1) →
      (∀ q1, partOf s1 = some q1 → partOf s2 = some { q1 with F := G }) →
      runL s2 = .ok s3 →
      (∀ q3, partOf s3 = some q3 → partOf s3' = some { q3 with F := G' }) →
      runT s3' = .ok s4 →
      ∃ (q : K8Part) (tl' : HTailF2) (F1 Fc : Fork), partOf s0 = some q ∧
        equations (q.F.nClaim + front) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
        partOf s1 = some ⟨tl', q.funs, F1⟩ ∧
        testsP p.nU { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } G' = .ok Fc ∧
        partOf s4 = some ⟨{ tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }, q.funs, Fc⟩

theorem k08_sits_meet : K08SitsMeet := by
  intro p runE runL runT hE hL hT front s0 s1 s2 s3 s3' s4 cls G G' h1 hadd h3 hkeep h4
  obtain ⟨q, tl', F1, hq, he, rfl⟩ := (sits_equations p runE hE front s0 s1 cls).1 h1
  have p1 := part_set hq { q with tl := tl', F := F1 }
  have p2 := hadd _ p1
  obtain ⟨q2, hq2, rfl⟩ := (sits_lsTail p runL hL s2 s3).1 h3
  obtain rfl : (⟨tl', q.funs, G⟩ : K8Part) = q2 := Option.some.inj (p2.symm.trans hq2)
  have p3 := part_set hq2 { (⟨tl', q.funs, G⟩ : K8Part) with
    tl := { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } }
  have p3' := hkeep _ p3
  obtain ⟨q3, Fc, hq3, ht, rfl⟩ := (sits_tests p runT hT s3' s4).1 h4
  rw [p3'] at hq3
  obtain rfl := Option.some.inj hq3
  exact ⟨q, tl', F1, Fc, hq, he, p1, ht, part_set p3' _⟩

/-- **The same in K08Run's letters.** -/
def K08SitsRun : Prop :=
  ∀ (p : K8.ParW) (runE : Nat → S → Except String (List Claim × S))
    (runL runT : S → Except String S),
    ("K8.equations", runE) ∈ (K8.whole p).claims → ("K8.lsTail", runL) ∈ (K8.whole p).after →
    ("K8.tests", runT) ∈ (K8.whole p).after →
    ∀ (front : Nat) (s0 s1 s2 s3 s3' s4 : S) (cls : List Claim) (G G' : Fork),
      runE front s0 = .ok (cls, s1) →
      (∀ q1, partOf s1 = some q1 → partOf s2 = some { q1 with F := G }) →
      runL s2 = .ok s3 →
      (∀ q3, partOf s3 = some q3 → partOf s3' = some { q3 with F := G' }) →
      runT s3' = .ok s4 →
      ∃ (q : K8Part) (tl' ts : HTailF2) (F1 Fc : Fork), partOf s0 = some q ∧
        equations (q.F.nClaim + front) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
        (∀ u, blank u ts = blank u q.tl) ∧ rkSelfTestP ts Fc = .ok () ∧ Fc.theta = G'.theta ∧
        partOf s4 = some ⟨ts, q.funs, Fc⟩

theorem k08_sits_run : K08SitsRun := by
  intro p runE runL runT hE hL hT front s0 s1 s2 s3 s3' s4 cls G G' h1 hadd h3 hkeep h4
  obtain ⟨q, tl', F1, Fc, hq, he, -, ht, p4⟩ :=
    k08_sits_meet p runE runL runT hE hL hT front s0 s1 s2 s3 s3' s4 cls G G' h1 hadd h3 hkeep h4
  obtain ⟨-, hco, hrk⟩ := tests_ok ht
  exact ⟨q, tl', _, F1, Fc, hq, he,
    fun u => (blank_lsTail u tl' _).trans (eq_blank u he), hrk, coef_theta hco, p4⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.part_set
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_meet
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_run
