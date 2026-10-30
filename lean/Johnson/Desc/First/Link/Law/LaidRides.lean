-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LaidRides.lean: «THE INDICES THAT THE SMALLNESS TEST's EQUATIONS ARE
SAID TO TAKE ARE WHAT ITS RECORD AND THE LIST OF TABLES FORETELL» (`LaidOk`), OVER A LINK's FIRST
TWO PIECES: MADE BY A YES OF THE RUN «K8.equations», KEPT BY EVERY RUN THAT LEAVES THE RECORD AND
THE LIST, BY THE SMALLNESS TEST's TWO RUNS BEHIND THE BATCHING, AND BY THE BATCHING KIND's LENS. And
the third piece's public sentence from its own yes, under that fact and «the rows owed are the
round's» (OwedRides.lean). Theorems.

What is said.
  `LaidOk s`: whatever number the record of s says is laid is `topOf` of that record and the list of
    tables. It holds outright where nothing is said to be laid. `pairOf s`: the record and the list;
    `laidOk_congr`. `pair_set`, `pair_putFork`: the lens's writing and the ledger's leave the pair.
    `k8Run_laid`: **a yes of the smallness test's run of equations makes it** (by
    `eq_laid`, Johnson/Meaning/K8Rows.lean). `k8LsTail_laid`, `k8Tests_laid`: its two runs behind
    the batching keep it. `gather_holds`, `gather_made`: along a gathering each of whose runs keeps
    a sentence it stays; if one of them makes it, it holds behind. `rows_of_yes`: **the sentence
    «the plan's claims and the ties' and reads' indices are at most the round's rows» in front of
    the one equation's piece, from that piece's yes, `owedOf = some p.rows` and `LaidOk`.**

Limits. Tools and one law. That each other run of a link's orders leaves the pair is a premise here.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OwedRides
import Johnson.Desc.First.Batch.Law.RowsRide
import Johnson.Desc.First.Batch.Law.ShutYes
import Johnson.Meaning.K8Rows
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Tie.Pv.Tail.Port (topOf)
open VerifiableInference.Desc.K9 (atS Where owedOf laidOf Window RunOf)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open _root_.Run (ckP)

/-- **Whatever number is said to be laid is what the record and the tables foretell.** -/
def LaidOk (s : S) : Prop :=
  ∀ tl funs n, s.tl? = some tl → s.funs? = some funs → laidOf tl = some n → n = topOf tl funs

/-- The smallness test's record and the list of tables. -/
def pairOf (s : S) : Option HTailF2 × Option (Array HFun) := (s.tl?, s.funs?)

theorem laidOk_congr {s s' : S} (h : pairOf s' = pairOf s) (hs : LaidOk s) : LaidOk s' := by
  intro tl funs n h1 h2
  have e1 : s'.tl? = s.tl? := congrArg Prod.fst h
  have e2 : s'.funs? = s.funs? := congrArg Prod.snd h
  exact hs tl funs n (e1 ▸ h1) (e2 ▸ h2)

/-- The ledger's writing leaves the pair. -/
theorem pair_putFork (s : S) (G : Fork) : pairOf (s.putFork G) = pairOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [pairOf, S.putFork, S.tl?, S.funs?, ho]
  | _ => rfl

/-- The link's record's writing leaves the pair. -/
theorem pair_putLink (s : S) (L : LinkCtx) : pairOf (s.putLink L) = pairOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [pairOf, S.putLink, S.tl?, S.funs?, ho]
  | _ => rfl

/-- The lens's writing leaves the pair. -/
theorem pair_set (s : S) (a : K9.Part) : pairOf (atS.set s a) = pairOf s := by
  have e : pairOf (atS.set s a) = pairOf ((s.putLink a.L).putFork a.F) := rfl
  rw [e, pair_putFork, pair_putLink]

/-- What is read behind a writing of the record, where a record is there. -/
theorem pair_putTl (s : S) (tl tl' : HTailF2) (h : s.tl? = some tl) :
    pairOf (s.putTl tl') = (some tl', s.funs?) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    by_cases ho : x.opened = true
    · simp [pairOf, S.putTl, S.tl?, S.funs?, ho]
    · simp [S.tl?, ho] at h
  | lay x => rfl
  | att x => rfl
  | _ => exact nomatch h

/-- **A yes of the smallness test's run of equations makes it.** -/
theorem k8Run_laid (front : ℕ) (e e₁ : S) (c : List Claim)
    (h : k8Run.2 front e = .ok (c, e₁)) : LaidOk e₁ := by
  obtain ⟨G, tl, funs, tl', F1, _, ht, hf, he, rfl⟩ := k8Run_ok front e e₁ c h
  intro t fs n h1 h2 hn
  have hp : pairOf ((e.putTl tl').putFork F1) = (some tl', some funs) := by
    rw [pair_putFork, pair_putTl e tl tl' ht, hf]
  obtain rfl : tl' = t := Option.some.inj ((congrArg Prod.fst hp).symm.trans h1)
  obtain rfl : funs = fs := Option.some.inj ((congrArg Prod.snd hp).symm.trans h2)
  exact (_root_.Meaning.K8.eq_laid Reading.gl (⟨fun _ => 0, fun _ _ _ => 0⟩ : World Cb.Gl.E) he hn).1

/-- The run that lays the ledger's tail keeps it. -/
theorem k8LsTail_laid (e e₁ : S) (h : k8LsTail e = .ok e₁) (hs : LaidOk e) : LaidOk e₁ := by
  obtain ⟨G, tl, _, ht, rfl⟩ := k8LsTail_ok e e₁ h
  intro t fs n h1 h2 hn
  have hp := pair_putTl e tl { tl with lsTail := G.LS.extract tl.slotA tl.slotB } ht
  obtain rfl := Option.some.inj ((congrArg Prod.fst hp).symm.trans h1)
  have h2' : e.funs? = some fs := (congrArg Prod.snd hp).symm.trans h2
  exact hs tl fs n ht h2' hn

/-- The run of the self tests keeps it. -/
theorem k8Tests_laid (nU : Array ℕ) (e e₁ : S) (h : k8Tests nU e = .ok e₁) (hs : LaidOk e) :
    LaidOk e₁ := by
  obtain ⟨G, tl, g, _, ht, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  refine laidOk_congr ?_ hs
  rw [pair_putFork, pair_putTl e tl tl ht]
  exact Prod.ext ht.symm rfl

/-- Along a gathering each of whose runs keeps a sentence it stays. -/
theorem gather_holds (Pp : S → Prop) (ws : S → List Window) (cut : List (ℕ × String)) :
    ∀ (runs : List (RunOf S)),
      (∀ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → Pp e → Pp e₁) →
      ∀ x x' : List Claim × S, runs.foldlM (gstep ws cut) x = .ok x' → Pp x.2 → Pp x'.2
  | [], _, x, x', h, hx => by
    have e : x = x' := Except.ok.inj h
    rw [← e]
    exact hx
  | r :: l, hr, x, x', h, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hz
    exact gather_holds Pp ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) _ _ h
      (hr r List.mem_cons_self _ _ _ _ hc hx)

/-- If one of the runs makes the sentence, it holds behind the gathering. -/
theorem gather_made (Pp : S → Prop) (ws : S → List Window) (cut : List (ℕ × String)) :
    ∀ (runs : List (RunOf S)),
      (∀ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → Pp e → Pp e₁) →
      (∃ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → Pp e₁) →
      ∀ x x' : List Claim × S, runs.foldlM (gstep ws cut) x = .ok x' → Pp x'.2
  | [], _, hm, _, _, _ => by
    obtain ⟨_, h, _⟩ := hm
    exact nomatch h
  | r :: l, hr, hm, x, x', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h2⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hz
    obtain ⟨r0, h0, hmk⟩ := hm
    rcases List.mem_cons.1 h0 with e0 | h1
    · rw [e0] at hmk
      exact gather_holds Pp ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
        (x.1 ++ c, e) x' h2 (hmk _ _ _ _ hc)
    · exact gather_made Pp ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
        ⟨r0, h1, hmk⟩ (x.1 ++ c, e) x' h2

variable {W Cl : Type} {F : Frame}

/-- **THE PUBLIC SENTENCE IN FRONT OF THE ONE EQUATION's PIECE, FROM ITS OWN YES AND TWO FACTS.** -/
theorem rows_of_yes (u : HTailF2) (p pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Cl W) (hpe : pe.b = below b₃) (on2 : S × F.E.Str → Prop)
    (hon2 : ∀ a, on2 a → owedOf a.1 = some p.rows ∧ LaidOk a.1) :
    ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → rowsAt p.rows u a.1 := by
  intro a τ b' ha hout tlb funs n hnum
  obtain ⟨ho, hl⟩ := hon2 a ha
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨a0, out, ha0, hdoor, _⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ hs)
  obtain ⟨m, h1, _, _, h4⟩ := _root_.Meaning.K8.door_counts hdoor
  have e1 : a.1.tl?.map (blank u) = some tlb := congrArg Prod.fst hnum
  have e2 : a.1.funs? = some funs := congrArg (fun x => x.2.1) hnum
  have e3 : a.1.fork?.map (·.planClaimsF) = some n := congrArg (fun x => x.2.2) hnum
  obtain ⟨tl, ht, rfl⟩ := Option.map_eq_some_iff.1 e1
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 e3
  obtain rfl : a0.F = G := Option.some.inj ((K9.get_fork a.1 a0 ha0).symm.trans hG)
  have hlaid : a0.laid = laidOf tl := by
    unfold atS at ha0
    simp only [Option.bind_eq_bind, Option.pure_def] at ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨tl0, ht0, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain rfl : tl0 = tl := Option.some.inj (ht0.symm.trans ht)
    rw [← Option.some.inj ha0]
  have howed : a0.owed = owedOf a.1 := by
    unfold atS at ha0
    simp only [Option.bind_eq_bind, Option.pure_def] at ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    obtain ⟨_, _, ha0⟩ := Option.bind_eq_some_iff.1 ha0
    rw [← Option.some.inj ha0]
  have em : m = topOf tl funs := hl tl funs m ht e2 (hlaid ▸ h1)
  have er : a0.F.planClaimsF + m = p.rows := Option.some.inj (h4.symm.trans (howed.trans ho))
  show a0.F.planClaimsF + top8 (blank u tl) funs ≤ p.rows
  have et : top8 (blank u tl) funs = topOf tl funs := rfl
  rw [et, ← em, er]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k8Run_laid
#print axioms VerifiableInference.Desc.LinkJoin.k8LsTail_laid
#print axioms VerifiableInference.Desc.LinkJoin.k8Tests_laid
#print axioms VerifiableInference.Desc.LinkJoin.gather_made
#print axioms VerifiableInference.Desc.LinkJoin.pair_set
#print axioms VerifiableInference.Desc.LinkJoin.rows_of_yes
