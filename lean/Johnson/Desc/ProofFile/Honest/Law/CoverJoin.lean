-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean: WHO JOINS: THE FRAME. A debt (`DebtAt`,
Honest/Law/CoverSplit.lean) stands at letters that are common to a chain (the falls whole, the marks
whole, the letter Q, the numbers), and asks one bound on all that sits at a member, and Q's step. No
owner can meet that alone. Here: (1) ONE FILLING OF Q, for all: `silentQ`: every mark at a member in
front has been silent; its step is a lemma; (2) WHAT AN OWNER IS HANDED: ITS OWN SENTENCE AT ITS OWN
MARK OR FALL ALONE: `MarkDebt`, `FallDebt`; (3) THE JOINER: `debt_join`: from these, one for each
mark at the member's place and one for each fall of the list, to `DebtAt` at Q := `silentQ` and at
any number that is at least the sum; (4) a fall that does not sit at the member or at a member
without a round right behind it owes 0 there (`fallDebt_none`).

WHAT THIS IS. Definitions (premises' forms), lemmas on lists, and conditional lemmas on the
library's own measure (`Iop.prRho`). None of the library's goals.

  1  `marksQuiet`, `marksQuiet_append`, `silentQ`, `silentQ_zero`, `silentQ_step`
  2  `MarkDebt`, `FallDebt`
  3  `fallOf_mem`, `runFall_mem`, `markOf_mem`, `pr_any_le`, `debt_join`
  4  `fallDebt_none`

MET FOR NOTHING. P := False; a number of 1 or more. `debt_join`'s premise hfront (what the front's
facts give: how the walk stands, and P) is ours to pay, from `tied_at` (Honest/Law/CoverLocal.lean),
`state_in_thread`, `state_seen` (Honest/Law/CoverThread.lean; not in the sealed library) and the
silence.

Limits. THE SUM RUNS OVER ALL FALLS OF THE LIST: those that cannot be reached from the member are
paid by 0 (4), where no fixed challenge stands behind the member's own. At a member without a round:
Honest/Law/CoverNone.lean. No stated share is in these laws. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 The one filling of Q -/

/-- No mark at a member of a list has spoken: each asked at all challenges in front of its member
and at that member's own. f: the challenges in front of the list; r: the list's members' own, in a
row. -/
def marksQuiet (ms : List Mark) : List (Block S Cl) → List Fmt.Drawn → List Fmt.Drawn → Bool
  | [], _, _ => true
  | c :: cs, f, r =>
    (markOf ms c.place f (r.take c.rounds.length)).isNone &&
      marksQuiet ms cs (f ++ r.take c.rounds.length) (r.drop c.rounds.length)

theorem marksQuiet_append (ms : List Mark) : ∀ (A B : List (Block S Cl)) (f r : List Fmt.Drawn),
    marksQuiet ms (A ++ B) f r =
      (marksQuiet ms A f (r.take (A.flatMap (·.rounds)).length) &&
        marksQuiet ms B (f ++ r.take (A.flatMap (·.rounds)).length)
          (r.drop (A.flatMap (·.rounds)).length))
  | [], B, f, r => by simp [marksQuiet]
  | c :: A, B, f, r => by
    have ih := marksQuiet_append ms A B (f ++ r.take c.rounds.length) (r.drop c.rounds.length)
    have e1 : (r.take (c.rounds.length + (A.flatMap (·.rounds)).length)).take c.rounds.length =
        r.take c.rounds.length := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have e2 : (r.take (c.rounds.length + (A.flatMap (·.rounds)).length)).drop c.rounds.length =
        (r.drop c.rounds.length).take (A.flatMap (·.rounds)).length := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    have e3 : r.take (c.rounds.length + (A.flatMap (·.rounds)).length) =
        r.take c.rounds.length ++ (r.drop c.rounds.length).take
          (A.flatMap (·.rounds)).length := by
      rw [List.take_add]
    simp only [List.cons_append, marksQuiet, List.flatMap_cons, List.length_append]
    rw [ih, e1, e2, e3, Bool.and_assoc, List.append_assoc, List.drop_drop]

/-- **THE ONE FILLING OF THE LETTER Q**: at the border number j of a chain's gated members bs: every
mark at a member in front has been silent. fr: all challenges in front, those in front of the chain
(skip of them) first. -/
def silentQ (ms : List Mark) (skip : Nat) (bs : List (Block S Cl)) (j : Nat)
    (fr : List Fmt.Drawn) : Prop :=
  marksQuiet ms (bs.take j) (fr.take skip) (fr.drop skip) = true

theorem silentQ_zero (ms : List Mark) (skip : Nat) (bs : List (Block S Cl))
    (fr : List Fmt.Drawn) : silentQ ms skip bs 0 fr := rfl

/-- **It goes on past a member whose marks are silent.** -/
theorem silentQ_step (ms : List Mark) (skip : Nat) (bs : List (Block S Cl)) {j : Nat}
    {b : Block S Cl} (hj : bs[j]? = some b) (fr own : List Fmt.Drawn) (hsk : skip ≤ fr.length)
    (hn : (fr.drop skip).length = ((bs.take j).flatMap (·.rounds)).length)
    (hown : own.length = b.rounds.length) (hq : silentQ ms skip bs j fr)
    (hm : (markOf ms b.place fr own).isSome = false) : silentQ ms skip bs (j + 1) (fr ++ own) := by
  unfold silentQ at hq ⊢
  have e1 : bs.take (j + 1) = bs.take j ++ [b] := by
    rw [List.take_add_one, hj]
    rfl
  have d1 : (fr ++ own).drop skip = fr.drop skip ++ own := List.drop_append_of_le_length hsk
  have d2 : (fr ++ own).take skip = fr.take skip := List.take_append_of_le_length hsk
  rw [e1, d1, d2, marksQuiet_append, ← hn, List.take_left' rfl, List.drop_left' rfl, hq,
    List.take_append_drop]
  show (true && ((markOf ms b.place fr (own.take b.rounds.length)).isNone && true)) = true
  rw [← hown, List.take_length]
  cases h : markOf ms b.place fr own with
  | none => rfl
  | some _ =>
    rw [h] at hm
    cases hm

/-! ## 2 What an owner is handed -/

/-- **WHAT AN OWNER OWES FOR A MARK OF ITS OWN.** dsb: the data of the rounds of the member at whose
place the mark stands. P: what the owner is handed of the challenges in front: a letter. q: its
number. -/
def MarkDebt (C : CK) (mk : Mark) (dsb : List RDT) (P : List Fmt.Drawn → Prop) (q : ℝ≥0∞) : Prop :=
  ∀ fr, P fr →
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) | (mk.test fr (drawnT C dsb ρ)).isSome = true} ≤ q

/-- **WHAT AN OWNER OWES FOR A FALL OF ITS OWN: THE WIDE FORM.** b :: t: the member with a round at
whose gate the fall is held (the fall's own member, or the last one with a round in front of it),
and the members behind it. dsb: the data of b's rounds. tl: none, but behind the first chain's last
gated member the sealing round's fixed challenge. P: what the owner is handed of the challenges in
front and of the verifier's state in front of b: a letter. No walk, no prover, no coin, no input is
in it. WHERE b's ROUNDS SEND ITEMS THAT ITS STEP LAYS INTO THE STATE, AND THE FALL SITS BEHIND b,
THIS EVENT PICKS THE ITEMS AND MAY BE MET BY 1 ALONE: then the narrow form (`runFall`) is the one to
ask for. -/
def FallDebt (C : CK) (f : Fall S) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (dsb : List RDT) (tl : List Fmt.Drawn) (P : List Fmt.Drawn → S → Prop) (q : ℝ≥0∞) : Prop :=
  ∀ fr s', P fr s' →
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) | localFall [f] ft (b :: t) s' (drawnT C dsb ρ ++ tl)} ≤ q

/-! ## 3 The joiner -/

theorem fallOf_mem {fs : List (Fall S)} {a : Place} {s : S} {ds : List Fmt.Drawn}
    (h : (fallOf fs a s ds).isSome = true) : ∃ f ∈ fs, (fallOf [f] a s ds).isSome = true := by
  unfold fallOf at h
  obtain ⟨f, hf, ht⟩ := (findSome_isSome _ _).1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hf
  refine ⟨f, h1, ?_⟩
  unfold fallOf
  exact (findSome_isSome _ _).2 ⟨f, List.mem_filter.2 ⟨List.mem_cons_self, h2⟩, ht⟩

/-- **A fall of a list is a fall of one of its members alone.** -/
theorem runFall_mem {fs : List (Fall S)} {L : Lay} {ss' : List (Step W Y)} {z : ChainProgress S Cl W Y}
    {s' : S} {ext : List Fmt.Drawn} (h : runFall fs L ss' z s' ext) :
    ∃ f ∈ fs, runFall [f] L ss' z s' ext := by
  obtain ⟨z', ps, cs, h1, h2, h3, h4⟩ := h
  obtain ⟨e, he, hf⟩ := (chainFall_iff _ _ _ _ _).1 h4
  obtain ⟨f, hfs, hf'⟩ := fallOf_mem hf
  exact ⟨f, hfs, z', ps, cs, h1, h2, h3, (chainFall_iff _ _ _ _ _).2 ⟨e, he, hf'⟩⟩

theorem markOf_mem {ms : List Mark} {a : Place} {fr own : List Fmt.Drawn}
    (h : (markOf ms a fr own).isSome = true) :
    ∃ mk ∈ ms.filter (fun m => m.place == a), (mk.test fr own).isSome = true := by
  unfold markOf at h
  exact (findSome_isSome _ _).1 h

/-- **The measure of «some event of a list holds» is at most the sum.** -/
theorem pr_any_le (C : CK) (ds : List RDT) {α : Type} (E : α → Iop.Rho (uLT C ds) → Prop)
    (q : α → ℝ≥0∞) : ∀ l : List α, (∀ x ∈ l, Iop.prRho {ρ | E x ρ} ≤ q x) →
    Iop.prRho {ρ | ∃ x ∈ l, E x ρ} ≤ (l.map q).sum
  | [], _ => le_trans (Iop.prRho_empty _ fun ρ hρ => by
      obtain ⟨x, hx, -⟩ := hρ
      cases hx) (zero_le _)
  | x :: l, h => by
    have ih := pr_any_le C ds E q l fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, List.sum_cons]
    refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _)
      (add_le_add (h x List.mem_cons_self) ih))
    rintro ρ ⟨y, hy, hE⟩
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact Or.inl hE
    · exact Or.inr ⟨y, hy', hE⟩

section
variable (C : CK) (all : List (Block S Cl)) (fs : List (Fall S)) (ms : List Mark) (skip : Nat)
  (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)

/-- **THE JOINER.** bs: the chain's gated members; b: the one number j, which has a round (not a
premise); t: the members behind it. PM, P: what the owners are handed. qM, qF: their numbers.
hfront: what the front's facts give. -/
theorem debt_join (bs : List (Block S Cl)) {b : Block S Cl} {t : List (Block S Cl)} {j n : Nat}
    {dsb : List RDT} {tl : List Fmt.Drawn} {last : Bool} {ft : Nat} (hj : bs[j]? = some b)
    (hn : n = ((bs.take j).flatMap (·.rounds)).length) (hlen : dsb.length = b.rounds.length)
    (PM : List Fmt.Drawn → Prop) (P : List Fmt.Drawn → S → Prop) (qM : Mark → ℝ≥0∞)
    (qF : Fall S → ℝ≥0∞)
    (hM : ∀ mk ∈ ms.filter (fun m => m.place == b.place), MarkDebt C mk dsb PM (qM mk))
    (hF : ∀ f ∈ fs, FallDebt C f ft b t dsb tl P (qF f))
    (hPM : ∀ fr, skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → silentQ ms skip bs j fr → PM fr)
    (hfront : ∀ fr a z s', skip ≤ fr.length → (fr.drop skip).length = n →
      fellBy all fs (X (fr.take skip)) n (fr.drop skip) = false → silentQ ms skip bs j fr →
      (X (fr.take skip)).start = some a →
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z →
      z.ver = some s' →
      z.todo = b :: t ∧ z.own = [] ∧ (X (fr.take skip)).lay.firstTree = ft ∧ P fr s')
    (hp : ((ms.filter fun m => m.place == b.place).map qM).sum + (fs.map qF).sum ≤ p j) :
    DebtAt C all fs ms skip X p (silentQ ms skip bs) b j n dsb tl last := by
  intro fr h1 h2 h3 h4
  refine ⟨le_trans ?_ hp, fun _ ρ hm _ => silentQ_step ms skip bs hj fr _ h1 (by rw [h2, hn])
    (by rw [drawnT_len, hlen]) h4 hm⟩
  have bM := pr_any_le C dsb (fun (mk : Mark) ρ => (mk.test fr (drawnT C dsb ρ)).isSome = true) qM
    (ms.filter fun m => m.place == b.place) fun mk hmk => hM mk hmk fr (hPM fr h1 h2 h3 h4)
  by_cases hz : ∃ a z s', (X (fr.take skip)).start = some a ∧
      walk (X (fr.take skip)).lay ((X (fr.take skip)).steps.take n) (fr.drop skip) a = .ok z ∧
      z.ver = some s'
  · obtain ⟨a, z, s', z1, z2, z3⟩ := hz
    obtain ⟨g1, g2, g3, g4⟩ := hfront fr a z s' h1 h2 h3 h4 z1 z2 z3
    have bF := pr_any_le C dsb
      (fun (f : Fall S) ρ => localFall [f] ft (b :: t) s' (drawnT C dsb ρ ++ tl)) qF fs
      fun f hf => hF f hf fr s' g4
    refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _) (add_le_add bM bF))
    intro ρ hρ
    rcases hρ with hm | ⟨a', z', s'', y1, y2, y3, y4⟩
    · exact Or.inl (markOf_mem hm)
    · rw [z1] at y1
      cases y1
      rw [z2] at y2
      cases y2
      rw [z3] at y3
      cases y3
      obtain ⟨f, hf, hr⟩ := runFall_mem y4
      have hl := run_local hr
      rw [g1, g2, g3] at hl
      exact Or.inr ⟨f, hf, hl⟩
  · refine le_trans (le_trans (pr_mono _ ?_) bM) (le_add_right le_rfl)
    intro ρ hρ
    rcases hρ with hm | ⟨a', z', s'', y1, y2, y3, -⟩
    · exact markOf_mem hm
    · exact absurd ⟨a', z', s'', y1, y2, y3⟩ hz

end

/-! ## 4 A fall that cannot be reached from the member -/

/-- **A fall that sits neither at b nor at a member without a round right behind it owes 0 at b's
gate**, where no fixed challenge stands behind b's own. -/
theorem fallDebt_none (C : CK) (f : Fall S) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (dsb : List RDT) (hlen : dsb.length = b.rounds.length)
    (h : ∀ d ∈ groupOf b t, f.place ≠ d.place) (P : List Fmt.Drawn → S → Prop) (q : ℝ≥0∞) :
    FallDebt C f ft b t dsb [] P q := by
  intro fr s' _
  refine zero_of_not C dsb _ (fun ρ hρ => ?_) q
  obtain ⟨rs, cols, h1, h2⟩ := hρ
  have hl : rs.length = b.rounds.length := by
    have e := congrArg List.length h1
    rw [List.length_map, List.append_nil, drawnT_len, hlen] at e
    exact e
  rw [chainFall_group [f] ft b t (fun d hd g hg => by
    obtain rfl := List.mem_singleton.1 hg
    exact h d hd) s' rs cols hl] at h2
  cases h2

end ProofFile.Honest

#print axioms ProofFile.Honest.marksQuiet_append
#print axioms ProofFile.Honest.silentQ_zero
#print axioms ProofFile.Honest.silentQ_step
#print axioms ProofFile.Honest.fallOf_mem
#print axioms ProofFile.Honest.runFall_mem
#print axioms ProofFile.Honest.markOf_mem
#print axioms ProofFile.Honest.pr_any_le
#print axioms ProofFile.Honest.debt_join
#print axioms ProofFile.Honest.fallDebt_none
