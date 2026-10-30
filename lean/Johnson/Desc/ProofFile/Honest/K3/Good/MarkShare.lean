-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkShare.lean: the kind "lookup" (K3): what the lookup owes
for its mark (`markK3`, `markRun`, Honest/K3/Good/Mark.lean). Conditional: a bound on the library's
own measure (`Iop.prRho`, Iop/InteractiveOracleProof.lean) of the verifier's messages of the lookup's member at which
the mark speaks: the number of events times a letter kap, under two named hypotheses on the kit of
verifier's messages. Definitions; theorems. None of the library's goals.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: a is the lookup's place and f its face. C is a kit of
verifier's messages (`Run.PQ.CK`, Run/PlanQTypes.lean); dsb is the data of the rounds of the
lookup's member; kap is a letter for a share.

What is shown.
  `shareAt`: of a round's challenges, the share that show what Q says.
  `head_le`, `round_le`: the measure of "round number |a| of a ++ d :: b shows what Q says" is at
    most that share: the bits of the test of work cancel; the other rounds do not matter.
  `any_le`: the measure of "some event of a list holds" is at most the sum.
  `markK3_le`, `markRun_le`: the bound, in the written-out form of the frame's `MarkDebt`
    (Honest/Law/CoverJoin.lean) at P := "true".
Helpers: `gchal_fib`, `gchal_card`, `FewAt`, `event_le`, `sum_const`, `events_le`.

Hypotheses that remain. Neither is shown in this file.
  `hc`: `CanAll C f dsb`: whatever the kit's messages show is such as the lookup's rounds can sample
    (`canDraw`, Honest/K3/GoodDrawsLaw.lean: the frame's own test). It can be had from the frame's
    `drawsFit_typed` (Honest/Law/Due.lean), at a kit that meets its three clauses (`kit_two`,
    Honest/Law/KitTwo.lean: the kit at the
    release's field) and at data that bear the rounds' entries and kinds; that is not called here
    (`canAll_of_kit`, Honest/K3/Good/MarkKit.lean, calls it).
  `hf`: `FewAll C f dsb kap`: for each event of the list, its round's data stand at its round's
    number in dsb, and of that round's challenges at most the share kap show the event. It can be
    had from a count at the kit, round by round.
  `h`: (in the helpers `event_le`, `events_le`) `FewAt` at the event, or at every event of the list.
    In `any_le`, without a name, in front of an arrow: each event's measure is at most its q.

Imported: Honest/Law/SharesHeld.lean and Honest/Law/Due.lean.
Follows. `gchal_fib`, `gchal_card` and `head_le` are written after
Johnson/Desc/K8/Honest/CountToRho.lean (`prRho_one_le`), here with rounds
behind the one; `any_le` after the frame's `pr_any_le` (CoverJoin.lean).

Users. `markK3_debt` and `markRun_debt` (Honest/K3/Good/MarkDebt.lean) call the two bounds. `member`
(Honest/K3/Good/MarkToy.lean) exhibits both hypotheses together at a synthetic kit.

Limits. At kap = 1 or more the clause of `hf` on the share holds of itself, and the bound says
nothing. kap is a letter: no number is evaluated. The measure is the uniform law on the member's
messages: that the messages of any run have it is not said. `markRun_le` assumes `FewAll`, on every
event of the lookup, though its proof uses the one run's events alone.
The d of `FewAll` is any datum at the event's number in dsb: that it bears the entry and the kind of
that round of the lookup is for whoever shows `FewAll` to show. At a datum that samples fewer
elements than the spot's number the event "is 0" shows at every challenge (the lacking element reads
as 0): the share is 1 and the hypothesis fails below 1; the bound cannot be had there, and is not
falsely had.
The bound for `markOut` is in Honest/K3/Good/MarkOut.lean: its last event (a factor that reads alpha
and the leaves' point) is no event on one round's sample.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Mark
import Johnson.Desc.ProofFile.Honest.Law.SharesHeld
import Johnson.Desc.ProofFile.Honest.Law.Due
import Iop.ViewKit
import Iop.GrindProofs
import Prob.Bias

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open Prob
open scoped ENNReal
open VerifiableInference.Desc (Place)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open Iop (GChal)

/-! ## 1 One round among many -/

/-- Over each challenge stand at most 2 ^ b messages. -/
theorem gchal_fib {C' : Type} [Fintype C'] (b : ℕ) (c₀ : C') :
    Prob.cnt (fun c : GChal b C' => GChal.old c = c₀) ≤ 2 ^ b := by
  have h := Nat.card_le_card_of_injective
    (fun x : {c : GChal b C' // GChal.old c = c₀} => GChal.test x.1) (fun x y hxy => by
      refine Subtype.ext ?_
      rw [← GChal.mk_old_test x.1, ← GChal.mk_old_test y.1, x.2, y.2]
      exact congrArg (GChal.mk b c₀) hxy)
  refine h.trans (le_of_eq ?_)
  rw [Nat.card_eq_fintype_card]
  simp

theorem gchal_card {C' : Type} [Fintype C'] (b : ℕ) :
    Nat.card (GChal b C') = Nat.card C' * 2 ^ b := by
  rw [Nat.card_congr (GChal.equiv b C'), Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp

/-- Of a round's challenges, the share that show what Q says. -/
noncomputable def shareAt (C : CK) (d : RDT) (Q : Fmt.Drawn → Prop) : ℝ≥0∞ :=
  ((Prob.cnt fun c : C.Ch d.entry d.kind => Q (C.dr d.entry d.kind c) : ℕ) : ℝ≥0∞) /
    (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞)

/-- **The first of several rounds.** -/
theorem head_le (C : CK) (d : RDT) (b : List RDT) (Q : Fmt.Drawn → Prop) :
    Iop.prRho {ρ : Iop.Rho (uLT C (d :: b)) | ∃ R, (drawnT C (d :: b) ρ)[0]? = some R ∧ Q R} ≤
      shareAt C d Q := by
  have hc : Prob.cnt (fun c : GChal d.entry.work (C.Ch d.entry d.kind) =>
      Q (C.dr d.entry d.kind (GChal.old c))) ≤
      Prob.cnt (fun c : C.Ch d.entry d.kind => Q (C.dr d.entry d.kind c)) * 2 ^ d.entry.work :=
    Prob.cnt_comp_le (GChal.old (b := d.entry.work)) (gchal_fib d.entry.work)
      (fun c => Q (C.dr d.entry d.kind c))
  have hh := Iop.prRho_head_le (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up (uLT C b)
    (fun c => Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))) _ hc
  have hsub : Iop.prRho {ρ : Iop.Rho (uLT C (d :: b)) |
        ∃ R, (drawnT C (d :: b) ρ)[0]? = some R ∧ Q R} ≤
      Iop.prRho (s := (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up :: uLT C b)
        {ρ | Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work)
          (show (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal × Iop.Rho (uLT C b) from ρ).1))} := by
    refine Prob.pr_mono _ fun ρ hρ => ?_
    obtain ⟨R, h1, h2⟩ := hρ
    obtain ⟨c, u⟩ := ρ
    have e : some (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)) = some R := h1
    show Q (C.dr d.entry d.kind (GChal.old (b := d.entry.work) c))
    rw [Option.some.inj e]
    exact h2
  refine hsub.trans (hh.trans (le_of_eq ?_))
  have hcard : (Fintype.card (TypedOracleCompiler.Run.PQ.roundS C d.toRD).up.Chal : ℝ≥0∞) =
      (Nat.card (C.Ch d.entry d.kind) : ℝ≥0∞) * ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← gchal_card, Nat.card_eq_fintype_card]
  unfold shareAt
  rw [hcard, Nat.cast_mul]
  have h2 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero (by positivity)).ne'
  have h3 : ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact ENNReal.mul_div_mul_right _ _ h2 h3

/-- **One round among many.** -/
theorem round_le (C : CK) (a : List RDT) (d : RDT) (b : List RDT) (Q : Fmt.Drawn → Prop) :
    Iop.prRho {ρ : Iop.Rho (uLT C (a ++ d :: b)) |
        ∃ R, (drawnT C (a ++ d :: b) ρ)[a.length]? = some R ∧ Q R} ≤ shareAt C d Q := by
  have hU : ∀ (x : Iop.Rho (uLT C a)) (y : Iop.Rho (uLT C (d :: b))),
      joinR C a (d :: b) x y ∈ {ρ : Iop.Rho (uLT C (a ++ d :: b)) |
        ∃ R, (drawnT C (a ++ d :: b) ρ)[a.length]? = some R ∧ Q R} →
      x ∉ (∅ : Set (Iop.Rho (uLT C a))) →
      y ∈ {y : Iop.Rho (uLT C (d :: b)) | ∃ R, (drawnT C (d :: b) y)[0]? = some R ∧ Q R} := by
    intro x y hxy _
    obtain ⟨R, h1, h2⟩ := hxy
    refine ⟨R, ?_, h2⟩
    rw [drawn_join, List.getElem?_append_right (le_of_eq (drawnT_len C a x)), drawnT_len,
      Nat.sub_self] at h1
    exact h1
  have h := fibre_le C a (d :: b) ∅
    (fun _ => {y : Iop.Rho (uLT C (d :: b)) | ∃ R, (drawnT C (d :: b) y)[0]? = some R ∧ Q R})
    {ρ : Iop.Rho (uLT C (a ++ d :: b)) |
      ∃ R, (drawnT C (a ++ d :: b) ρ)[a.length]? = some R ∧ Q R} 0 (shareAt C d Q)
    (Iop.prRho_empty _ fun _ hx => hx) hU (fun _ _ => head_le C d b Q)
  rwa [zero_add] at h

/-- The measure of "some event of a list holds" is at most the sum. -/
theorem any_le (C : CK) (ds : List RDT) {α : Type} (E : α → Iop.Rho (uLT C ds) → Prop)
    (q : α → ℝ≥0∞) : ∀ l : List α, (∀ x ∈ l, Iop.prRho {ρ | E x ρ} ≤ q x) →
    Iop.prRho {ρ | ∃ x ∈ l, E x ρ} ≤ (l.map q).sum
  | [], _ => le_trans (Iop.prRho_empty _ fun ρ hρ => by
      obtain ⟨x, hx, -⟩ := hρ
      cases hx) (zero_le _)
  | x :: l, h => by
    have ih := any_le C ds E q l fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, List.sum_cons]
    refine le_trans (pr_mono _ ?_) (le_trans (pr_union_le _ _ _)
      (add_le_add (h x List.mem_cons_self) ih))
    rintro ρ ⟨y, hy, hE⟩
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact Or.inl hE
    · exact Or.inr ⟨y, hy', hE⟩

/-! ## 2 The two hypotheses -/

/-- **Whatever the kit's messages show is such as the lookup's rounds can sample.** -/
def CanAll (C : CK) (f : LFace) (dsb : List RDT) : Prop :=
  ∀ ρ : Iop.Rho (uLT C dsb), canDraw f (drawnT C dsb ρ) = true

/-- **Of its round's challenges at most the share kap show the event.** -/
def FewAt (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) (e : Event) : Prop :=
  ∃ (a : List RDT) (d : RDT) (b : List RDT), dsb = a ++ d :: b ∧ a.length = e.round f ∧
    shareAt C d (fun R => e.shows R = true) ≤ kap

/-- The like for each event of the lookup. -/
def FewAll (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) : Prop :=
  ∀ e ∈ eventsOf f, FewAt C f dsb kap e

/-! ## 3 The bound -/

/-- One event. -/
theorem event_le (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) (e : Event)
    (h : FewAt C f dsb kap e) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) | e.holds f (drawnT C dsb ρ) = true} ≤ kap := by
  obtain ⟨a, d, b, rfl, hl, hs⟩ := h
  refine le_trans (pr_mono _ ?_) (le_trans (round_le C a d b fun R => e.shows R = true) hs)
  intro ρ hρ
  have hlen : a.length < (drawnT C (a ++ d :: b) ρ).length := by
    rw [drawnT_len, List.length_append, List.length_cons]
    omega
  refine ⟨(drawnT C (a ++ d :: b) ρ)[a.length], List.getElem?_eq_getElem hlen, ?_⟩
  rw [← holds_at f (drawnT C (a ++ d :: b) ρ) e (by rw [← hl]; exact List.getElem?_eq_getElem hlen)]
  exact hρ

theorem sum_const {α : Type} (l : List α) (kap : ℝ≥0∞) :
    (l.map fun _ => kap).sum = (l.length : ℝ≥0∞) * kap := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_succ, add_mul, one_mul,
      add_comm]

/-- Some event of a list of events of the lookup. -/
theorem events_le (C : CK) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞) (l : List Event)
    (h : ∀ e ∈ l, FewAt C f dsb kap e) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) | ∃ e ∈ l, e.holds f (drawnT C dsb ρ) = true} ≤
      (l.length : ℝ≥0∞) * kap := by
  rw [← sum_const]
  exact any_le C dsb (fun e ρ => e.holds f (drawnT C dsb ρ) = true) (fun _ => kap) l
    fun e he => event_le C f dsb kap e (h e he)

/-- **What the lookup owes for its mark**: at every list fr of challenges in front, the measure of
the member's messages at which the mark speaks is at most the number of events times kap. -/
theorem markK3_le (C : CK) (a : Place) (f : LFace) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewAll C f dsb kap) (fr : List Fmt.Drawn) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) |
        ((markK3 a f).test fr (drawnT C dsb ρ)).isSome = true} ≤ (events f : ℝ≥0∞) * kap := by
  rw [← eventsOf_length]
  refine le_trans (pr_mono _ ?_) (events_le C f dsb kap (eventsOf f) hf)
  intro ρ hρ
  refine event_of_bad f _ (hc ρ) ?_
  cases hg : goodK3 f (drawnT C dsb ρ) with
  | false => rfl
  | true =>
    have h0 : ((markK3 a f).test fr (drawnT C dsb ρ)).isSome = false := by
      unfold markK3
      simp [hg]
    have h1 : ((markK3 a f).test fr (drawnT C dsb ρ)).isSome = true := hρ
    rw [h0] at h1
    cases h1

/-- **The like for one run's mark.** -/
theorem markRun_le (C : CK) (a : Place) (f : LFace) (r : Run) (dsb : List RDT) (kap : ℝ≥0∞)
    (hc : CanAll C f dsb) (hf : FewAll C f dsb kap) (fr : List Fmt.Drawn) :
    Iop.prRho {ρ : Iop.Rho (uLT C dsb) |
        ((markRun a f r).test fr (drawnT C dsb ρ)).isSome = true} ≤
      (eventsRun f r : ℝ≥0∞) * kap := by
  rw [← runEvents_length]
  refine le_trans (pr_mono _ ?_)
    (events_le C f dsb kap (runEvents f r) fun e he => hf e (runEvents_sub f r he))
  intro ρ hρ
  refine event_of_badRun f r _ (hc ρ) ?_
  cases hg : goodRun f r (drawnT C dsb ρ) with
  | false => rfl
  | true =>
    have h0 : ((markRun a f r).test fr (drawnT C dsb ρ)).isSome = false := by
      unfold markRun
      simp [hg]
    have h1 : ((markRun a f r).test fr (drawnT C dsb ρ)).isSome = true := hρ
    rw [h0] at h1
    cases h1

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.gchal_fib
#print axioms ProofFile.Honest.K3.Good.gchal_card
#print axioms ProofFile.Honest.K3.Good.head_le
#print axioms ProofFile.Honest.K3.Good.round_le
#print axioms ProofFile.Honest.K3.Good.any_le
#print axioms ProofFile.Honest.K3.Good.event_le
#print axioms ProofFile.Honest.K3.Good.sum_const
#print axioms ProofFile.Honest.K3.Good.events_le
#print axioms ProofFile.Honest.K3.Good.markK3_le
#print axioms ProofFile.Honest.K3.Good.markRun_le
