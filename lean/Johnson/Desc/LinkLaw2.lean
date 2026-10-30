-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LinkLaw2.lean: the law of a segment's batching, stated of the text that runs, and
proved from named premises. The proposition `LinkLaw` of Johnson/Desc/LinkLaw.lean speaks of no
verifier.

The setting. The protocol is written as data (Johnson/Desc/Block.lean). A segment (the record
`Link`) has blocks that hear the prover and test nothing at once: each has named runs of CLAIMS,
values that must be 0. One block, the batching, draws a challenge chi and replaces all claims of the
segment by ONE equation, each claim under a power of chi. `Link.blocksInOrder` lays a segment out as a list
of blocks: laid, the hearing blocks, the batching (handed all claims as one function,
`claimsInBy L.each`: `claimsIn` with the segment's test behind each run), a block that asks the
segment's tests behind the adding and then runs the "runs behind the batching"
(`Link.runBehind`, then `afterIn`), the closing blocks, cleared. `foldBlocks` is the verifier's fold
over such a list, on a view.

WHAT THE LAW SAYS (section 7). It is a property of a segment L, of a meaning X laid beside it
(`LinkSem`: what the claims, the one equation and the equations behind the claims are worth at
the data y to which the prover is bound) and of a number d.
  `LinkSem.Sound`: there are sets of at most d bad challenges, named by what is fixed before the
    draw and by y. Wherever the verifier's own fold over the batching block and the block behind it
    (`Link.mid`, two blocks of `Link.blocksInOrder`: `Link.flat_eq`) says yes, the stretch has drawn
    just one element; and if it is not bad at y and the one equation in the state behind holds at y,
    all equations of the segment hold at y. So: if an equation fails, then but for d challenges the
    state behind the batching holds a false equation. This is the form "bad sets and a backward
    step" from which round-by-round soundness is made.
  `LinkSem.Sound.count`, `count_draws`: the same as a count of field elements; of drawn triples.
  `LinkSem.Honest`: at a yes, if all equations of the segment hold, the one equation holds.
  `LinkSem.Answers`, `LinkSem.Worth`: companions that no law on soundness can give: the fold
    says yes somewhere at true data; it says yes somewhere at data at which an equation fails; the
    reading takes more than d values. A run can show them of a segment; here they are shown of the
    toy of section 8 alone (`meant_answers`, `meant_worth`), and no other file of this library shows
    them.
  `LinkSem.Premises.sound`, `.honest`: PROVED: the premises below give the two halves.

"Fixed before the draw" is, for the segment's whole sum, a consequence (section 4,
`LinkSem.claimsIn_fixed`) of the same thing asked run by run (`RunFixed`). The claims are made at
a state that already holds chi, and some read it. What is asked of a run is that the sum of its
claims with their weights is a polynomial in chi whose coefficients (`eqs`) see only the part of
the state that is fixed before the draw and the prover's data, under exponents (`exps`) that see
only public data. A claim's value may read what is laid into the state later, also by the runs
behind the batching: so values are read at a state that is `later` and `full`, and
`one t s y` is the value of the sums that s holds, read at t.

THE PREMISES, WHAT EACH RESTS ON, AND WHETHER IT IS PROVED.
  plan       the segment passes its own test on the plan          a run of `planOk`       not run
  square     every equation has its exponent                      the filling of X         unproved
  later      "later" is a preorder                                the filling of X         unproved
  exps       the exponents differ and are at most d               their form               unproved
             (at real sizes NOT by running `expsOkB`)
  runs       `RunFixed` for each named run of claims              the run's kind           unproved
  batch      `BatchAdds`                                          the batching kind (K9)   unproved
  after      `AfterKeeps` for each run behind the batching        the run's kind           unproved
  full       `AfterFull`: behind these runs the state is full     these kinds together     unproved
  (after and full are asked at states that meet `behind`, which the batching hands on.)
  and, outside `Premises`: that the blocks in front hand on `ready`: the hearing kinds and the
  rule of composition; `Worth`: a run; beside it `RdInj`: the field's reading.
All eight are met together by the toy of section 8, and by nothing else in this library.

THE SILLY MEMBERS (section 8), as theorems, all at one meaning, AT d = 2 IN A FIELD OF 5 ELEMENTS
(at d = 5 every segment meets `Sound`). The toy: a scalar heard before the draw is the fixed part;
one claim reads chi, so the exponents are 0 and 2; a run behind the batching lays a weight that
every claim's value reads. The segment as it is meant meets all premises, both halves and the
companions. Not one of these meets `Sound`: a batching that says yes to all; a batching that draws
nothing and says yes; an order that forgets the run of claims (`AllEq` speaks of the blocks' runs,
not of the order, so the test on the plan, `orderOk`, bears weight); a run behind the batching that
wipes the sums; a second order that forgets the run behind the batching. A batching that says no to
all meets `Sound`, as every verifier that refuses all does, and does not meet `Answers`.

LIMITS.
 (1) THIS IS THE BATCHING OF A SEGMENT, NOT THE WHOLE SEGMENT. The hearing blocks in front and the
     closing behind have lemmas of their own. That the whole segment is sound follows from these,
     this piece and a rule of composition for a row of blocks; that is NOT shown here. Nothing is
     said here of a block that draws a point at which other blocks' identities are tested ("host and
     guests").
 (2) X IS LETTERS. A hollow filling gives a hollow law: a one equation that never holds; equations
     that fail only at states from which the fold never says yes; a reading of few values; d not
     below the field's size. `Worth` guards the first three.
 (3) THE COUNT IS OF FIELD ELEMENTS (or of triples of words) THAT A VIEW SHOWS AS DRAWN, not of the
     raw challenges of the written rounds. Johnson/Desc/LinkLaw3.lean carries it there.
 (4) HERE `claimsIn` IS RUN IN TOYS ALONE (section 8). The verifier's own runs of claims, at the
     head's link (`order_head`, Johnson/Desc/First/Link/Law/LinkJoinPay.lean), are not spoken of in
     this file.
 (5) y is one letter for all that the prover is bound to before the draw. That it is bound (a
     function of the oracle messages sent) is asked where the law is used.
 (6) Nothing on an honest prover, on masks or on hiding.
 (7) `RunFixed` ASKS THAT A RUN LEAVES THE FIXED PART AS IT IS (`X.fixed s' = X.fixed s`). Runs of
     the protocol lay things into the ledger behind the draw: hiding coefficients under slots that
     were free till then, marks on claims that were owed. So a meaning whose fixed part reads the
     whole ledger CANNOT MEET THIS CLAUSE at such a run: the fixed part must leave out what the runs
     lay, and still name the terms. Whether there is such a meaning at the protocol's runs is not
     shown. All premises start from a yes at one state: nothing is asked at a challenge at which a
     run refuses.

It imports, beside the format's file: Johnson/Top/H0/Walk/LinkLawProofs.lean
(`everyRunOnce`, `claimsAreTheRuns`) and Johnson/Desc/Sound/FoldLaw.lean (`Block.step_eq`,
`foldBlocks_ok`, `foldBlocks_error`, `foldBlocks_short`).

-/
import Johnson.Top.H0.Walk.LinkLawProofs
import Johnson.Desc.BlockLaws
import Johnson.Desc.Sound.FoldLaw
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-! ## 1 The root count (an auxiliary lemma; not the law) -/

section RootCount
open Polynomial
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- A list of terms (exponent, coefficient) as a polynomial. -/
noncomputable def termsPoly (t : List (ℕ × K)) : K[X] := (t.map fun x => monomial x.1 x.2).sum

omit [Fintype K] [DecidableEq K] in
theorem termsPoly_cons (a : ℕ × K) (t : List (ℕ × K)) :
    termsPoly K (a :: t) = monomial a.1 a.2 + termsPoly K t := by
  simp [termsPoly]

omit [Fintype K] [DecidableEq K] in
theorem termsAt_cons (a : ℕ × K) (t : List (ℕ × K)) (chi : K) :
    termsAt K (a :: t) chi = chi ^ a.1 * a.2 + termsAt K t chi := by
  simp [termsAt]

omit [Fintype K] [DecidableEq K] in
theorem termsAt_append (t u : List (ℕ × K)) (chi : K) :
    termsAt K (t ++ u) chi = termsAt K t chi + termsAt K u chi := by
  simp [termsAt]

omit [Fintype K] [DecidableEq K] in
theorem termsPoly_eval (t : List (ℕ × K)) (chi : K) :
    (termsPoly K t).eval chi = termsAt K t chi := by
  induction t with
  | nil => simp [termsPoly, termsAt]
  | cons a t ih => rw [termsPoly_cons, termsAt_cons, eval_add, eval_monomial, ih, mul_comm]

omit [Fintype K] [DecidableEq K] in
theorem termsPoly_coeff_of_not_mem (t : List (ℕ × K)) (e : ℕ) (h : e ∉ t.map (·.1)) :
    (termsPoly K t).coeff e = 0 := by
  induction t with
  | nil => simp [termsPoly]
  | cons a t ih =>
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [termsPoly_cons, coeff_add, coeff_monomial, if_neg (fun q => h.1 q.symm), ih h.2, add_zero]

omit [Fintype K] [DecidableEq K] in
theorem termsPoly_coeff (t : List (ℕ × K)) (h : (t.map (·.1)).Nodup) (x : ℕ × K) (hx : x ∈ t) :
    (termsPoly K t).coeff x.1 = x.2 := by
  induction t with
  | nil => cases hx
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [termsPoly_cons, coeff_add, coeff_monomial]
    rcases List.mem_cons.1 hx with rfl | hx'
    · rw [if_pos rfl, termsPoly_coeff_of_not_mem K t _ h.1, add_zero]
    · have hne : a.1 ≠ x.1 := fun q => h.1 (q ▸ List.mem_map_of_mem hx')
      rw [if_neg hne, zero_add, ih h.2 hx']

omit [Fintype K] [DecidableEq K] in
theorem termsPoly_natDegree_le (t : List (ℕ × K)) (d : ℕ) (h : ∀ x ∈ t, x.1 ≤ d) :
    (termsPoly K t).natDegree ≤ d := by
  induction t with
  | nil => simp [termsPoly]
  | cons a t ih =>
    rw [termsPoly_cons]
    exact natDegree_add_le_of_degree_le
      ((natDegree_monomial_le a.2).trans (h a (List.mem_cons_self ..)))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **The root count.** A sum of terms chi ^ e * c whose exponents differ from each other and are at
most d, and one of whose coefficients is not 0, vanishes at no more than d values of chi. -/
theorem termsAt_roots_le (t : List (ℕ × K)) (d : ℕ) (h : TermsOk K t d) (hx : ∃ x ∈ t, x.2 ≠ 0) :
    (Finset.univ.filter fun chi : K => termsAt K t chi = 0).card ≤ d := by
  obtain ⟨x, hx, hne⟩ := hx
  have hP : termsPoly K t ≠ 0 := fun h0 =>
    hne (by rw [← termsPoly_coeff K t h.1 x hx, h0, coeff_zero])
  calc (Finset.univ.filter fun chi : K => termsAt K t chi = 0).card
      ≤ (termsPoly K t).roots.toFinset.card := Finset.card_le_card fun chi hchi => by
        rw [Finset.mem_filter] at hchi
        rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, termsPoly_eval]
        exact hchi.2
    _ ≤ Multiset.card (termsPoly K t).roots := Multiset.toFinset_card_le _
    _ ≤ (termsPoly K t).natDegree := card_roots' _
    _ ≤ d := termsPoly_natDegree_le K t d h.2

end RootCount

/-! ## 2 The runs of claims that a segment's order names -/

section Fold
variable {S Cl : Type}

/-- The run that an entry of a segment's order names, if it is there. -/
def runOf (bs : List (Block S Cl)) (o : ℕ × String) :
    Option (ℕ → S → Except String (List Cl × S)) :=
  (bs[o.1]?).bind fun b => b.claims.lookup o.2

theorem toOption_eq_some {α : Type} {x : Except String α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

/-- One entry of the order, where the runs one by one return. -/
theorem runsOneByOne_cons {bs : List (Block S Cl)} {o : ℕ × String} {os : List (ℕ × String)}
    {k : ℕ} {s s' : S} {ls : List (List Cl)}
    (h : runsOneByOne bs (o :: os) k s = some (ls, s')) :
    ∃ run y zs, runOf bs o = some run ∧ run k s = .ok y ∧
      runsOneByOne bs os (k + y.1.length) y.2 = some (zs, s') ∧ ls = y.1 :: zs := by
  simp only [runsOneByOne, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨run, ⟨b, hb, hlk⟩, y, hy, z, hz, rfl, rfl⟩ := h
  refine ⟨run, y, z.1, ?_, toOption_eq_some hy, hz, rfl⟩
  unfold runOf
  rw [hb]
  exact hlk

/-- What the batching block is handed, as the runs one by one (by `claimsAreTheRuns`). -/
theorem runs_of_claimsIn {bs : List (Block S Cl)} {order : List (ℕ × String)} {s s' : S}
    {cls : List Cl} (h : claimsIn bs order s = .ok (cls, s')) :
    ∃ ls, runsOneByOne bs order 0 s = some (ls, s') ∧ cls = ls.flatten := by
  have h1 := claimsAreTheRuns S Cl bs order s
  rw [h] at h1
  obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.1 h1.symm
  simp only [Prod.mk.injEq] at hxe
  exact ⟨x.1, by rw [hx, ← hxe.2], hxe.1.symm⟩

theorem mem_order_iff {bs : List (Block S Cl)} {order : List (ℕ × String)}
    (h : orderOk bs order = true) (o : ℕ × String) : o ∈ order ↔ o ∈ allRuns bs :=
  (everyRunOnce S Cl bs order h).1.mem_iff

end Fold

/-! ## 3 What a segment's batching means: the letters of the law -/

section Law
variable {S Cl P Y : Type} (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- **The meaning that is laid beside a segment's text.** Nothing here is code of the verifier. S:
the state that the verifier carries. Cl: the type of a claim. P: the part of the state that is fixed
before the batching challenge is drawn. Y: the data to which the prover is bound before that draw
(what stands behind the oracle messages sent so far). K: the field. A run of claims is named as the
segment's order names it: (the block's number, the run's name). -/
structure LinkSem (S Cl P Y : Type) where
  /-- a drawn element, as a view shows it (three words), as an element of the field -/
  rd : Fmt.Ext → K
  /-- what of the state is fixed before the draw -/
  fixed : S → P
  /-- the challenge, as a state behind the draw holds it -/
  chi : S → K
  /-- the condition on the state in front of the batching block -/
  ready : S → Prop
  /-- the condition on a state behind the draw (for one: all its words are below the prime) -/
  good : S → Prop
  /-- the condition on a state behind the adding of the claims: it holds along the runs behind the
  batching -/
  behind : S → Prop
  /-- "t is s, or comes behind s, among the states behind the draw": what a claim speaks of may be
  laid into the state by a run of claims (a scalar's shown value and factor); it then stays -/
  later : S → S → Prop
  /-- "all that a claim's value reads of the state has been laid": some of it is laid only by the
  runs behind the batching (the weights of a virtual row) -/
  full : S → Prop
  /-- the value of the claim cl as claim number j of the segment, WITH its weight: read at the state
  t, at the data y and the challenge c -/
  wv : S → Y → K → ℕ → Cl → K
  /-- `one t s y`: the value at the data y of the left-hand side of the segment's one equation as
  the state s holds it, what it speaks of read at the state t. The equation in a state s behind the
  batching and the runs behind it says `one s s y = 0` -/
  one : S → S → Y → K
  /-- how many claims a run makes -/
  cnt : ℕ × String → P → ℕ
  /-- THE EQUATIONS BEHIND A RUN's CLAIMS: their left-hand sides' values. They see neither the
  challenge nor the number of claims made before -/
  eqs : ℕ × String → P → Y → List K
  /-- the exponent of the challenge under which each of these equations stands, if n claims were
  made before the run. They do not see the prover's data -/
  exps : ℕ × String → ℕ → P → List ℕ

variable {K}
variable (X : LinkSem K S Cl P Y)

/-- The claims of a list, as the claims number n, n + 1, … of the segment: the sum of their values
with their weights. -/
def LinkSem.wsum (t : S) (y : Y) (c : K) : ℕ → List Cl → K
  | _, [] => 0
  | n, cl :: l => X.wv t y c n cl + LinkSem.wsum t y c (n + 1) l

/-- A run's terms: each equation with its exponent. -/
def LinkSem.terms (o : ℕ × String) (n : ℕ) (p : P) (y : Y) : List (ℕ × K) :=
  (X.exps o n p).zip (X.eqs o p y)

/-- The terms of the runs of an order, if n claims were made before. -/
def LinkSem.termsFrom (p : P) (y : Y) : List (ℕ × String) → ℕ → List (ℕ × K)
  | [], _ => []
  | o :: os, n => X.terms o n p y ++ LinkSem.termsFrom p y os (n + X.cnt o p)

/-- Their exponents. -/
def LinkSem.expsFrom (p : P) : List (ℕ × String) → ℕ → List ℕ
  | [], _ => []
  | o :: os, n => X.exps o n p ++ LinkSem.expsFrom p os (n + X.cnt o p)

/-- Every equation has its exponent: the two lists are equally long. -/
def LinkSem.Square : Prop := ∀ o n p y, (X.exps o n p).length = (X.eqs o p y).length

/-- A TEST ON PUBLIC DATA: along the order, the exponents differ from each other and are at most d.
-/
def LinkSem.ExpsOk (order : List (ℕ × String)) (p : P) (d : ℕ) : Prop :=
  (X.expsFrom p order 0).Nodup ∧ ∀ e ∈ X.expsFrom p order 0, e ≤ d

/-- The same test with code; no file of this library runs it. -/
def LinkSem.expsOkB (order : List (ℕ × String)) (p : P) (d : ℕ) : Bool :=
  decide (X.expsFrom p order 0).Nodup && (X.expsFrom p order 0).all (· ≤ d)

omit [Field K] [Fintype K] [DecidableEq K] in
theorem LinkSem.expsOkB_iff (order : List (ℕ × String)) (p : P) (d : ℕ) :
    X.expsOkB order p d = true ↔ X.ExpsOk order p d := by
  simp [LinkSem.expsOkB, LinkSem.ExpsOk]

/-- **FIXED BEFORE THE DRAW, as a premise on one run of claims.** At every good state behind the
draw at which the run returns: the state that it hands on is good, is later, and has the same fixed
part and the same challenge; it makes as many claims as `cnt` says; and the sum of its claims'
values with their weights, READ AT ANY FULL STATE LATER THAN THE ONE THAT IT HANDS ON, is the
polynomial in the challenge whose coefficients are the run's equations, which see the fixed part and
the prover's data alone. -/
def LinkSem.RunFixed (o : ℕ × String) (run : ℕ → S → Except String (List Cl × S)) : Prop :=
  ∀ n s cls s', X.good s → run n s = .ok (cls, s') →
    X.good s' ∧ X.later s s' ∧ X.fixed s' = X.fixed s ∧ X.chi s' = X.chi s ∧
      cls.length = X.cnt o (X.fixed s) ∧
      ∀ t y, X.later s' t → X.full t →
        X.wsum t y (X.chi s) n cls = termsAt K (X.terms o n (X.fixed s) y) (X.chi s)

/-- The like of every named run of a list of blocks. -/
def LinkSem.RunsFixed (bs : List (Block S Cl)) : Prop :=
  ∀ o run, runOf bs o = some run → X.RunFixed o run

/-- **What is asked of the batching block** b, which was handed the function f of claims. Where its
step says yes, at a ready state and a stretch whose words are below the prime: its rounds have drawn
just one element x; f was run, and has returned, at a good state that has the fixed part of the
state in front and holds x as the challenge; and, IF THE STATE THAT f HAS RETURNED IS GOOD AND STILL
HOLDS x (the runs' duty, not the batching's: `RunFixed`), the state behind meets `behind` and is
later than it, and the one equation's left-hand side in the state behind is the sum of the returned
claims' values with their weights, numbered from 0, both read at any later state. -/
def LinkSem.BatchAdds (ft : ℕ) (b : Block S Cl) (f : S → Except String (List Cl × S)) : Prop :=
  ∀ s rs cols s' k, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true → b.step ft s rs cols = .ok (s', k) →
    ∃ x s₁ cls s₂, rs.flatMap (·.drawn.elems) = [x] ∧ X.good s₁ ∧ X.fixed s₁ = X.fixed s ∧
      X.chi s₁ = X.rd x ∧ f s₁ = .ok (cls, s₂) ∧
      (X.good s₂ → X.chi s₂ = X.rd x → X.behind s' ∧ X.later s₂ s' ∧
        ∀ t y, X.later s' t → X.one t s' y = X.wsum t y (X.rd x) 0 cls)

/-- **All equations of the segment hold** at the data y: every equation behind every named run of
claims of every block of the list. IT IS SAID OF THE BLOCKS' RUNS, NOT OF THE ORDER: an order that
forgets a run does not shorten it. -/
def LinkSem.AllEq (bs : List (Block S Cl)) (p : P) (y : Y) : Prop :=
  ∀ o ∈ allRuns bs, ∀ c ∈ X.eqs o p y, c = 0

open Classical in
/-- **The bad challenges** at a fixed part and the prover's data: none if all coefficients are 0;
else the roots of the polynomial. They are named before the draw. -/
noncomputable def LinkSem.bad (order : List (ℕ × String)) (p : P) (y : Y) : Finset K :=
  if ∃ x ∈ X.termsFrom p y order 0, x.2 ≠ 0 then
    Finset.univ.filter fun c => termsAt K (X.termsFrom p y order 0) c = 0
  else ∅

/-! ## 4 Fixed before the draw: from the runs to the segment -/

omit [Fintype K] [DecidableEq K] in
theorem LinkSem.wsum_append (t : S) (y : Y) (c : K) (a b : List Cl) (n : ℕ) :
    X.wsum t y c n (a ++ b) = X.wsum t y c n a + X.wsum t y c (n + a.length) b := by
  induction a generalizing n with
  | nil => simp [LinkSem.wsum]
  | cons x a ih =>
    simp only [List.cons_append, LinkSem.wsum, ih, List.length_cons]
    rw [show n + 1 + a.length = n + (a.length + 1) by omega, add_assoc]

/-- `later` is a preorder. -/
def LinkSem.LaterOk : Prop :=
  (∀ s, X.later s s) ∧ ∀ s t u, X.later s t → X.later t u → X.later s u

omit [Fintype K] [DecidableEq K] in
/-- **The sum that the batching forms is a polynomial in the challenge whose coefficients were fixed
before the draw**: a consequence of `RunsFixed`, along the runs in the segment's order. -/
theorem LinkSem.runs_fixed {bs : List (Block S Cl)} (hl : X.LaterOk) (hruns : X.RunsFixed bs) :
    ∀ (order : List (ℕ × String)) (n : ℕ) (s : S) (ls : List (List Cl)) (s' : S), X.good s →
      runsOneByOne bs order n s = some (ls, s') →
      X.good s' ∧ X.later s s' ∧ X.fixed s' = X.fixed s ∧ X.chi s' = X.chi s ∧
        ∀ t y, X.later s' t → X.full t → X.wsum t y (X.chi s) n ls.flatten =
          termsAt K (X.termsFrom (X.fixed s) y order n) (X.chi s) := by
  intro order
  induction order with
  | nil =>
    intro n s ls s' hg h
    simp only [runsOneByOne, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, hl.1 s, rfl, rfl, fun t y _ _ => by
      simp [LinkSem.wsum, LinkSem.termsFrom, termsAt]⟩
  | cons o os ih =>
    intro n s ls s' hg h
    obtain ⟨run, y₁, zs, hrun, hy, hz, rfl⟩ := runsOneByOne_cons h
    obtain ⟨hg₁, hl₁, hf₁, hc₁, hlen, hsum⟩ := hruns o run hrun n s y₁.1 y₁.2 hg hy
    obtain ⟨hg', hl', hf', hc', hnew⟩ := ih (n + y₁.1.length) y₁.2 zs s' hg₁ hz
    refine ⟨hg', hl.2 _ _ _ hl₁ hl', hf'.trans hf₁, hc'.trans hc₁, fun t y ht hfull => ?_⟩
    have h2 := hnew t y ht hfull
    rw [hlen, hf₁, hc₁] at h2
    rw [List.flatten_cons, X.wsum_append, hsum t y (hl.2 _ _ _ hl' ht) hfull, hlen, h2,
      LinkSem.termsFrom, termsAt_append]

omit [Fintype K] [DecidableEq K] in
theorem LinkSem.claimsIn_fixed {bs : List (Block S Cl)} (hl : X.LaterOk) (hruns : X.RunsFixed bs)
    (order : List (ℕ × String)) (s : S) (cls : List Cl) (s' : S) (hg : X.good s)
    (h : claimsIn bs order s = .ok (cls, s')) :
    X.good s' ∧ X.chi s' = X.chi s ∧ ∀ t y, X.later s' t → X.full t →
      X.wsum t y (X.chi s) 0 cls = termsAt K (X.termsFrom (X.fixed s) y order 0) (X.chi s) := by
  obtain ⟨ls, hls, rfl⟩ := runs_of_claimsIn h
  obtain ⟨hg', _, _, hc', hsum⟩ := X.runs_fixed hl hruns order 0 s ls s' hg hls
  exact ⟨hg', hc', hsum⟩

/-! ## 5 The terms of the order against the equations of the blocks -/

omit [Field K] [Fintype K] [DecidableEq K] in
theorem LinkSem.map_fst_termsFrom (hsq : X.Square) (p : P) (y : Y) :
    ∀ (order : List (ℕ × String)) (n : ℕ),
      (X.termsFrom p y order n).map (·.1) = X.expsFrom p order n
  | [], _ => rfl
  | o :: os, n => by
    rw [LinkSem.termsFrom, LinkSem.expsFrom, List.map_append, LinkSem.map_fst_termsFrom hsq p y os,
      LinkSem.terms, List.map_fst_zip (le_of_eq (hsq o n p y))]

omit [Field K] [Fintype K] [DecidableEq K] in
theorem LinkSem.termsOk (hsq : X.Square) {order : List (ℕ × String)} {p : P} {d : ℕ}
    (h : X.ExpsOk order p d) (y : Y) : TermsOk K (X.termsFrom p y order 0) d := by
  refine ⟨by rw [X.map_fst_termsFrom hsq]; exact h.1, fun x hx => h.2 x.1 ?_⟩
  rw [← X.map_fst_termsFrom hsq p y]
  exact List.mem_map_of_mem hx

omit [Field K] [Fintype K] [DecidableEq K] in
/-- An equation of a run that the order names is the coefficient of a term. -/
theorem LinkSem.term_of_eq (hsq : X.Square) (p : P) (y : Y) {o : ℕ × String} {c : K}
    (hc : c ∈ X.eqs o p y) :
    ∀ (order : List (ℕ × String)) (n : ℕ), o ∈ order → ∃ x ∈ X.termsFrom p y order n, x.2 = c
  | [], _, h => by cases h
  | o' :: os, n, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have hi' : i < (X.exps o n p).length := by rw [hsq o n p y]; exact hi
      refine ⟨((X.exps o n p)[i], (X.eqs o p y)[i]), ?_, rfl⟩
      rw [LinkSem.termsFrom]
      refine List.mem_append_left _ ?_
      have hz : i < ((X.exps o n p).zip (X.eqs o p y)).length := by
        rw [List.length_zip]; exact lt_min hi' hi
      have := List.getElem_mem hz
      rwa [List.getElem_zip] at this
    · obtain ⟨x, hx, hxc⟩ := LinkSem.term_of_eq hsq p y hc os (n + X.cnt o' p) h'
      exact ⟨x, by rw [LinkSem.termsFrom]; exact List.mem_append_right _ hx, hxc⟩

omit [Field K] [Fintype K] [DecidableEq K] in
/-- The coefficient of a term is an equation of a run that the order names. -/
theorem LinkSem.eq_of_term (p : P) (y : Y) :
    ∀ (order : List (ℕ × String)) (n : ℕ), ∀ x ∈ X.termsFrom p y order n,
      ∃ o ∈ order, x.2 ∈ X.eqs o p y
  | [], _, x, h => by cases h
  | o :: os, n, x, h => by
    rw [LinkSem.termsFrom] at h
    rcases List.mem_append.1 h with h | h
    · exact ⟨o, List.mem_cons_self .., (List.of_mem_zip h).2⟩
    · obtain ⟨o', ho', hx⟩ := LinkSem.eq_of_term p y os _ x h
      exact ⟨o', List.mem_cons_of_mem _ ho', hx⟩

theorem LinkSem.bad_card_le (hsq : X.Square) {order : List (ℕ × String)} {p : P} {d : ℕ}
    (h : X.ExpsOk order p d) (y : Y) : (X.bad order p y).card ≤ d := by
  unfold LinkSem.bad
  split
  · next hx => exact termsAt_roots_le K _ d (X.termsOk hsq h y) hx
  · simp

end Law

/-! ## 6 The runs behind the batching -/

section After
variable {S Cl : Type}

/-- One step of `afterIn`'s fold. -/
def stepA (bs : List (Block S Cl)) (acc : Except String S) (o : ℕ × String) : Except String S :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)

theorem afterIn_eq (bs : List (Block S Cl)) (order : List (ℕ × String)) (s : S) :
    afterIn bs order s = order.foldl (stepA bs) (.ok s) := rfl

theorem foldA_error (bs : List (Block S Cl)) (order : List (ℕ × String)) (e : String) :
    order.foldl (stepA bs) (.error e) = .error e := by
  induction order with
  | nil => rfl
  | cons o os ih => exact ih

/-- The run behind the batching that an entry of a segment's second order names. -/
def afterOf (bs : List (Block S Cl)) (o : ℕ × String) : Option (S → Except String S) :=
  (bs[o.1]?).bind fun b => b.after.lookup o.2

theorem stepA_ok {bs : List (Block S Cl)} {x z : S} {o : ℕ × String}
    (h : stepA bs (.ok x) o = .ok z) : ∃ run, afterOf bs o = some run ∧ run x = .ok z := by
  unfold stepA at h
  simp only [Except.bind] at h
  unfold afterOf
  cases hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) with
  | none => simp [hl, named] at h
  | some run =>
    simp only [hl, named] at h
    cases hr : run x with
    | error e => simp [hr] at h
    | ok y =>
      simp only [hr, Except.ok.injEq] at h
      exact ⟨run, rfl, by rw [hr, h]⟩

end After

/-! ## 7 The law -/

section TheLaw
variable {S Cl P Y K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The first block of a segment's flat list: it holds the segment's own test on the plan. -/
def Link.laidB (L : Link S Cl) : Block S Cl :=
  { roundlessBlock (L.name ++ ": laid") L.chain (some L.number) 0 L.lay with
      planOk := orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
        L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter }

/-- The batching block, as the flat list holds it: handed the segment's claims, with the segment's
test behind each run. -/
def Link.batchB (L : Link S Cl) : Block S Cl := L.batch (claimsInBy L.each L.hear L.order)

/-- The block of the flat list that asks the segment's tests behind the adding and then runs the
runs behind the batching. -/
def Link.behindB (L : Link S Cl) : Block S Cl :=
  roundlessBlock (L.name ++ ": behind the batching") L.chain (some L.number) (L.hear.length + 2)
    L.runBehind

/-- Where that block's function says yes, the runs behind the batching have said yes, with the same
state. -/
theorem Link.afterIn_of_runBehind {L : Link S Cl} {s s' : S} (h : L.runBehind s = .ok s') :
    afterIn L.hear L.orderAfter s = .ok s' := by
  unfold Link.runBehind at h
  split at h
  · exact h
  · cases h

/-- The last block of the flat list. -/
def Link.clearedB (L : Link S Cl) : Block S Cl :=
  roundlessBlock (L.name ++ ": cleared") L.chain (some L.number) (L.hear.length + L.close.length + 3)
    L.clear

/-- The two blocks of which the law speaks. -/
def Link.mid (L : Link S Cl) : List (Block S Cl) := [L.batchB, L.behindB]

/-- They are blocks of the flat list that runs, at their place in it. -/
theorem Link.flat_eq (L : Link S Cl) :
    L.blocksInOrder = L.laidB :: L.hear ++ L.mid ++ L.close ++ [L.clearedB] := rfl

variable (X : LinkSem K S Cl P Y)

/-- What is asked of each run behind the batching, at a state that meets `behind`: the state that
it hands on meets it too, is later, and holds the same one equation: read at any later state, the
left-hand side has the same value. (Such a run may lay what the equation speaks of; it does not turn
the sums.) -/
def LinkSem.AfterKeeps (bs : List (Block S Cl)) : Prop :=
  ∀ o run, afterOf bs o = some run → ∀ s s', X.behind s → run s = .ok s' →
    X.behind s' ∧ X.later s s' ∧ ∀ t y, X.later s' t → X.one t s' y = X.one t s y

/-- What is asked of the runs behind the batching together: from a state that meets `behind` they
lead to a full state. -/
def LinkSem.AfterFull (L : Link S Cl) : Prop :=
  ∀ s s', X.behind s → afterIn L.hear L.orderAfter s = .ok s' → X.full s'

/-- **THE LAW OF A SEGMENT's BATCHING, the half on soundness**, as a property of a segment L, of the
meaning X that is laid beside it, and of a number d. There are sets of bad challenges, named by what
is fixed before the draw and by the prover's data, each of at most d elements. And wherever the
verifier's own fold over the batching block and the runs behind it says yes on a stretch (from a
ready state; all words below the prime; no round left over): the stretch has drawn just one element;
and at every data y at which that element is not bad: IF THE ONE EQUATION IN THE STATE BEHIND HOLDS,
ALL THE SEGMENT's EQUATIONS HOLD. Read backwards: if one equation of the segment fails at the data
to which the prover is bound, then but for at most d challenges the state behind the batching holds
a false equation. -/
def LinkSem.Sound (L : Link S Cl) (ft d : ℕ) : Prop :=
  ∃ bad : P → Y → Finset K, (∀ s y, X.ready s → (bad (X.fixed s) y).card ≤ d) ∧
    ∀ s rs cols s' cols', X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
      foldBlocks ft L.mid s rs cols = .ok (s', [], cols') →
      ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧
        ∀ y, X.rd x ∉ bad (X.fixed s) y → X.one s' s' y = 0 → X.AllEq L.hear (X.fixed s) y

/-- **The half on true data**: where the fold says yes and all the segment's equations hold, the one
equation holds, at every challenge. -/
def LinkSem.Honest (L : Link S Cl) (ft : ℕ) : Prop :=
  ∀ s rs cols s' cols' y, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
    foldBlocks ft L.mid s rs cols = .ok (s', [], cols') →
    X.AllEq L.hear (X.fixed s) y → X.one s' s' y = 0

/-- **The companion**, which no law on soundness can give: the fold does say yes somewhere, at data
at which all the segment's equations hold. It is shown of a segment by a run; in this library of the
toy of section 8 alone (`meant_answers`). -/
def LinkSem.Answers (L : Link S Cl) (ft : ℕ) : Prop :=
  ∃ s rs cols s' cols' y, X.ready s ∧ viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
    foldBlocks ft L.mid s rs cols = .ok (s', [], cols') ∧ X.AllEq L.hear (X.fixed s) y

omit [Field K] [Fintype K] [DecidableEq K] in
theorem LinkSem.afterIn_keeps {bs : List (Block S Cl)} (hl : X.LaterOk) (h : X.AfterKeeps bs) :
    ∀ (order : List (ℕ × String)) (s s' : S), X.behind s → afterIn bs order s = .ok s' →
      X.behind s' ∧ X.later s s' ∧ ∀ t y, X.later s' t → X.one t s' y = X.one t s y := by
  intro order
  induction order with
  | nil =>
    intro s s' hb hs
    have : s = s' := by simpa [afterIn] using hs
    subst this
    exact ⟨hb, hl.1 s, fun _ _ _ => rfl⟩
  | cons o os ih =>
    intro s s' hb hs
    rw [afterIn_eq, List.foldl_cons] at hs
    cases hz : stepA bs (.ok s) o with
    | error e => rw [hz, foldA_error] at hs; cases hs
    | ok z =>
      rw [hz] at hs
      obtain ⟨run, hrun, hr⟩ := stepA_ok hz
      obtain ⟨hb₁, hl₁, hk₁⟩ := h o run hrun s z hb hr
      obtain ⟨hb₂, hl₂, hk₂⟩ := ih z s' hb₁ hs
      exact ⟨hb₂, hl.2 _ _ _ hl₁ hl₂, fun t y ht =>
        (hk₂ t y ht).trans (hk₁ t y (hl.2 _ _ _ hl₂ ht))⟩

/-- A block without a round, as a step. -/
theorem quiet_step (name : String) (c : ℕ) (l : Option ℕ) (p : ℕ) (f : S → Except String S)
    (ft : ℕ) (s : S) (cols : List OpenedColumn) :
    (roundlessBlock name c l p f : Block S Cl).step ft s [] cols = (f s).map fun s' => (s', 0) := by
  rw [Block.step_eq]
  cases h : f s <;> simp [roundlessBlock, roundsFit, groupsOf, regroup, h, Except.map, bind,
    Except.bind, pure, Except.pure]

/-- One block of the fold, where the fold returns. -/
theorem foldBlocks_cons_yes {ft : ℕ} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (b :: l) s rs cols = .ok r) :
    ∃ s' k, b.rounds.length ≤ rs.length ∧
      b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok r := by
  by_cases hle : b.rounds.length ≤ rs.length
  · have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]; omega
    rw [← List.take_append_drop b.rounds.length rs] at h
    cases hs : b.step ft s (rs.take b.rounds.length) cols with
    | error e => rw [foldBlocks_error ft b l s _ _ cols hlen e hs] at h; cases h
    | ok x =>
      obtain ⟨s', k⟩ := x
      rw [foldBlocks_ok ft b l s _ _ cols hlen s' k hs] at h
      exact ⟨s', k, hle, rfl, h⟩
  · rw [foldBlocks_short ft b l s rs cols hle] at h; cases h

/-- The fold over the two blocks, taken apart. -/
theorem Link.mid_ok {L : Link S Cl} {ft : ℕ} {s s'' : S} {rs : List Fmt.RoundView}
    {cols cols'' : List OpenedColumn} (h : foldBlocks ft L.mid s rs cols = .ok (s'', [], cols'')) :
    ∃ s' k, L.batchB.step ft s rs cols = .ok (s', k) ∧
      afterIn L.hear L.orderAfter s' = .ok s'' := by
  obtain ⟨s', k, hle, hs, h2⟩ := foldBlocks_cons_yes h
  obtain ⟨s₂, k₂, _, hq, h3⟩ := foldBlocks_cons_yes h2
  have hq : L.behindB.step ft s' [] (cols.drop k) = .ok (s₂, k₂) := hq
  have h3 : foldBlocks ft [] s₂ (rs.drop L.batchB.rounds.length) ((cols.drop k).drop k₂) =
    .ok (s'', [], cols'') := h3
  simp only [foldBlocks, Except.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, hd, _⟩ := h3
  have hrs : rs.take L.batchB.rounds.length = rs :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 hd)
  rw [hrs] at hs
  refine ⟨s', k, hs, ?_⟩
  rw [Link.behindB, quiet_step] at hq
  cases ha : L.runBehind s' with
  | error e => rw [ha] at hq; cases hq
  | ok z =>
    rw [ha] at hq
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hq
    rw [← hq.1]
    exact Link.afterIn_of_runBehind ha

/-- The premises of the law, under one name. -/
structure LinkSem.Premises (L : Link S Cl) (ft d : ℕ) : Prop where
  /-- the segment passes its own test on the plan -/
  plan : L.laidB.planOk = true
  /-- every equation has its exponent -/
  square : X.Square
  /-- "later" is a preorder -/
  later : X.LaterOk
  /-- the exponents differ and are at most d: a test on what is fixed before the draw -/
  exps : ∀ s, X.ready s → X.ExpsOk L.order (X.fixed s) d
  /-- FIXED BEFORE THE DRAW, for each named run of claims: a premise on the run's kind -/
  runs : X.RunsFixed L.hear
  /-- a premise on the batching kind -/
  batch : X.BatchAdds ft L.batchB (claimsInBy L.each L.hear L.order)
  /-- for each run behind the batching: a premise on the run's kind -/
  after : X.AfterKeeps L.hear
  /-- for the runs behind the batching together: a premise on these kinds -/
  full : X.AfterFull L

theorem Link.orderOk_of_plan {L : Link S Cl} (h : L.laidB.planOk = true) :
    orderOk L.hear L.order = true := by
  have h' : (orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
    L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.1.1

omit [Fintype K] [DecidableEq K] in
/-- What the premises give at one yes of the batching block's step: the one equation's left-hand
side is the polynomial, at the element drawn. -/
theorem LinkSem.Premises.batch_value {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Premises L ft d) {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : ℕ}
    (hr : X.ready s) (hw : viewWordsBelowPrime ⟨rs, cols⟩ = true)
    (hs : L.batchB.step ft s rs cols = .ok (s', k)) :
    ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧ X.behind s' ∧ ∀ t y, X.later s' t → X.full t →
      X.one t s' y = termsAt K (X.termsFrom (X.fixed s) y L.order 0) (X.rd x) := by
  obtain ⟨x, s₁, cls, s₂, hx, hg, hf, hc, hcl, hone⟩ := H.batch s rs cols s' k hr hw hs
  obtain ⟨hg₂, hc₂, hsum⟩ := X.claimsIn_fixed H.later H.runs _ _ _ _ hg
    (claimsIn_of_claimsInBy _ _ _ _ _ hcl)
  obtain ⟨hb, hl₂, hv⟩ := hone hg₂ (hc₂.trans hc)
  exact ⟨x, hx, hb, fun t y ht hfull => by
    rw [hv t y ht, ← hc, hsum t y (H.later.2 _ _ _ hl₂ ht) hfull, hf]⟩

/-- A root of the polynomial that is not bad: all the segment's equations hold. -/
theorem LinkSem.Premises.back {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Premises L ft d) {p : P} {y : Y} {c : K}
    (hroot : termsAt K (X.termsFrom p y L.order 0) c = 0) (hbad : c ∉ X.bad L.order p y) :
    X.AllEq L.hear p y := by
  intro o ho e he
  by_contra hne
  obtain ⟨t, ht, hte⟩ := X.term_of_eq H.square p y he L.order 0
    ((mem_order_iff (Link.orderOk_of_plan H.plan) o).2 ho)
  apply hbad
  unfold LinkSem.bad
  rw [if_pos ⟨t, ht, by rw [hte]; exact hne⟩, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hroot⟩

omit [Fintype K] [DecidableEq K] in
/-- The like at one yes of the fold over the two blocks. -/
theorem LinkSem.Premises.value {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Premises L ft d) {s s' : S} {rs : List Fmt.RoundView} {cols cols' : List OpenedColumn}
    (hr : X.ready s) (hw : viewWordsBelowPrime ⟨rs, cols⟩ = true)
    (h : foldBlocks ft L.mid s rs cols = .ok (s', [], cols')) :
    ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧
      ∀ y, X.one s' s' y = termsAt K (X.termsFrom (X.fixed s) y L.order 0) (X.rd x) := by
  obtain ⟨s₀, k, hs, ha⟩ := Link.mid_ok h
  obtain ⟨x, hx, hb, hv⟩ := H.batch_value hr hw hs
  obtain ⟨_, hl, hk⟩ := X.afterIn_keeps H.later H.after _ _ _ hb ha
  exact ⟨x, hx, fun y => by rw [hk s' y (H.later.1 s'), hv s' y hl (H.full _ _ hb ha)]⟩

/-- **THE LAW, PROVED FROM THE PREMISES: soundness.** -/
theorem LinkSem.Premises.sound {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Premises L ft d) : X.Sound L ft d := by
  refine ⟨X.bad L.order, fun s y hr => X.bad_card_le H.square (H.exps s hr) y, ?_⟩
  intro s rs cols s' cols' hr hw h
  obtain ⟨x, hx, hv⟩ := H.value hr hw h
  exact ⟨x, hx, fun y hbad hone => H.back ((hv y).symm.trans hone) hbad⟩

omit [Fintype K] [DecidableEq K] in
/-- **THE LAW, PROVED FROM THE PREMISES: true data.** -/
theorem LinkSem.Premises.honest {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Premises L ft d) : X.Honest L ft := by
  intro s rs cols s' cols' y hr hw h hall
  obtain ⟨x, _, hv⟩ := H.value hr hw h
  rw [hv y]
  have hz : ∀ t ∈ X.termsFrom (X.fixed s) y L.order 0, t.2 = 0 := fun t ht => by
    obtain ⟨o, ho, hc⟩ := X.eq_of_term (X.fixed s) y L.order 0 t ht
    exact hall o ((mem_order_iff (Link.orderOk_of_plan H.plan) o).1 ho) _ hc
  unfold termsAt
  apply List.sum_eq_zero
  intro v hv'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv'
  rw [hz t ht, mul_zero]

open Classical in
/-- **The law as a count.** If one equation of the segment fails at the data y, at most d elements
of the field are drawn on some stretch on which the fold says yes and behind which the one equation
holds at y. -/
theorem LinkSem.Sound.count {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Sound L ft d) (s : S) (y : Y) (hr : X.ready s)
    (hn : ¬ X.AllEq L.hear (X.fixed s) y) :
    (Finset.univ.filter fun c : K => ∃ rs cols s' cols' x, viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
      foldBlocks ft L.mid s rs cols = .ok (s', [], cols') ∧
      rs.flatMap (·.drawn.elems) = [x] ∧ X.rd x = c ∧ X.one s' s' y = 0).card ≤ d := by
  obtain ⟨bad, hcard, hback⟩ := H
  refine (Finset.card_le_card fun c hc => ?_).trans (hcard s y hr)
  rw [Finset.mem_filter] at hc
  obtain ⟨_, rs, cols, s', cols', x, hw, hf, hx, rfl, hone⟩ := hc
  obtain ⟨x', hx', hb⟩ := hback s rs cols s' cols' hr hw hf
  have : x' = x := by rw [hx] at hx'; exact (List.cons.inj hx').1.symm
  subst this
  by_contra hnb
  exact hn (hb y hnb hone)

/-- All three words of a drawn element are below the prime. -/
def okE (x : Fmt.Ext) : Bool := x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord

theorem okE_of_okViewW {rs : List Fmt.RoundView} {cols : List OpenedColumn} {x : Fmt.Ext}
    (h : viewWordsBelowPrime ⟨rs, cols⟩ = true) (hx : rs.flatMap (·.drawn.elems) = [x]) : okE x = true := by
  have hm : x ∈ rs.flatMap (·.drawn.elems) := by rw [hx]; exact List.mem_singleton.2 rfl
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hm
  simp only [viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.1 r hr).1 x hxr
  simpa [okE, Bool.and_eq_true] using this

/-- The reading of a drawn element tells apart the elements whose words are below the prime. -/
def LinkSem.RdInj (X : LinkSem K S Cl P Y) : Prop :=
  ∀ x x', okE x = true → okE x' = true → X.rd x = X.rd x' → x = x'

/-- **A filling is worth something only if** the fold says yes somewhere at true data, AND SAYS YES
SOMEWHERE AT DATA AT WHICH AN EQUATION OF THE SEGMENT FAILS, and the reading takes more than d
values on elements whose words are below the prime. Without the second the half on soundness may
speak of no state from which the fold ever says yes; a meaning whose one equation never holds (`one`
never 0) fails the first together with `Honest`; with a reading of at most d values all draws may be
bad. (For a count of DRAWS more is wanted of the reading: `RdInj`.) -/
def LinkSem.Worth (X : LinkSem K S Cl P Y) (L : Link S Cl) (ft d : ℕ) : Prop :=
  X.Answers L ft ∧
  (∃ s rs cols s' cols' y, X.ready s ∧ viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
    foldBlocks ft L.mid s rs cols = .ok (s', [], cols') ∧ ¬ X.AllEq L.hear (X.fixed s) y) ∧
  ∃ xs : List Fmt.Ext, (xs.map X.rd).Nodup ∧ xs.length = d + 1 ∧ ∀ x ∈ xs, okE x = true

omit [Fintype K] in
/-- **The law as a count of DRAWS.** If the reading tells such elements apart, and one equation of
the segment fails at the data y: of the elements as a view shows them (three words), at most d are
drawn on some stretch on which the fold says yes and behind which the one equation holds at y. -/
theorem LinkSem.Sound.count_draws {X : LinkSem K S Cl P Y} {L : Link S Cl} {ft d : ℕ}
    (H : X.Sound L ft d) (hinj : X.RdInj) (s : S) (y : Y) (hr : X.ready s)
    (hn : ¬ X.AllEq L.hear (X.fixed s) y) (xs : List Fmt.Ext) (hnd : xs.Nodup)
    (hxs : ∀ x ∈ xs, ∃ rs cols s' cols', viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
      foldBlocks ft L.mid s rs cols = .ok (s', [], cols') ∧
      rs.flatMap (·.drawn.elems) = [x] ∧ X.one s' s' y = 0) : xs.length ≤ d := by
  obtain ⟨bad, hcard, hback⟩ := H
  have hok : ∀ x ∈ xs, okE x = true := fun x hx => by
    obtain ⟨rs, cols, _, _, hw, _, he, _⟩ := hxs x hx
    exact okE_of_okViewW hw he
  have hnd' : (xs.map X.rd).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab => hinj a b (hok a ha) (hok b hb) hab) hnd
  have hsub : (xs.map X.rd).toFinset ⊆ bad (X.fixed s) y := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
    obtain ⟨rs, cols, s', cols', hw, hf, he, hone⟩ := hxs x hx
    obtain ⟨x', hx', hb⟩ := hback s rs cols s' cols' hr hw hf
    have : x' = x := by rw [he] at hx'; exact (List.cons.inj hx').1.symm
    subst this
    by_contra hnb
    exact hn (hb y hnb hone)
  calc xs.length = (xs.map X.rd).length := (List.length_map _).symm
    _ = (xs.map X.rd).toFinset.card := (List.toFinset_card_of_nodup hnd').symm
    _ ≤ (bad (X.fixed s) y).card := Finset.card_le_card hsub
    _ ≤ d := hcard s y hr

end TheLaw

/-! ## 8 The silly members: the law tried on toys, as theorems -/

namespace LinkToy

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The toy's field. -/
abbrev F5 : Type := ZMod 5

/-- The toy's state: a scalar heard before the draw; the challenge; the one equation's sums: a
coefficient on each of two hidden values; and a weight under which both hidden values are read,
WHICH A RUN BEHIND THE BATCHING LAYS. -/
structure St where
  heard : F5
  chi : F5
  led : F5 × F5
  w : Option F5

/-- A claim of the toy's: `scale` times a hidden value (the second one, or the first) is 0. -/
structure TClaim where
  second : Bool
  scale : F5

/-- A drawn element as an element of the field: its first word. -/
def rd (x : Fmt.Ext) : F5 := (x.1.toNat : F5)

/-- The block that hears, with a given run behind the batching: no round. Its one run of claims
makes two claims: the scalar heard times the first hidden value is 0; THE CHALLENGE times the second
is 0: a claim that reads the challenge. -/
def hearWith (aft : St → Except String St) : Block St TClaim :=
  { name := "hear", place := ⟨1, some 0, 1, .K4⟩, planOk := true, rounds := [], oracles := []
    before := [], decide := fun s _ _ => .ok s
    claims := [("both", fun _ s => .ok ([⟨false, s.heard⟩, ⟨true, s.chi⟩], s))]
    after := [("weigh", aft)] }

/-- The run behind the batching as it is meant: it lays the weight 2. -/
def weigh (s : St) : Except String St := .ok { s with w := some 2 }

/-- The hearing block as it is meant. -/
def hearB : Block St TClaim := hearWith weigh

/-- Claims added to the sums, claim number n under c ^ n. -/
def addAll (c : F5) : ℕ → List TClaim → F5 × F5 → F5 × F5
  | _, [], l => l
  | n, cl :: cs, l =>
    addAll c (n + 1) cs
      (if cl.second then (l.1, l.2 + c ^ n * cl.scale) else (l.1 + c ^ n * cl.scale, l.2))

/-- The batching's one round: nothing is sent; one element is drawn. -/
def round : Fmt.DeclaredRound := { entry := { name := "BAT-sigma", drawE := 1 } }

/-- A block with that round and a given decision. -/
def blockOf (dec : St → List Fmt.RoundView → Except String St) : Block St TClaim :=
  { name := "batch", place := ⟨1, some 0, 2, .K9⟩, planOk := true, rounds := [round]
    oracles := [[]], before := [], decide := fun s rs _ => dec s rs, claims := [], after := [] }

/-- The decision of the toy's batching: it lays the element drawn into the state, runs the function
of claims that it is handed, and adds the claims. -/
def batchDec (f : St → Except String (List TClaim × St)) (s : St) (rs : List Fmt.RoundView) :
    Except String St :=
  match rs.flatMap (·.drawn.elems) with
  | [x] => (f { s with chi := rd x }).map fun y => { y.2 with led := addAll (rd x) 0 y.1 (0, 0) }
  | _ => .error "one element"

/-- THE TOY's BATCHING. -/
def batchB (f : St → Except String (List TClaim × St)) : Block St TClaim := blockOf (batchDec f)

/-- A toy segment. -/
def link (hear : Block St TClaim)
    (batch : (St → Except String (List TClaim × St)) → Block St TClaim)
    (order orderAfter : List (ℕ × String)) : Link St TClaim :=
  { name := "toy", chain := 1, number := 0, lay := .ok, hear := [hear], order := order
    each := fun _ _ _ => .ok (), orderAfter := orderAfter, tests := fun _ => .ok ()
    batch := batch, close := [], clear := .ok }

/-- The segment as it is meant. -/
def meant : Link St TClaim := link hearB batchB [(0, "both")] [(0, "weigh")]

/-- SILLY: its batching says yes to all and hands the state on. -/
def yesToAll : Link St TClaim :=
  link hearB (fun _ => blockOf fun s _ => .ok s) [(0, "both")] [(0, "weigh")]

/-- SILLY: its batching says no to all. -/
def noToAll : Link St TClaim :=
  link hearB (fun _ => blockOf fun _ _ => .error "no") [(0, "both")] [(0, "weigh")]

/-- SILLY: its batching has no round, draws nothing and says yes. -/
def drawsNothing : Link St TClaim :=
  link hearB (fun _ => roundlessBlock "batch" 1 (some 0) 2 .ok) [(0, "both")] [(0, "weigh")]

/-- SILLY: the order forgets the run of claims. -/
def forgetful : Link St TClaim := link hearB batchB [] [(0, "weigh")]

/-- SILLY: the run behind the batching wipes the sums. -/
def wipes : Link St TClaim :=
  link (hearWith fun s => .ok { s with led := (0, 0), w := some 2 }) batchB [(0, "both")]
    [(0, "weigh")]

/-- SILLY: the second order forgets the run behind the batching: the weight is never laid. -/
def forgetsAfter : Link St TClaim := link hearB batchB [(0, "both")] []

/-- The meaning beside all of them: the prover's data are the two hidden values; what is fixed
before the draw is the scalar heard; a state is full once the weight 2 is laid; what is laid stays.
-/
def sem : LinkSem F5 St TClaim F5 (F5 × F5) :=
  { rd := rd, fixed := (·.heard), chi := (·.chi)
    ready := fun s => s.w = none, good := fun s => s.w = none
    behind := fun s => s.w = none ∨ s.w = some 2
    later := fun s t => s.w = none ∨ s.w = t.w
    full := fun t => t.w = some 2
    wv := fun t y c j cl => t.w.getD 0 * (c ^ j * cl.scale * (if cl.second then y.2 else y.1))
    one := fun t s y => t.w.getD 0 * (s.led.1 * y.1 + s.led.2 * y.2)
    cnt := fun _ _ => 2
    eqs := fun _ p y => [2 * (p * y.1), 2 * y.2]
    exps := fun _ n _ => [n, n + 2] }

/-- A round in which nothing is sent and x is drawn. -/
def rv (x : Fmt.Ext) : Fmt.RoundView := ⟨[], ⟨[x], [], [], none⟩⟩

theorem elems_noDigest (rs : List Fmt.RoundView) :
    (rs.map noDigest).flatMap (·.drawn.elems) = rs.flatMap (·.drawn.elems) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]; rfl

/-- A block of the toy's as a step, on one round that draws x. -/
theorem blockOf_step (dec : St → List Fmt.RoundView → Except String St) (s : St) (x : Fmt.Ext) :
    (blockOf dec).step 0 s [rv x] [] = (dec s [rv x]).map fun s' => (s', 0) := by
  have h1 : roundsFit (blockOf dec).rounds [rv x] = true := rfl
  have h2 : groupsOf 0 (blockOf dec).rounds ([rv x].map (·.drawn)) = [] := rfl
  have h3 : [rv x].map noDigest = [rv x] := rfl
  rw [Block.step_eq, h1, h2, h3]
  cases h : dec s [rv x] <;>
    simp [blockOf, h, Except.map, bind, Except.bind, pure, Except.pure]

/-- Where a block of the toy's says yes, its decision has said yes on the rounds without their
digests. -/
theorem blockOf_yes {dec : St → List Fmt.RoundView → Except String St} {s s' : St} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : (blockOf dec).step 0 s rs cols = .ok (s', k)) :
    dec s (rs.map noDigest) = .ok s' := by
  rw [Block.step_eq] at h
  split at h
  · split at h
    · simp only [blockOf] at h
      cases hd : dec s (rs.map noDigest) with
      | error e => simp [hd, bind, Except.bind] at h
      | ok z =>
        simp only [hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]
    · cases h
  · cases h

/-- The fold over a toy segment's two blocks, on one round that draws x. -/
theorem mid_eval (L : Link St TClaim) (dec : St → List Fmt.RoundView → Except String St)
    (hb : L.batchB = blockOf dec) (s s' s'' : St) (x : Fmt.Ext) (hd : dec s [rv x] = .ok s')
    (ha : L.runBehind s' = .ok s'') :
    foldBlocks 0 L.mid s [rv x] [] = .ok (s'', [], []) := by
  have h1 : L.batchB.step 0 s [rv x] [] = .ok (s', 0) := by
    rw [hb, blockOf_step, hd]; rfl
  have h2 : L.behindB.step 0 s' [] [] = .ok (s'', 0) := by
    rw [Link.behindB, quiet_step, ha]; rfl
  have e1 := foldBlocks_ok 0 L.batchB [L.behindB] s [rv x] [] [] (by rw [hb]; rfl) s' 0 h1
  have e2 := foldBlocks_ok 0 L.behindB [] s' [] [] [] rfl s'' 0 h2
  rw [Link.mid, ← List.append_nil [rv x], e1]
  exact e2

theorem claims_hear (aft : St → Except String St) (s : St) :
    claimsIn [hearWith aft] [(0, "both")] s = .ok ([⟨false, s.heard⟩, ⟨true, s.chi⟩], s) := by
  simp [claimsIn, claimsInBy, claimsInStep, hearWith, named, List.lookup, Except.bind]

/-- The toy's batching, handed the hearing block's claims, on one round that draws x. -/
theorem batchDec_hear (aft : St → Except String St) (s : St) (x : Fmt.Ext) :
    batchDec (claimsIn [hearWith aft] [(0, "both")]) s [rv x] =
      .ok ⟨s.heard, rd x, addAll (rd x) 0 [⟨false, s.heard⟩, ⟨true, rd x⟩] (0, 0), s.w⟩ := by
  have h : batchDec (claimsIn [hearWith aft] [(0, "both")]) s [rv x] =
      (claimsIn [hearWith aft] [(0, "both")] { s with chi := rd x }).map fun y =>
        { y.2 with led := addAll (rd x) 0 y.1 (0, 0) } := rfl
  rw [h, claims_hear]
  rfl

theorem after_hear (aft : St → Except String St) (s s' : St) (h : aft s = .ok s') :
    afterIn [hearWith aft] [(0, "weigh")] s = .ok s' := by
  simp [afterIn, hearWith, named, List.lookup, Except.bind, h]

theorem addAll_value (c : F5) (t : St) (y : F5 × F5) : ∀ (cls : List TClaim) (n : ℕ) (l : F5 × F5),
    t.w.getD 0 * ((addAll c n cls l).1 * y.1 + (addAll c n cls l).2 * y.2) =
      t.w.getD 0 * (l.1 * y.1 + l.2 * y.2) + sem.wsum t y c n cls
  | [], _, _ => by simp [addAll, LinkSem.wsum]
  | cl :: cs, n, l => by
    rw [addAll, addAll_value c t y cs]
    simp only [LinkSem.wsum, sem]
    cases cl.second <;> simp <;> ring

theorem run_of_hear {aft : St → Except String St} {o : ℕ × String}
    {run : ℕ → St → Except String (List TClaim × St)} (h : runOf [hearWith aft] o = some run) :
    run = fun _ s => .ok ([⟨false, s.heard⟩, ⟨true, s.chi⟩], s) := by
  obtain ⟨i, nm⟩ := o
  cases i with
  | zero =>
    simp only [runOf, hearWith, List.getElem?_cons_zero, Option.bind_some, List.lookup] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  | succ i => simp [runOf] at h

theorem after_of_hear {o : ℕ × String} {run : St → Except String St}
    (h : afterOf [hearB] o = some run) : run = weigh := by
  obtain ⟨i, nm⟩ := o
  cases i with
  | zero =>
    simp only [afterOf, hearB, hearWith, List.getElem?_cons_zero, Option.bind_some,
      List.lookup] at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  | succ i => simp [afterOf] at h

/-- THE MEANT SEGMENT MEETS ALL PREMISES OF THE LAW, at d = 2 (the field has 5 elements). -/
theorem meant_premises : sem.Premises meant 0 2 where
  plan := by decide
  square := fun _ _ _ _ => rfl
  later := ⟨fun _ => Or.inr rfl, fun s t u h h' => by
    rcases h with h | h
    · exact Or.inl h
    · rcases h' with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h.trans h')⟩
  exps := fun _ _ => by
    simp [LinkSem.ExpsOk, LinkSem.expsFrom, sem, meant, link]
  runs := fun o run h n s cls s' hg hr => by
    rw [run_of_hear h] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hg, Or.inr rfl, rfl, rfl, rfl, fun t y _ hfull => ?_⟩
    have hw : t.w = some 2 := hfull
    simp only [LinkSem.wsum, LinkSem.terms, termsAt, sem, hw, Option.getD_some, List.zip_cons_cons,
      List.zip_nil_right, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp
    ring
  batch := fun s rs cols s' k hr _ h => by
    have hd : batchDec (claimsIn [hearB] [(0, "both")]) s (rs.map noDigest) = .ok s' :=
      blockOf_yes h
    unfold batchDec at hd
    simp only [elems_noDigest] at hd
    split at hd
    · next x hx =>
      rw [hearB, claims_hear] at hd
      simp only [Except.map, Except.ok.injEq] at hd
      subst hd
      refine ⟨x, { s with chi := rd x }, _, { s with chi := rd x }, hx, hr, rfl, rfl,
        claims_hear _ _, fun hg _ => ⟨Or.inl hg, Or.inl hg, fun t y _ => ?_⟩⟩
      have := addAll_value (rd x) t y [⟨false, s.heard⟩, ⟨true, rd x⟩] 0 (0, 0)
      simpa [sem] using this
    · cases hd
  after := fun o run h s s' hb hr => by
    rw [after_of_hear h] at hr
    simp only [weigh, Except.ok.injEq] at hr
    subst hr
    exact ⟨Or.inr rfl, hb, fun _ _ _ => rfl⟩
  full := fun s s' _ h => by
    have h' : afterIn [hearWith weigh] [(0, "weigh")] s = .ok s' := h
    rw [after_hear weigh s _ rfl] at h'
    simp only [Except.ok.injEq] at h'
    subst h'
    rfl

/-- So it meets the law's two halves. -/
theorem meant_sound : sem.Sound meant 0 2 := meant_premises.sound
theorem meant_honest : sem.Honest meant 0 := meant_premises.honest

/-- The state from which the toys start: the scalar heard is 1; no weight is laid. -/
def s0 : St := ⟨1, 0, (0, 0), none⟩

/-- The meant segment's fold on one round that draws x. -/
theorem meant_eval (x : Fmt.Ext) :
    foldBlocks 0 meant.mid s0 [rv x] [] =
      .ok (⟨1, rd x, addAll (rd x) 0 [⟨false, 1⟩, ⟨true, rd x⟩] (0, 0), some 2⟩, [], []) :=
  mid_eval meant _ rfl s0 ⟨1, rd x, addAll (rd x) 0 [⟨false, 1⟩, ⟨true, rd x⟩] (0, 0), none⟩ _ x
    (batchDec_hear weigh s0 x) (after_hear weigh _ _ rfl)

/-- The companion: at the hidden values 0, 0 it says yes. -/
theorem meant_answers : sem.Answers meant 0 :=
  ⟨s0, [rv (0, 0, 0)], [], _, [], (0, 0), rfl, by decide, meant_eval _,
    fun _ _ c hc => by simpa [sem] using hc⟩

theorem both_mem (aft : St → Except String St) : (0, "both") ∈ allRuns [hearWith aft] := by
  simp [allRuns, hearWith]

/-- At the scalar heard 1 and the hidden values 1, 0 the first equation fails. -/
theorem not_allEq (aft : St → Except String St) : ¬ sem.AllEq [hearWith aft] 1 (1, 0) := fun h =>
  absurd (h (0, "both") (both_mem aft) 2 (by simp [sem])) (by decide)

/-- The toy's filling is worth something. -/
theorem meant_worth : sem.Worth meant 0 2 :=
  ⟨meant_answers,
    ⟨s0, [rv (0, 0, 0)], [], _, [], (1, 0), rfl, by decide, meant_eval _, not_allEq weigh⟩,
    ⟨[(0, 0, 0), (1, 0, 0), (2, 0, 0)], by decide, rfl, by decide⟩⟩

/-- A segment of the toy's whose fold says yes at every draw with a one equation that holds at the
hidden values 1, 0, where the first equation fails, does not meet the law at d = 2. -/
theorem not_sound (L : Link St TClaim) (aft : St → Except String St) (hh : L.hear = [hearWith aft])
    (h : ∀ x : Fmt.Ext, ∃ s', foldBlocks 0 L.mid s0 [rv x] [] = .ok (s', [], []) ∧
      sem.one s' s' (1, 0) = 0) : ¬ sem.Sound L 0 2 := by
  rintro ⟨bad, hcard, hback⟩
  have hin : ∀ x : Fmt.Ext, viewWordsBelowPrime ⟨[rv x], []⟩ = true → rd x ∈ bad 1 (1, 0) := by
    intro x hw
    obtain ⟨s', hf, hone⟩ := h x
    obtain ⟨x', hx', hb⟩ := hback s0 [rv x] [] s' [] rfl hw hf
    have hxx : x' = x := by
      have : [x] = [x'] := hx'
      exact (List.cons.inj this).1.symm
    subst hxx
    by_contra hn
    have hall := hb (1, 0) hn hone
    rw [hh] at hall
    exact not_allEq aft hall
  have h0 : (0 : F5) ∈ bad 1 (1, 0) := hin (0, 0, 0) (by decide)
  have h1 : (1 : F5) ∈ bad 1 (1, 0) := hin (1, 0, 0) (by decide)
  have h2 : (2 : F5) ∈ bad 1 (1, 0) := hin (2, 0, 0) (by decide)
  have hs : ({0, 1, 2} : Finset F5) ⊆ bad 1 (1, 0) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have h3 := (Finset.card_le_card hs).trans (hcard s0 (1, 0) rfl)
  exact absurd h3 (by decide)

/-- **YES TO ALL DOES NOT MEET THE LAW.** -/
theorem yesToAll_not_sound : ¬ sem.Sound yesToAll 0 2 :=
  not_sound yesToAll weigh rfl fun x =>
    ⟨{ s0 with w := some 2 }, mid_eval yesToAll (fun s _ => .ok s) rfl s0 s0 _ x rfl
      (after_hear weigh _ _ rfl), by simp [sem, s0]⟩

/-- **AN ORDER THAT FORGETS A RUN OF CLAIMS DOES NOT MEET THE LAW.** -/
theorem forgetful_not_sound : ¬ sem.Sound forgetful 0 2 :=
  not_sound forgetful weigh rfl fun x =>
    ⟨⟨1, rd x, (0, 0), some 2⟩, mid_eval forgetful _ rfl s0 ⟨1, rd x, (0, 0), none⟩ _ x rfl
      (after_hear weigh _ _ rfl), by simp [sem]⟩

/-- **A RUN BEHIND THE BATCHING THAT WIPES THE SUMS DOES NOT MEET THE LAW.** -/
theorem wipes_not_sound : ¬ sem.Sound wipes 0 2 :=
  not_sound wipes _ rfl fun x =>
    ⟨⟨1, rd x, (0, 0), some 2⟩,
      mid_eval wipes _ rfl s0 ⟨1, rd x, addAll (rd x) 0 [⟨false, 1⟩, ⟨true, rd x⟩] (0, 0), none⟩ _ x
        (batchDec_hear _ s0 x) (after_hear _ _ _ rfl), by simp [sem]⟩

/-- **A SECOND ORDER THAT FORGETS THE RUN BEHIND THE BATCHING DOES NOT MEET THE LAW**: the weight is
never laid, and the one equation says nothing. -/
theorem forgetsAfter_not_sound : ¬ sem.Sound forgetsAfter 0 2 :=
  not_sound forgetsAfter weigh rfl fun x =>
    ⟨⟨1, rd x, addAll (rd x) 0 [⟨false, 1⟩, ⟨true, rd x⟩] (0, 0), none⟩,
      mid_eval forgetsAfter _ rfl s0 _ _ x
        (batchDec_hear weigh s0 x) rfl, by simp [sem]⟩

/-- **A BATCHING THAT DRAWS NOTHING AND SAYS YES DOES NOT MEET THE LAW.** -/
theorem drawsNothing_not_sound : ¬ sem.Sound drawsNothing 0 2 := by
  rintro ⟨_, _, hback⟩
  have h1 : drawsNothing.batchB.step 0 s0 [] [] = .ok (s0, 0) := by
    show (roundlessBlock "batch" 1 (some 0) 2 .ok : Block St TClaim).step 0 s0 [] [] = _
    rw [quiet_step]; rfl
  have h2 : drawsNothing.behindB.step 0 s0 [] [] = .ok ({ s0 with w := some 2 }, 0) := by
    rw [Link.behindB, quiet_step,
      show drawsNothing.runBehind s0 = _ from after_hear weigh _ _ rfl]
    rfl
  have e1 := foldBlocks_ok 0 drawsNothing.batchB [drawsNothing.behindB] s0 [] [] [] rfl s0 0 h1
  have e2 := foldBlocks_ok 0 drawsNothing.behindB [] s0 [] [] [] rfl _ 0 h2
  obtain ⟨x, hx, _⟩ := hback s0 [] [] _ [] rfl (by decide) (e1.trans e2)
  cases hx

/-- NO TO ALL meets the half on soundness, as every verifier that refuses all does … -/
theorem noToAll_sound : sem.Sound noToAll 0 2 :=
  ⟨fun _ _ => ∅, fun _ _ _ => by simp, fun s rs cols s' cols' _ _ h => by
    obtain ⟨s₀, k, hs, _⟩ := Link.mid_ok h
    cases blockOf_yes (dec := fun _ _ => .error "no") hs⟩

/-- … AND **DOES NOT MEET THE COMPANION.** -/
theorem noToAll_not_answers : ¬ sem.Answers noToAll 0 := by
  rintro ⟨s, rs, cols, s', cols', y, _, _, h, _⟩
  obtain ⟨s₀, k, hs, _⟩ := Link.mid_ok h
  cases blockOf_yes (dec := fun _ _ => .error "no") hs

end LinkToy

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.termsPoly_cons
#print axioms VerifiableInference.Desc.termsAt_cons
#print axioms VerifiableInference.Desc.termsAt_append
#print axioms VerifiableInference.Desc.termsPoly_eval
#print axioms VerifiableInference.Desc.termsPoly_coeff_of_not_mem
#print axioms VerifiableInference.Desc.termsPoly_coeff
#print axioms VerifiableInference.Desc.termsPoly_natDegree_le
#print axioms VerifiableInference.Desc.termsAt_roots_le
#print axioms VerifiableInference.Desc.toOption_eq_some
#print axioms VerifiableInference.Desc.runsOneByOne_cons
#print axioms VerifiableInference.Desc.runs_of_claimsIn
#print axioms VerifiableInference.Desc.mem_order_iff
#print axioms VerifiableInference.Desc.LinkSem.expsOkB_iff
#print axioms VerifiableInference.Desc.LinkSem.wsum_append
#print axioms VerifiableInference.Desc.LinkSem.runs_fixed
#print axioms VerifiableInference.Desc.LinkSem.claimsIn_fixed
#print axioms VerifiableInference.Desc.LinkSem.map_fst_termsFrom
#print axioms VerifiableInference.Desc.LinkSem.termsOk
#print axioms VerifiableInference.Desc.LinkSem.term_of_eq
#print axioms VerifiableInference.Desc.LinkSem.eq_of_term
#print axioms VerifiableInference.Desc.LinkSem.bad_card_le
#print axioms VerifiableInference.Desc.afterIn_eq
#print axioms VerifiableInference.Desc.foldA_error
#print axioms VerifiableInference.Desc.stepA_ok
#print axioms VerifiableInference.Desc.Link.flat_eq
#print axioms VerifiableInference.Desc.LinkSem.afterIn_keeps
#print axioms VerifiableInference.Desc.quiet_step
#print axioms VerifiableInference.Desc.foldBlocks_cons_yes
#print axioms VerifiableInference.Desc.Link.mid_ok
#print axioms VerifiableInference.Desc.Link.orderOk_of_plan
#print axioms VerifiableInference.Desc.LinkSem.Premises.batch_value
#print axioms VerifiableInference.Desc.LinkSem.Premises.back
#print axioms VerifiableInference.Desc.LinkSem.Premises.value
#print axioms VerifiableInference.Desc.LinkSem.Premises.sound
#print axioms VerifiableInference.Desc.LinkSem.Premises.honest
#print axioms VerifiableInference.Desc.LinkSem.Sound.count
#print axioms VerifiableInference.Desc.okE_of_okViewW
#print axioms VerifiableInference.Desc.LinkSem.Sound.count_draws
#print axioms VerifiableInference.Desc.LinkToy.elems_noDigest
#print axioms VerifiableInference.Desc.LinkToy.blockOf_step
#print axioms VerifiableInference.Desc.LinkToy.blockOf_yes
#print axioms VerifiableInference.Desc.LinkToy.mid_eval
#print axioms VerifiableInference.Desc.LinkToy.claims_hear
#print axioms VerifiableInference.Desc.LinkToy.batchDec_hear
#print axioms VerifiableInference.Desc.LinkToy.after_hear
#print axioms VerifiableInference.Desc.LinkToy.addAll_value
#print axioms VerifiableInference.Desc.LinkToy.run_of_hear
#print axioms VerifiableInference.Desc.LinkToy.after_of_hear
#print axioms VerifiableInference.Desc.LinkToy.meant_premises
#print axioms VerifiableInference.Desc.LinkToy.meant_sound
#print axioms VerifiableInference.Desc.LinkToy.meant_honest
#print axioms VerifiableInference.Desc.LinkToy.meant_eval
#print axioms VerifiableInference.Desc.LinkToy.meant_answers
#print axioms VerifiableInference.Desc.LinkToy.both_mem
#print axioms VerifiableInference.Desc.LinkToy.not_allEq
#print axioms VerifiableInference.Desc.LinkToy.meant_worth
#print axioms VerifiableInference.Desc.LinkToy.not_sound
#print axioms VerifiableInference.Desc.LinkToy.yesToAll_not_sound
#print axioms VerifiableInference.Desc.LinkToy.forgetful_not_sound
#print axioms VerifiableInference.Desc.LinkToy.wipes_not_sound
#print axioms VerifiableInference.Desc.LinkToy.forgetsAfter_not_sound
#print axioms VerifiableInference.Desc.LinkToy.drawsNothing_not_sound
#print axioms VerifiableInference.Desc.LinkToy.noToAll_sound
#print axioms VerifiableInference.Desc.LinkToy.noToAll_not_answers
