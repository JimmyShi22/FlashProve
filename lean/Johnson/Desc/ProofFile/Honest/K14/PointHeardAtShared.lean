-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/PointHeardAtShared.lean: kind K14: TWO SILENT DEFAULTS OF THIS
KIND's TEXTS THAT HANG ON A RUN ARE NOT TAKEN FROM THE BORDER 2 OF THE SHARED CHAIN ON, wherever
that chain's honest thread stands. Statements with their proofs; no definition.

The two defaults.
  * The parts at "send o_u", "send o_omega" and "SPLIT" read the shared point by heardFrom
    (Honest/ForKinds.lean), which returns a shorter list, and no error, where fewer challenges have
    been heard; and the vectors' texts take and drop elements of the point, so that a point of too
    few elements gives other weights in silence (the head of Honest/K14/Sendings.lean; the list of
    Honest/K14/DefaultsIdle.lean, under C).
  * The thread's witness reads the first challenge heard by firstRv (Honest/K14/Thread2.lean), which
    returns "no challenge" where none has been heard.

  point_heard         **at the full size, where the invariant of the shared chain's thread holds at
                      a border b with 2 ≤ b: a first challenge has been heard, and it holds as many
                      field elements as the round "LIN point" declares**, whatever the thread's
                      other letters are
  firstRv_heard       so firstRv returns that challenge, not its default
  heardFrom_point     and heardFrom at the number 0 returns a list of one challenge, not a shorter
                      one

How. The invariant's clause on the challenges heard (Thread.Fit, Honest/Thread/Thr.lean) says that
they fit the rounds declared in front of the border. The chain's member 0 declares no round; its
member 1, "LIN point", declares one (rounds_of_blocks, Johnson/Desc/K14/Law/RoundsMake.lean).

Limits.
  * h is a hypothesis: P5J.AtMgA (Johnson/P5J/MgAtAll.lean), at the hash OnBytes.secondHashFunction. That the
    invariant holds at any state of any run is not shown.
  * AT THE BORDERS 0 AND 1 BOTH DEFAULTS ARE TAKEN: nothing has been heard there. No part of this
    kind stands in front of the border 2.
  * AT A BORDER. A part moves inside a member, behind the border, where more has been heard: that
    what heardFrom returns stays is heardFrom_more (Honest/Thread/HeardLaw.lean); it is not joined
    here.
  * The point alone. The challenge of "LIN zeta", which the part at "SPLIT" reads too, and the seeds
    of the two sendings (the same list, under C) are not treated.
  * That the number which the round declares is the number of elements that the shape counts is not
    said here.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.TiesAtTheEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St p14Of beforePointOf)
open Desc.K14.Law (entryAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X P₁ Wt : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **From the border 2 on a first challenge has been heard, and it holds as many field elements as
the round "LIN point" declares.** -/
theorem point_heard (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Nat} {k : Coins Bk}
    {s : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (b + 2) k s m E) :
    ∃ d rest, m.st.heard = d :: rest ∧
      d.elems.length = (entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0).drawE := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨r₁, hr, hre⟩ : ∃ r₁, B.b1.rounds = [r₁] ∧
      r₁.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0 := by
    have q := (Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ B.made).1
    cases hb1 : B.b1.rounds with
    | nil => rw [hb1] at q; cases q
    | cons a t =>
      rw [hb1] at q
      cases t with
      | nil => exact ⟨a, rfl, (List.cons.inj q).1⟩
      | cons a' t' => cases (List.cons.inj q).2
  have hF : drawsFit (declsTo (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread.bs (b + 2)) m.st.heard = true := hA.2.1
  have ed : ∃ more, declsTo (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread.bs (b + 2) = r₁ :: more := by
    refine ⟨((x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl).take b).flatMap (·.rounds), ?_⟩
    unfold declsTo
    rw [e]
    simp only [List.take_succ_cons, List.flatMap_cons]
    rw [l0.rounds, l1.rounds, hr]
    rfl
  obtain ⟨more, ed⟩ := ed
  rw [ed] at hF
  cases hh : m.st.heard with
  | nil => rw [hh] at hF; cases hF
  | cons d rest =>
    rw [hh] at hF
    have h1 : drawFit r₁ d = true := (Bool.and_eq_true_iff.1 hF).1
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨d, rest, rfl, by rw [← hre]; exact h1.1.1.1.1.1.1.1⟩

/-- So firstRv returns the first challenge heard, not its default. -/
theorem firstRv_heard (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Nat} {k : Coins Bk}
    {s : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (b + 2) k s m E) :
    ∃ d rest, m.st.heard = d :: rest ∧ firstRv m.st.heard = rvOf d := by
  obtain ⟨d, rest, e, -⟩ :=
    point_heard H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  exact ⟨d, rest, e, by rw [e]; rfl⟩

/-- And heardFrom at the number 0 returns a list of one challenge. -/
theorem heardFrom_point (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Nat} {k : Coins Bk}
    {s : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (b + 2) k s m E) :
    ∃ d, heardFrom m.st 0 1 = [d] ∧
      d.elems.length = (entryAt (p14Of Zp.p.chains (beforePointOf Np)) 0).drawE := by
  obtain ⟨d, rest, e, hl⟩ :=
    point_heard H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  exact ⟨d, by unfold heardFrom; rw [e]; rfl, hl⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.point_heard
#print axioms ProofFile.Honest.K14.firstRv_heard
#print axioms ProofFile.Honest.K14.heardFrom_point
