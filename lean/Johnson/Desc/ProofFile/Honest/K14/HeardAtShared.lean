-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/HeardAtShared.lean: kind K14: MORE SILENT DEFAULTS OF THIS KIND's
TEXTS THAT HANG ON A RUN ARE NOT TAKEN, wherever the shared chain's honest thread stands. It goes on
from Honest/K14/PointHeardAtShared.lean. Statements with their proofs; no definition.

The defaults (the head of Honest/K14/Sendings.lean; the list of Honest/K14/DefaultsIdle.lean, under
C).
  * The parts at "send o_u", "send o_omega" and "SPLIT" read the shared point, and the part at
  "SPLIT" the
    challenge of "LIN zeta" too, by heardFrom (Honest/ForKinds.lean), which returns a shorter list,
    and no error, where fewer challenges have been heard; and the vectors' texts take and drop
    elements of these challenges, so that one of too few elements gives other weights in silence.
  * The two sendings cut their seeds off the elements of a challenge (K1.cutSeeds); where these are
  too
    few a seed's point is shorter and its factor is 0.

  drawsFit_at, heardFrom_of   two steps on lists
  point_whole     **from the border 2 on**: there is a challenge d with as many field elements as
                  the shape counts columns' variables (kCol), and heardFrom at the number 0 returns
                  [d] AT EVERY STATE THAT HAS HEARD WHAT THE STAND HAS HEARD AND MORE: so also
                  inside a member, at a state of whatever types
  zeta_whole      **from the border 8 on** the like for "LIN zeta": the number 6, kRow elements
  seeds_whole_u, seeds_whole_omega   **at every list of challenges that the rounds of the member 2
                                     (of the
                  member 5) can draw**: the first holds just the seeds' elements, and no seed's
                  factor is 0: the library's draws_send (Johnson/SendSim/At/SeatedAt.lean) at the
                  member's own rounds

Limits.
  * h is a hypothesis: P5J.AtMgA (Johnson/P5J/MgAtAll.lean), at the hash OnBytes.secondHashFunction. That the
    invariant holds at any state of any run is not shown.
  * In front of the border 2 (of the border 8) the default IS taken. No part of this kind that reads
    the point stands in front of the border 2, and none that reads "LIN zeta" in front of the border
    8.
  * That a part's own state has heard what the stand has heard and more is a premise of the two
    first (ht): it is not joined here to the frame's play.
  * The numbers 0 and 6 are those at which the parts are laid at the full size (atPoint, atZeta);
    that a value of the parts' data has these two numbers is not said here. It is said by
    nowSharedBy_at_head (Johnson/Desc/ProofFile/Honest/K14/AtWiderShared.lean).

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.PointHeardAtShared
import Johnson.Desc.K14.Honest.ChainSteps
import Johnson.SendSim.At.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St p14Of beforePointOf)
open Desc.K14.Law (entryAt parU parO)

/-- Where challenges fit a list of declared rounds, the challenge at a round's number fits it. -/
theorem drawsFit_at : ∀ (pre : List Fmt.DeclaredRound) (r : Fmt.DeclaredRound) (more : List Fmt.DeclaredRound)
    (heard : List Fmt.Drawn), drawsFit (pre ++ r :: more) heard = true →
    ∃ d, (heard.drop pre.length).take 1 = [d] ∧ pre.length + 1 ≤ heard.length ∧ drawFit r d = true
  | [], _, _, [], h => by cases h
  | [], _, _, d :: ds, h =>
    ⟨d, rfl, Nat.succ_le_succ (Nat.zero_le _), (Bool.and_eq_true_iff.1 h).1⟩
  | _ :: _, _, _, [], h => by cases h
  | _ :: pre, r, more, _ :: ds, h => by
    obtain ⟨d, h1, h2, h3⟩ := drawsFit_at pre r more ds (Bool.and_eq_true_iff.1 h).2
    exact ⟨d, h1, Nat.succ_le_succ h2, h3⟩

/-- What heardFrom returns at a state that has heard a list and more. -/
theorem heardFrom_of {W' X' : Type} {t' : State W' X'} {heard more : List Fmt.Drawn} {i : Nat}
    {d : Fmt.Drawn} (ht : t'.heard = heard ++ more) (hd : (heard.drop i).take 1 = [d])
    (hl : i + 1 ≤ heard.length) : heardFrom t' i 1 = [d] := by
  unfold heardFrom
  rw [ht, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  exact hd

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

/-- **From the border 2 on the shared point is heard whole, also inside a member.** -/
theorem point_whole (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Nat} {k : Coins Bk}
    {s : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (b + 2) k s m E) :
    ∃ d : Fmt.Drawn, d.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kCol ∧
      ∀ (W' X' : Type) (t' : State W' X') (more : List Fmt.Drawn),
        t'.heard = m.st.heard ++ more → heardFrom t' 0 1 = [d] := by
  obtain ⟨d, rest, e, hl⟩ :=
    point_heard H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  refine ⟨d, hl.trans (Desc.K14.Law.entry_point _).1, fun W' X' t' more ht => ?_⟩
  exact heardFrom_of ht (by rw [e]; rfl) (by rw [e]; exact Nat.succ_le_succ (Nat.zero_le _))

/-- **From the border 8 on the challenge of "LIN zeta" is heard whole, also inside a member.** -/
theorem zeta_whole (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Nat} {k : Coins Bk}
    {s : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (b + 8) k s m E) :
    ∃ d : Fmt.Drawn, d.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kRow ∧
      ∀ (W' X' : Type) (t' : State W' X') (more : List Fmt.Drawn),
        t'.heard = m.st.heard ++ more → heardFrom t' 6 1 = [d] := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, l0, l1, l2, l3, l4, l5, l6, l7, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨-, r2, r3, r4, r5, r6, -, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU B.b1 B.b2 B.b3 B.b4
    B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
  have q := Desc.K14.Law.rounds_of_blocks _ _ _ _ _ _ _ _ _ B.made
  obtain ⟨r₁, hr1⟩ : ∃ r₁, B.b1.rounds = [r₁] := by
    have q1 := congrArg List.length q.1
    rw [List.length_map] at q1
    exact List.length_eq_one_iff.1 q1
  obtain ⟨r₇, hr7, hre⟩ : ∃ r₇, B.b7.rounds = [r₇] ∧
      r₇.entry = entryAt (p14Of Zp.p.chains (beforePointOf Np)) 2 := by
    have q7 := q.2.2
    cases hb7 : B.b7.rounds with
    | nil => rw [hb7] at q7; cases q7
    | cons a t =>
      rw [hb7] at q7
      cases t with
      | nil => exact ⟨a, rfl, (List.cons.inj q7).1⟩
      | cons a' t' => cases (List.cons.inj q7).2
  have hF : drawsFit (declsTo (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread.bs (b + 8)) m.st.heard = true := hA.2.1
  obtain ⟨pre, more, hlen, ed⟩ : ∃ pre more, pre.length = 6 ∧
      declsTo (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order
        wit table fixed n₁ n₂ Vd Rd Kp w).thread.bs (b + 8) = pre ++ r₇ :: more := by
    refine ⟨r₁ :: (VerifiableInference.Desc.K1.rounds
        (parU (p14Of Zp.p.chains (beforePointOf Np)) sentU) ++ (B.b4.rounds ++
      VerifiableInference.Desc.K1.rounds (parO (p14Of Zp.p.chains (beforePointOf Np))))),
      ((x8 :: tl).take b).flatMap (·.rounds), ?_, ?_⟩
    · rw [r4]
      rfl
    · unfold declsTo
      rw [e]
      simp only [List.take_succ_cons, List.flatMap_cons]
      rw [l0.rounds, l1.rounds, l2.rounds, l3.rounds, l4.rounds, l5.rounds, l6.rounds, l7.rounds,
        hr1, r2, r3, r5, r6, hr7]
      simp only [List.nil_append, List.cons_append, List.append_assoc]
      rfl
  rw [ed] at hF
  obtain ⟨d, h1, h2, h3⟩ := drawsFit_at pre r₇ more m.st.heard hF
  rw [hlen] at h1 h2
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h3
  refine ⟨d, ?_, fun W' X' t' more' ht => heardFrom_of ht h1 h2⟩
  rw [h3.1.1.1.1.1.1.1, hre]
  exact (Desc.K14.Law.entry_zeta _).1

/-- **The seeds of "send o_u" are whole** at every list of challenges that the member's rounds can
draw. -/
theorem seeds_whole_u (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∃ sentU, Desc.K14.withU (p14Of Zp.p.chains (beforePointOf Np)).S = some sentU ∧
      ∀ blk, (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
          n₂ Vd Rd Kp w).thread.bs[2]? = some blk →
        ∀ ds, drawsFit blk.rounds ds = true →
          K1.seedsFit (parU (p14Of Zp.p.chains (beforePointOf Np)) sentU) ds = true ∧
            ∀ s ∈ K1.seedsAt (parU (p14Of Zp.p.chains (beforePointOf Np)) sentU) ds,
              OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, l2, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨-, r2, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU B.b1 B.b2 B.b3 B.b4
    B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
  refine ⟨sentU, hQ.facts.goes, fun blk hb ds hd => ?_⟩
  rw [e] at hb
  obtain rfl : x2 = blk := Option.some.inj hb
  rw [l2.rounds, r2] at hd
  exact OnBytes.SendSim.At.draws_send _ hd

/-- **The seeds of "send o_omega" are whole** at every list of challenges that the member's rounds
can draw. -/
theorem seeds_whole_omega (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ blk, (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
        n₂ Vd Rd Kp w).thread.bs[5]? = some blk →
      ∀ ds, drawsFit blk.rounds ds = true →
        K1.seedsFit (parO (p14Of Zp.p.chains (beforePointOf Np))) ds = true ∧
          ∀ s ∈ K1.seedsAt (parO (p14Of Zp.p.chains (beforePointOf Np))) ds,
            OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, -, -, -, l5, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨-, -, -, -, r5, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU B.b1 B.b2 B.b3 B.b4
    B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
  intro blk hb ds hd
  rw [e] at hb
  obtain rfl : x5 = blk := Option.some.inj hb
  rw [l5.rounds, r5] at hd
  exact OnBytes.SendSim.At.draws_send _ hd

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.drawsFit_at
#print axioms ProofFile.Honest.K14.heardFrom_of
#print axioms ProofFile.Honest.K14.point_whole
#print axioms ProofFile.Honest.K14.zeta_whole
#print axioms ProofFile.Honest.K14.seeds_whole_u
#print axioms ProofFile.Honest.K14.seeds_whole_omega
