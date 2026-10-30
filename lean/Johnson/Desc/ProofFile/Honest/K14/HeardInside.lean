-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/HeardInside.lean: kind K14: THE SILENT DEFAULTS OF
Honest/K14/HeardAtShared.lean ARE NOT TAKEN AT THE STATES THAT THE FRAME's OWN PLAY REACHES INSIDE A
MEMBER OF THE SHARED CHAIN, and at the very terms that the parts read. It joins that file's
sentences to the frame. Statements with their proofs; no definition.

A state inside a member is said by InsideOf (Honest/Law/Inside.lean): it is reached by the frame's
play over the member's first n rounds from a state at which the thread's invariant holds in front of
the member. A part is handed that state narrowed to its own types (State.narrow, Honest/Frame.lean),
which keeps what was heard.

  heard_inside
      inside a member the run has heard what the stand in front had heard, and then the challenges
      of the member's first n rounds, which fit these rounds
  point_inside
      **inside a member at the number 2 or later**: heardFrom at the number 0, at the state as a
      part is handed it, returns [d], and d holds kCol field elements
  zeta_inside
      **inside a member at the number 8 or later** the like for "LIN zeta": the number 6, kRow
      elements
  point_zeta_inside_any
      the two at once, at whatever state has heard just what the state inside the member has heard:
      so also at the state that the part at "SPLIT" builds for itself out of the list heard
  jobOmega_par
      the parameters of "send o_omega" are those of which seeds_whole_omega speaks (for "send o_u":
      the library's jobU_par, Honest/K14/SendingsShows.lean)
  answer_round_fits, seeds_of_first
      off a challenge that fits a sending's first round the seeds are whole: draws_send with the
      empty challenge at the answers' round, which draws nothing
  seeds_inside
      behind the first round of a member whose rounds are a sending's: the last challenge heard is
      that round's own (the library's lately_one, Honest/K14/SendingsViaPaid.lean), and the term
      cutSeeds … (elems (t.lately 1)) is the list of seeds off it; it holds just the seeds'
      elements, and no seed's factor is 0
  seeds_inside_u, seeds_inside_omega
      **that at "send o_u" and at "send o_omega"**, at the very term that the part's second move
      reads (sendingPart, Honest/K14/Sendings.lean)

Limits. h is a hypothesis: P5J.AtMgA (Johnson/P5J/MgAtAll.lean), at the hash OnBytes.secondHashFunction. That
the invariant holds at any state of any run, and so that any state is inside a member, is not shown.
The numbers 0 and 6 are those at which the library lays the parts under that hypothesis
(nowSharedBy_at_head, Honest/K14/AtWiderShared.lean).
That the walk of a run hands a part just such a state is the library's thread_in_chain
(Honest/Law/Inside.lean), under its own premises; it is not called here.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.HeardAtShared
import Johnson.Desc.ProofFile.Honest.Law.Inside
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St p14Of beforePointOf)
open Desc.K14.Law (parU parO)
open VerifiableInference.Desc.K1 (cutSeeds)

/-- **Inside a member the run has heard what the stand in front had heard, and the challenges of the
member's first n rounds.** -/
theorem heard_inside {S Cl V W Y Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : Nat}
    {hs : List (Placed V W Y)} {b : Block S Cl} {A : Coins Bk → S → Mid W Y → Env → Prop} {n : Nat}
    {k : Coins Bk} {m : Mid W Y} {E : Env} (hI : InsideOf φ Bk chain hs b A n k m E) :
    ∃ s m₀ E₀ ds, A k s m₀ E₀ ∧ drawsFit (b.rounds.take n) ds = true ∧
      m.st.heard = m₀.st.heard ++ ds := by
  obtain ⟨s, m₀, E₀, l, ds, y, hA, -, hd, hp, rfl, -⟩ := hI
  exact ⟨s, m₀, E₀, ds, hA, hd, play_heard _ _ _ _ _ hp⟩

/-- The parameters of "send o_omega". -/
theorem jobOmega_par (Q : Desc.K14.P14) (a : Nat) : (jobOmega ⟨Q, a⟩).Q = parO Q := rfl

/-- The answers' round draws nothing: the empty challenge fits it. -/
theorem answer_round_fits (P : VerifiableInference.Desc.K1.Par) :
    drawFit { entry := VerifiableInference.Desc.K1.answerEntry P } ⟨[], [], [], none⟩ = true := rfl

/-- **Off a challenge that fits a sending's first round the seeds are whole.** -/
theorem seeds_of_first (P : VerifiableInference.Desc.K1.Par) (d : Fmt.Drawn)
    (hd : drawFit { entry := VerifiableInference.Desc.K1.seedEntry P } d = true) :
    cutSeeds P.coordinates P.seeds (elems [d]) = K1.seedsAt P [d] ∧
      K1.seedsFit P [d] = true ∧ ∀ s ∈ K1.seedsAt P [d], OnBytes.Slice.readE s.2 ≠ 0 := by
  have h2 : drawsFit (VerifiableInference.Desc.K1.rounds P) [d, ⟨[], [], [], none⟩] = true := by
    show (drawFit { entry := VerifiableInference.Desc.K1.seedEntry P } d &&
      (drawFit { entry := VerifiableInference.Desc.K1.answerEntry P } ⟨[], [], [], none⟩ &&
        true)) = true
    rw [hd, answer_round_fits]
    rfl
  obtain ⟨a, b⟩ := OnBytes.SendSim.At.draws_send P h2
  refine ⟨?_, a, b⟩
  show cutSeeds P.coordinates P.seeds (d.elems.map OnBytes.E.ofTriple ++ []) = _
  rw [List.append_nil]
  rfl

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

/-- **Inside a member at the number 2 or later the shared point is heard whole**, at the state as a
part is handed it. -/
theorem point_inside (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {V Pb : Type}
    {φ : Face V (Common W₀ Rc OnBytes.TableKey) Pb} {chain : Nat}
    {hs : List (Placed V (Common W₀ Rc OnBytes.TableKey) X₀)} {blk : Block St ProofFile.Cl} {b n : Nat}
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hI : InsideOf φ Bk chain hs blk (Thr (SharedThread.lettersShared Zp Np cF H N Mg shape
      nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).thread (b + 2)) n k m E) :
    ∃ d : Fmt.Drawn, d.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kCol ∧
      ∀ (W' Y' : Type) (f : Common W₀ Rc OnBytes.TableKey → W') (g : X₀ → Y'),
        heardFrom (m.st.narrow f g) 0 1 = [d] := by
  obtain ⟨s, m₀, E₀, ds, hA, -, e⟩ := heard_inside hI
  obtain ⟨d, hl, hall⟩ :=
    point_whole H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  exact ⟨d, hl, fun W' Y' f g => hall W' Y' _ ds e⟩

/-- **Inside a member at the number 8 or later the challenge of "LIN zeta" is heard whole**, at the
state as a part is handed it. -/
theorem zeta_inside (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {V Pb : Type}
    {φ : Face V (Common W₀ Rc OnBytes.TableKey) Pb} {chain : Nat}
    {hs : List (Placed V (Common W₀ Rc OnBytes.TableKey) X₀)} {blk : Block St ProofFile.Cl} {b n : Nat}
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hI : InsideOf φ Bk chain hs blk (Thr (SharedThread.lettersShared Zp Np cF H N Mg shape
      nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).thread (b + 8)) n k m E) :
    ∃ d : Fmt.Drawn, d.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kRow ∧
      ∀ (W' Y' : Type) (f : Common W₀ Rc OnBytes.TableKey → W') (g : X₀ → Y'),
        heardFrom (m.st.narrow f g) 6 1 = [d] := by
  obtain ⟨s, m₀, E₀, ds, hA, -, e⟩ := heard_inside hI
  obtain ⟨d, hl, hall⟩ :=
    zeta_whole H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  exact ⟨d, hl, fun W' Y' f g => hall W' Y' _ ds e⟩

/-- **The two at once, at whatever state has heard just what the state inside the member has
heard**: so also at the state that the part at "SPLIT" builds for itself out of the list heard
(splitValue, Honest/K14/Parts.lean). -/
theorem point_zeta_inside_any (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {V Pb : Type}
    {φ : Face V (Common W₀ Rc OnBytes.TableKey) Pb} {chain : Nat}
    {hs : List (Placed V (Common W₀ Rc OnBytes.TableKey) X₀)} {blk : Block St ProofFile.Cl} {b n : Nat}
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hI : InsideOf φ Bk chain hs blk (Thr (SharedThread.lettersShared Zp Np cF H N Mg shape
      nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).thread (b + 8)) n k m E) :
    ∃ d₀ d₆ : Fmt.Drawn, d₀.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kCol ∧
      d₆.elems.length = (p14Of Zp.p.chains (beforePointOf Np)).S.kRow ∧
      ∀ (W' Y' : Type) (t' : State W' Y'), t'.heard = m.st.heard →
        heardFrom t' 0 1 = [d₀] ∧ heardFrom t' 6 1 = [d₆] := by
  obtain ⟨s, m₀, E₀, ds, hA, -, e⟩ := heard_inside hI
  obtain ⟨d₀, hl₀, hall₀⟩ := point_whole (b := b + 6) H N Mg shape nothingLeft order wit table fixed
    n₁ n₂ Vd Rd Kp w h hA
  obtain ⟨d₆, hl₆, hall₆⟩ :=
    zeta_whole H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h hA
  exact ⟨d₀, d₆, hl₀, hl₆, fun W' Y' t' ht =>
    ⟨hall₀ W' Y' t' ds (ht.trans e), hall₆ W' Y' t' ds (ht.trans e)⟩⟩

/-- **Behind a member's first round, where its rounds are a sending's: the term that the part's
second move reads is the whole list of seeds.** hr: the member's rounds. -/
theorem seeds_inside {S Cl V W Y Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : Nat}
    {hs : List (Placed V W Y)} {blk : Block S Cl} {A : Coins Bk → S → Mid W Y → Env → Prop}
    {k : Coins Bk} {m : Mid W Y} {E : Env} (P : VerifiableInference.Desc.K1.Par)
    (hr : blk.rounds = VerifiableInference.Desc.K1.rounds P)
    (hI : InsideOf φ Bk chain hs blk A 1 k m E) :
    ∃ d : Fmt.Drawn, ∀ (W' Y' : Type) (f : W → W') (g : Y → Y'),
      cutSeeds P.coordinates P.seeds (elems ((m.st.narrow f g).lately 1)) = K1.seedsAt P [d] ∧
        K1.seedsFit P [d] = true ∧ ∀ s ∈ K1.seedsAt P [d], OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨s, m₀, E₀, ds, -, hd, e⟩ := heard_inside hI
  rw [hr] at hd
  have hd' : drawsFit [{ entry := VerifiableInference.Desc.K1.seedEntry P }] ds = true := hd
  cases ds with
  | nil => cases hd'
  | cons d t =>
    cases t with
    | cons _ _ =>
      have h0 := (Bool.and_eq_true_iff.1 hd').2
      cases h0
    | nil =>
      refine ⟨d, fun W' Y' f g => ?_⟩
      have hl : (m.st.narrow f g).lately 1 = [d] := by
        show ({ input := f m.st.input, heard := m.st.heard, own := g m.st.own } :
          State W' Y').lately 1 = [d]
        rw [e]
        exact lately_one _ _ _ _
      rw [hl]
      exact seeds_of_first P d (Bool.and_eq_true_iff.1 hd').1

/-- **Behind the first round of "send o_u".** -/
theorem seeds_inside_u (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (a : Nat) {V Pb : Type}
    {φ : Face V (Common W₀ Rc OnBytes.TableKey) Pb} {chain : Nat}
    {hs : List (Placed V (Common W₀ Rc OnBytes.TableKey) X₀)} {blk : Block St ProofFile.Cl}
    (hb : (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread.bs[2]? = some blk)
    {A : Coins Bk → St → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Env → Prop}
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hI : InsideOf φ Bk chain hs blk A 1 k m E) :
    ∃ d : Fmt.Drawn, ∀ (W' Y' : Type) (f : Common W₀ Rc OnBytes.TableKey → W') (g : X₀ → Y'),
      cutSeeds (jobU ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q.coordinates
          (jobU ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q.seeds
          (elems ((m.st.narrow f g).lately 1)) =
        K1.seedsAt (jobU ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d] ∧
      K1.seedsFit (jobU ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d] = true ∧
      ∀ s ∈ K1.seedsAt (jobU ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d],
        OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, l2, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨-, r2, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU B.b1 B.b2 B.b3 B.b4
    B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
  rw [e] at hb
  obtain rfl : x2 = blk := Option.some.inj hb
  rw [jobU_par hQ.facts.goes a]
  exact seeds_inside _ (l2.rounds.trans r2) hI

/-- **Behind the first round of "send o_omega".** -/
theorem seeds_inside_omega (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (a : Nat)
    {V Pb : Type} {φ : Face V (Common W₀ Rc OnBytes.TableKey) Pb} {chain : Nat}
    {hs : List (Placed V (Common W₀ Rc OnBytes.TableKey) X₀)} {blk : Block St ProofFile.Cl}
    (hb : (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread.bs[5]? = some blk)
    {A : Coins Bk → St → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Env → Prop}
    {k : Coins Bk} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E : Env}
    (hI : InsideOf φ Bk chain hs blk A 1 k m E) :
    ∃ d : Fmt.Drawn, ∀ (W' Y' : Type) (f : Common W₀ Rc OnBytes.TableKey → W') (g : X₀ → Y'),
      cutSeeds (jobOmega ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q.coordinates
          (jobOmega ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q.seeds
          (elems ((m.st.narrow f g).lately 1)) =
        K1.seedsAt (jobOmega ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d] ∧
      K1.seedsFit (jobOmega ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d] = true ∧
      ∀ s ∈ K1.seedsAt (jobOmega ⟨p14Of Zp.p.chains (beforePointOf Np), a⟩).Q [d],
        OnBytes.Slice.readE s.2 ≠ 0 := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_at_head h
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, e, -, -, -, -, -, l5, -⟩ :=
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).bs B
  obtain ⟨-, -, -, -, r5, -⟩ := Desc.K14.Honest.blocks_rounds _ sentU B.b1 B.b2 B.b3 B.b4
    B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
  rw [e] at hb
  obtain rfl : x5 = blk := Option.some.inj hb
  rw [jobOmega_par]
  exact seeds_inside _ (l5.rounds.trans r5) hI

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.heard_inside
#print axioms ProofFile.Honest.K14.jobOmega_par
#print axioms ProofFile.Honest.K14.answer_round_fits
#print axioms ProofFile.Honest.K14.seeds_of_first
#print axioms ProofFile.Honest.K14.point_inside
#print axioms ProofFile.Honest.K14.zeta_inside
#print axioms ProofFile.Honest.K14.point_zeta_inside_any
#print axioms ProofFile.Honest.K14.seeds_inside
#print axioms ProofFile.Honest.K14.seeds_inside_u
#print axioms ProofFile.Honest.K14.seeds_inside_omega
