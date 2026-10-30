-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/BehindAtFifty.lean: `BehindS` AT THE KIND K1's FIFTY LATER
MEMBERS, AT ProofFile's `lettersHead` WITH `b₀ = 339`, THE RIDERS `csHead` AND THE CLAUSE `fHeadJ`. The
columns hF (FormAtFifty.lean) · hK · h₀ · hst · hl of `owesS_head_form` at these numbers.

  `noL_cases`            the fifty numbers, by segment
  `k1_clauses_fifty`     the whole arm of `fHeadJ` behind the member's step
  `k1_behindS_fifty`     the law

Limits. Nothing shows that the member accepts. Nothing on any property. Full size, the format's
second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RidesAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.FormAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.ReadsHead
import Johnson.Desc.ProofFile.Honest.K1.Law.LaysT
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ
import Johnson.Desc.ProofFile.Honest.Thread.K1RelsDigits
import Johnson.Desc.ProofFile.Honest.Thread.HeadStays
import Johnson.Desc.ProofFile.Honest.Thread.AttGStays
import Johnson.Desc.ProofFile.Honest.Thread.LayOwnStays
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- **THE FIFTY NUMBERS.** -/
theorem noL_cases {l : ℕ} (hl : l < 25) (d : Bool) :
    (l < 24 ∧ d = false ∧ K1.noL l d = 14 * l + 5) ∨ (l < 24 ∧ d = true ∧ K1.noL l d = 14 * l + 7) ∨
      (l = 24 ∧ d = false ∧ K1.noL l d = 342) ∨ (l = 24 ∧ d = true ∧ K1.noL l d = 344) := by
  by_cases e : l = 24
  · subst e
    cases d
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  · have e' : l < 24 := by omega
    cases d
    · refine Or.inl ⟨e', rfl, ?_⟩
      simp only [K1.noL, IM.k1Ix, if_neg e, Bool.false_eq_true, if_false]
    · refine Or.inr (Or.inl ⟨e', rfl, ?_⟩)
      simp only [K1.noL, IM.k1Ix, if_neg e, if_true]

theorem k1_keeps_split (d : Bool) : d = false ∨ d = true := by
  cases d <;> simp

theorem k1_reads_of {l : ℕ} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l false) s s') :
    K1ReadsKeeps s s' := by
  rcases k1_keeps_cases k with ⟨-, c⟩ | ⟨e, -⟩
  · exact c.1
  · cases e

theorem k1_commit_of {l : ℕ} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l true) s s') :
    K1CommitKeeps s s' := by
  rcases k1_keeps_cases k with ⟨e, -⟩ | ⟨-, c⟩
  · cases e
  · exact c.1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
  {ν : Nat} {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}

/-- **THE WHOLE ARM OF `fHeadJ` BEHIND THE MEMBER's STEP.** -/
theorem k1_clauses_fifty (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) (d : Bool) {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hblk : cF.blocksInOrder[K1.noL l d]? = some blk)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (K1.noL l d) k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.Stepped blk k s m E ds y cols s') :
    fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD .K1 (IM.k1PlaceL l d) s s' := by
  have y0 : StepYes 0 blk s s' := stepYes_of_stepped _ hd hS
  have hp := place_fifty hl d
  have hpiece : (IM.k1PlaceL l d).piece ≠ 1 := by
    show IM.k1Ix l d + 1 ≠ 1
    cases d <;> simp only [IM.k1Ix] <;> split <;> simp
  refine ⟨⟨⟨⟨⟨(fHead_K1_later Zp cF G take P11 p12 P13 (l := l) rfl hpiece s s').2
      ⟨k1_clause_fifty h hl d hblk y0, k1_rels_fifty h hl d hblk y0⟩,
    formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd _ _ w hp
      (k1_form_fifty h H Q test carryX item n₁ n₂ 339 Vd _ _ w Said hl d hblk hT hS)⟩, ?_⟩,
    trivial⟩, trivial⟩, trivial⟩
  intro l' e hc
  obtain rfl : l = l' := Option.some.inj e
  cases d with
  | false =>
    exfalso
    have : IM.k1Ix l false + 1 = 6 ∨ IM.k1Ix l false + 1 = 7 := hc
    simp only [IM.k1Ix, Bool.false_eq_true, if_false] at this
    split at this <;> omega
  | true =>
    obtain ⟨new, h1, h2, h3⟩ :=
      k1_rels_digits h H Q test carryX item n₁ n₂ 339 Vd _ _ w hl hblk hT.1 hS
    refine ⟨new, h1, h2, fun mm kk ρ ho => h3 mm kk ρ ?_⟩
    rw [border_at hp] at ho
    exact ho

/-- **BEHIND A MEMBER OF THE FIFTY: THE FORM, THE RIDERS, THE CLAUSE.** -/
theorem k1_behindS_fifty (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) (d : Bool) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (K1.noL l d) := by
  have hp := place_fifty hl d
  have hn := noL_cases hl d
  have hn0 : (l < 24 ∧ K1.noL l d = 14 * l + 5) ∨ (l < 24 ∧ K1.noL l d = 14 * l + 7) ∨
      (l = 24 ∧ K1.noL l d = 342) ∨ (l = 24 ∧ K1.noL l d = 344) := by
    rcases hn with ⟨a, -, c⟩ | ⟨a, -, c⟩ | ⟨a, -, c⟩ | ⟨a, -, c⟩
    · exact Or.inl ⟨a, c⟩
    · exact Or.inr (Or.inl ⟨a, c⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨a, c⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, c⟩))
  have hnF : d = false → K1.noL l d ≠ 344 := by
    intro e
    rcases hn with ⟨a, -, c⟩ | ⟨a, e', c⟩ | ⟨-, -, c⟩ | ⟨-, e', c⟩
    · omega
    · rw [e] at e'; cases e'
    · omega
    · rw [e] at e'; cases e'
  clear hn
  have hK : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.keeps (K1.noL l d) s s' →
      K1KeepsAt (IM.k1PlaceL l d) s s' := fun s s' a => by
    have a' := (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').1 a
    have hpiece : (IM.k1PlaceL l d).piece ≠ 1 := by
      show IM.k1Ix l d + 1 ≠ 1
      cases d <;> simp only [IM.k1Ix] <;> split <;> simp
    exact ((fHead_K1_later Zp cF G take P11 p12 P13 (l := l) rfl hpiece s s').1 a'.1.1.1.1.1).1
  refine behindS_of_keeps_and _ Said
    (R₀ := fun c v s => 339 ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ 339 Vd _ _ w) ?_ ?_ ?_ ?_
  · intro blk hblk k s m E ds y cols s' hA hd hS
    exact ⟨k1_form_fifty h H Q test carryX item n₁ n₂ 339 Vd _ _ w Said hl d hblk hA hS,
      (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').2
        (k1_clauses_fifty h H Q test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl d hblk hA hd hS)⟩
  · intro blk hblk k s m E ds y cols s' hA hd hS hc
    have y0 : StepYes 0 blk s s' := stepYes_of_stepped _ hd hS
    have k1 := k1_keeps_rest (k1_clause_fifty h hl d hblk y0)
    have hri := hA.1.2.2.2.2.2.1
    have hc' : 339 ≤ K1.noL l d + 1 := hc
    have hfr : 339 ≤ K1.noL l d := by omega
    have e : s'.out = s.out := k1.2.1
    rw [e]
    exact hri.1 hfr
  · intro c hc h1 h2
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    · rcases k1_keeps_split d with rfl | rfl
      · exact staysBy_x_reads _ fun s s' a => k1_reads_of (hK s s' a)
      · exact staysBy_x_commit _ fun s s' a => k1_commit_of (hK s s' a)
    · rcases k1_keeps_split d with rfl | rfl
      · exfalso
        have a1 : 343 ≤ K1.noL l false := h1
        have a2 := hnF rfl
        omega
      · exact staysBy_t_commit _ fun s s' a => k1_commit_of (hK s s' a)
    · exfalso
      have a1 : 347 ≤ K1.noL l d := h1
      omega
    · exfalso
      have a1 : 346 ≤ K1.noL l d := h1
      omega
    · rcases k1_keeps_split d with rfl | rfl
      · exfalso
        have a1 : 344 ≤ K1.noL l false := h1
        have a2 := hnF rfl
        omega
      · exact staysBy_fold_commit _ fun s s' a => k1_commit_of (hK s s' a)
    · exfalso
      have a1 : 346 ≤ K1.noL l d := h1
      omega
    · exfalso
      have a1 : 346 ≤ K1.noL l d := h1
      omega
    · exfalso
      have a1 : 14 * g + 9 ≤ K1.noL l d := h1
      have a2 : K1.noL l d + 1 ≤ 14 * g + 9 := h2
      omega
    · refine staysBy_att_read _ (fun a => a.g) (R := R g) ?_
      rcases k1_keeps_split d with rfl | rfl
      · exact fun s s' a => attG_reads (k1_reads_of (hK s s' a))
      · exact fun s s' a => attG_commit (k1_commit_of (hK s s' a))
    · refine staysBy_own _ ?_
      rcases k1_keeps_split d with rfl | rfl
      · exact fun s s' a => layOwn_reads (k1_reads_of (hK s s' a))
      · exact fun s s' a => layOwn_commit (k1_commit_of (hK s s' a))
  · intro c hc e
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    · exfalso
      have a1 : 342 = K1.noL l d + 1 := e
      omega
    · have a1 : 343 = K1.noL l d + 1 := e
      have e24 : l = 24 := by omega
      subst e24
      have ed : d = false := by
        cases d
        · rfl
        · exfalso
          have e4 : K1.noL 24 true = 344 := rfl
          omega
      subst ed
      obtain ⟨Bs, base₀, O⟩ := h.laid.opened
      obtain ⟨e₀, Xl, reads, he, hX, hla⟩ := K1.k01_flat_reads h.scope h.reads O 24 (by decide)
      obtain ⟨-, l₀, hl₀, hk₀, -⟩ := IM.ground_named h.scope h.reads O.pub O.blank
      obtain rfl : l₀ = Xl := Option.some.inj (hl₀.symm.trans hX)
      exact k1_laysS_t _ Said _ _ _
        (fun blk hblk => by
          obtain rfl : e₀ = blk := Option.some.inj (he.symm.trans hblk)
          exact ⟨_, _, _, hla⟩)
        hX (by rw [hk₀]; decide) (by rw [hk₀]; decide)
    · exfalso
      have a1 : 347 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 346 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 344 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 346 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 346 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 14 * g + 9 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 14 * (2 * g + 1) + 4 = K1.noL l d + 1 := e
      omega
    · exfalso
      have a1 : 28 * g + 5 = K1.noL l d + 1 := e
      omega

/-- **WHAT RIDES PAST A MEMBER OF THE FIFTY RIDES, AT THE TERM's CLAUSE.** -/
theorem k1_ridesPastS_fifty_I (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (b₀ : Nat) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) {l : ℕ} (hl : l < 25) (d : Bool) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (K1.noL l d) := by
  have hpiece : (IM.k1PlaceL l d).piece ≠ 1 := by
    show IM.k1Ix l d + 1 ≠ 1
    cases d <;> simp only [IM.k1Ix] <;> split <;> simp
  refine k1_ridesPastS_fifty h H Q test carryX item n₁ n₂ b₀ Vd Rd _ w Said hl d
    (fun s s' a => (fHead_K1_later Zp cF G take P11 p12 P13 (l := l) rfl hpiece s s').1 a.1.1.1.1.1)
    fun e s s' a => ?_
  subst e
  have hc : (IM.k1PlaceL l true).piece = 6 ∨ (IM.k1PlaceL l true).piece = 7 := by
    show IM.k1Ix l true + 1 = 6 ∨ IM.k1Ix l true + 1 = 7
    simp only [IM.k1Ix, if_true]
    split <;> simp
  exact ⟨a.1.1.1.2 l rfl hc, a.1.1.1.1.2⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.noL_cases
#print axioms ProofFile.Honest.K1.k1_clauses_fifty
#print axioms ProofFile.Honest.K1.k1_behindS_fifty
#print axioms ProofFile.Honest.K1.k1_ridesPastS_fifty_I
