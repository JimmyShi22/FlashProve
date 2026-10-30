-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/LettersOmega.lean: Omega's member of the last chain's
proximity test held to its sender in the shared chain, at one run of the frame's walking prover.

  heard_at_pair        at a run, at a called part of the last chain and a called part of the shared
                       chain: what the first has heard is what the first chain heard (as many
                       challenges as the first chain has rounds), then what the second has heard,
                       then more
  take_front           a take that reaches past a list's front keeps that front
  omega_data_at_run    the data of Omega's member at a front that holds what the first chain and
                       the sender had heard, at the job jobW lays
                       (the number of "LIN point" moved by the first chain's rounds), is the
                       sender's data at the sender's own state, at the sender's own reader of rows
  omega_rows_of_data   what the member lays is laid of that data
  omega_rows_are_sent  at the sender's own coins the member's rows at message 0 are the sender's

By what. played_at_second, played_at_run (the walks of the run's three chains); walk_hears,
start_hears (what a walk's state has heard); runC_ends, runC_parts, seal_back (how many rounds the
first chain has); omega_one_input, omega_data_at_sender (OmegaMemberSent.lean); rows_below
(K12/LaidBelow.lean).

Limits.
- That the number of "LIN point" stands within what the sender had heard, and that the front holds
  all that the sender had heard, are the last two premises of omega_data_at_run's clause on fronts.
- omega_rows_are_sent takes the data's agreement and the coins' count as premises. The stretch that
  the frame carries is read against the sender's own purse by omega_held
  (AtFullSide/K12/HeldAtHeadW.lean).
- The one message 0. Message 1, o_sp, is no member of this test.
- A conditional at a run: nothing here shows that runC returns or that a part is called.
- Nothing on what a half plays. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.OmegaMemberSent
import Johnson.Desc.ProofFile.Honest.K12.LaidBelow
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtSecond
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun
import Johnson.Desc.ProofFile.Honest.WalkHeard
import Johnson.Desc.ProofFile.Honest.Law.RunC
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block FileDescription withEmptySealRound)
open ProofFile.Honest.K12.Light (askOf memOfSending rowsOfLaid rows_below played_at_second played_at_run)
open ProofFile.Honest.K14 (dueOf jobOmega laid offsetOf rowsOf)

/-- **What a called part of the last chain has heard, against what a called part of the shared
chain has heard.** -/
theorem heard_at_pair {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x c = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    {V₂ Pb₂ : Type} (σ₂ : Side F.S₂ F.Cl V₂ (Common W₀ Rc Ky) X₀ Pb₂)
    (u₂ : Member V₂ (Common W₀ Rc Ky) X₀ Pb₂) (pre₂ t₂ : List (Block F.S₂ F.Cl)) (i₂ : ℕ)
    (S₂ : StandsAt F.shared.blocksInOrder R.shared σ₂ u₂ pre₂ t₂ i₂)
    (hrun : runC F Bk P w₀ rc x c ρ = .ok r) (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hc₂ : r.called ⟨σ₂.block.place, u₂.number⟩ = true) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (m₂ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (h₁ e : List Fmt.Drawn),
      midAtW F Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      midSharedAtW F Bk P w₀ rc x c ρ ⟨σ₂.block.place, u₂.number⟩ = .ok (some m₂) ∧
      m.st.heard = h₁ ++ (m₂.st.heard ++ e) ∧
      h₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length := by
  obtain ⟨g₁, f₂, m, a₁, z₁, a₂, z₂, a₃, y, ha₁, hz₁, -, hm₁, ha₂, hz₂, l₂, hm₂, ha₃, hy, -, hym,
    hmid⟩ := played_at_second hpl hR hrun σ u pre t i _ S rfl hc
  obtain ⟨b₂, y₂, m₂, hb₂, hy₂, ly₂, hym₂, hmid₂⟩ :=
    played_at_run hpl hR hrun σ₂ u₂ pre₂ t₂ i₂ _ S₂ rfl hc₂
  have H₁ : g₁.st.heard = [] ++ z₁.laid.map (·.drawn) :=
    walk_hears _ _ _ _ _ _ (start_hears ha₁) hz₁ g₁ hm₁
  have H₂ : f₂.st.heard = [] ++ z₂.laid.map (·.drawn) :=
    walk_hears _ _ _ _ _ _ (start_hears ha₂) hz₂ f₂ hm₂
  have H₃ : m.st.heard = (g₁.st.heard ++ f₂.st.heard) ++ y.laid.map (·.drawn) :=
    walk_hears _ _ _ _ _ _ (start_hears ha₃) hy m hym
  have H₄ : m₂.st.heard = [] ++ y₂.laid.map (·.drawn) :=
    walk_hears _ _ _ _ _ _ (start_hears hb₂) hy₂ m₂ hym₂
  rw [List.nil_append] at H₁ H₂ H₄
  have hn : z₁.laid.length = (F.first.blocksInOrder.flatMap (·.rounds)).length := by
    obtain ⟨⟨g1, -, -⟩, -, -⟩ := runC_ends hrun
    obtain ⟨R', b₁, w₁, b₂', w₂, b₃, w₃, hR', hb₁, hw₁, hq, -, -, -, -, hr⟩ := runC_parts hrun
    rw [hR] at hR'
    cases hR'
    obtain rfl : b₁ = a₁ := Except.ok.inj (hb₁.symm.trans ha₁)
    obtain rfl : w₁ = z₁ := Except.ok.inj (hw₁.symm.trans hz₁)
    subst hr
    have hs₁ : (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
        roundsOf w₁.laid := seal_back hq
    have k := g1
    rw [show (withEmptySealRound (⟨(roundsOf w₁.laid).dropLast, w₁.cols⟩ : Fmt.View)).rounds =
      roundsOf w₁.laid from hs₁] at k
    exact (roundsOf_length _).symm.trans k
  rw [← l₂] at ly₂
  refine ⟨m, m₂, z₁.laid.map (·.drawn),
    (z₂.laid.drop ((pre₂.flatMap (·.rounds)).length + i₂)).map (·.drawn) ++
      y.laid.map (·.drawn), hmid, hmid₂, ?_, ?_⟩
  · have e₂ : z₂.laid.map (·.drawn) =
        (z₂.laid.take ((pre₂.flatMap (·.rounds)).length + i₂)).map (·.drawn) ++
          (z₂.laid.drop ((pre₂.flatMap (·.rounds)).length + i₂)).map (·.drawn) := by
      rw [← List.map_append, List.take_append_drop]
    rw [H₃, H₁, H₂, H₄, ly₂, e₂]
    simp only [List.append_assoc]
  · rw [List.length_map]
    exact hn

/-- A take that reaches past a list's front keeps that front. -/
theorem take_front {α : Type} (h e : List α) (q : Nat) (hq : h.length ≤ q) :
    ∃ e', (h ++ e).take q = h ++ e' := by
  induction h generalizing q with
  | nil => exact ⟨_, rfl⟩
  | cons a h ih =>
    cases q with
    | zero => simp at hq
    | succ q =>
      obtain ⟨e', he⟩ := ih q (by simpa using hq)
      exact ⟨e', by rw [List.cons_append, List.take_succ_cons, he, List.cons_append]⟩

/-- **The data of Omega's member at one run is the sender's.** A: the two sendings' public data. wt,
rd: the readers of the index and of the committer's values. At a front of the last chain that holds
what the sender had heard, at the job that jobW lays, the data is the sender's at its own state. -/
theorem omega_data_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x c = .ok R)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    {V₂ Pb₂ : Type} (σ₂ : Side F.S₂ F.Cl V₂ (Common W₀ Rc Ky) X₀ Pb₂)
    (u₂ : Member V₂ (Common W₀ Rc Ky) X₀ Pb₂) (pre₂ t₂ : List (Block F.S₂ F.Cl)) (i₂ : ℕ)
    (S₂ : StandsAt F.shared.blocksInOrder R.shared σ₂ u₂ pre₂ t₂ i₂)
    (hrun : runC F Bk P w₀ rc x c ρ = .ok r) (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hc₂ : r.called ⟨σ₂.block.place, u₂.number⟩ = true) (A : ProofFile.Honest.K14.SendPub)
    (wt : W₀ → Weights) (rd : Rc → TableRand) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (m₂ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      midAtW F Bk P w₀ rc x c ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      midSharedAtW F Bk P w₀ rc x c ρ ⟨σ₂.block.place, u₂.number⟩ = .ok (some m₂) ∧
      ∀ (fr : Front Y) (q k : Nat), fr.heard = m.st.heard.take q →
        (F.first.blocksInOrder.flatMap (·.rounds)).length + m₂.st.heard.length ≤ q →
        A.atPoint < m₂.st.heard.length →
        (jobOmega ⟨A.P, (F.first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩).data
            ⟨askOf A (fun w : Local W₀ Rc Xi Tr => wt w.w₀) (fun w => rd w.rc) m.st.input,
              fr.heard, ()⟩ k =
          (jobOmega A).data
            ⟨⟨rowsOf A.P.S (wt m₂.st.input.w₀) (rd m₂.st.input.rc)⟩, m₂.st.heard, ()⟩ k := by
  obtain ⟨m, m₂, h₁, e, hm, hm₂, hh, hl⟩ :=
    heard_at_pair hpl hR σ u pre t i S σ₂ u₂ pre₂ t₂ i₂ S₂ hrun hc hc₂
  obtain ⟨m', m₂', hm', hm₂', hask⟩ :=
    omega_one_input hpl hR σ u pre t i S σ₂ u₂ pre₂ t₂ i₂ S₂ hrun hc hc₂ A wt rd
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  obtain rfl : m₂' = m₂ := Option.some.inj (Except.ok.inj (hm₂'.symm.trans hm₂))
  refine ⟨m', m₂', hm', hm₂', fun fr q k hfr hq ha => ?_⟩
  rw [← hl] at hq ⊢
  obtain ⟨e', he'⟩ := take_front (h₁ ++ m₂'.st.heard) e q (by rw [List.length_append]; exact hq)
  have hfr' : fr.heard = h₁ ++ (m₂'.st.heard ++ e') := by
    rw [hfr, hh, ← List.append_assoc, he', List.append_assoc]
  rw [hfr', hask]
  exact omega_data_at_sender A.P A.atPoint _ h₁ _ e' k ha

/-- **What the member lays is laid of its data**, at the sender's own public numbers. -/
theorem omega_rows_of_data {W X : Type} (A : ProofFile.Honest.K14.SendPub) (n : Nat) (at_ : Addr) (k : Nat)
    (fs : Option Nat × Option Nat) (ask : W → ProofFile.Honest.K14.Ask) (w : W) (fr : Front X)
    (c : Stretch) (d : Nat → OnBytes.E)
    (h : (jobOmega ⟨A.P, n⟩).data ⟨ask w, fr.heard, ()⟩ k = d) :
    (memOfSending (jobOmega ⟨A.P, n⟩) at_ k fs ask none).rows w fr c =
      rowsOfLaid (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD k default).shape
        (laid (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD k default).shape d
          (fun i => OnBytes.E.ofTriple (OnBytes.Slice.ofE (c.e i))) ((jobOmega A).sort k)) := by
  subst h
  rfl

/-- **At the sender's own coins the member's rows at message 0 are the sender's rows.** t: the
sender's state. c₀: the sender's coins, at least the message's count. -/
theorem omega_rows_are_sent {W X : Type} (A : ProofFile.Honest.K14.SendPub) (n : Nat) (at_ : Addr)
    (fs : Option Nat × Option Nat) (ask : W → ProofFile.Honest.K14.Ask) (w : W) (fr : Front X)
    (t : State ProofFile.Honest.K14.Ask Unit)
    (hd : (jobOmega ⟨A.P, n⟩).data ⟨ask w, fr.heard, ()⟩ 0 = (jobOmega A).data t 0)
    {d : Due} (c₀ : Cs d)
    (hb : dueOf (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD 0 default).shape
      (.plain A.P.S.omegaRowsHigh) ≤ d.e) :
    (memOfSending (jobOmega ⟨A.P, n⟩) at_ 0 fs ask none).rows w fr (stretchOf c₀) =
      rowsOfLaid (jobOmega A).Q.codes ((jobOmega A).Q.sent.getD 0 default).shape
        ((jobOmega A).rows t (coinsE c₀).toArray 0) := by
  rw [omega_rows_of_data A n at_ 0 fs ask w fr _ _ hd]
  refine rows_below _ _ _ _ _ A.P.S.omegaRowsHigh fun i hi' => ?_
  have hj : i < d.e := Nat.lt_of_lt_of_le hi' hb
  have e₁ : (coinsE c₀).toArray.getD i OnBytes.zeroE =
      OnBytes.E.ofTriple (OnBytes.Slice.ofE (c₀.e ⟨i, hj⟩)) := by
    simp [coinsE, hj]
  have e₂ : (stretchOf c₀).e i = c₀.e ⟨i, hj⟩ := by
    simp only [stretchOf, dif_pos hj]
  have h0 : offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 = 0 := rfl
  show OnBytes.E.ofTriple (OnBytes.Slice.ofE ((stretchOf c₀).e i)) =
    (coinsE c₀).toArray.getD
      (offsetOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort 0 + i) OnBytes.zeroE
  rw [h0, Nat.zero_add, e₁, e₂]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.heard_at_pair
#print axioms ProofFile.Honest.K12.AtProof.take_front
#print axioms ProofFile.Honest.K12.AtProof.omega_data_at_run
#print axioms ProofFile.Honest.K12.AtProof.omega_rows_of_data
#print axioms ProofFile.Honest.K12.AtProof.omega_rows_are_sent
