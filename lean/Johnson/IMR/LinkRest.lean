-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/LinkRest.lean: A TOOL FOR WHOEVER WALKS A LINK BY PLACE: the five
sub-protocols of a link l < 24 from the batching to the shutting (numbers 14 l + 9 to 14 l + 13 of
the flat list) keep every relation R on the verifier's state that
  is reflexive and transitive; a Quiet step keeps; the batching's maker keeps where the gathered
  claims do; and the three makers of "what closes a link" keep.
NOTHING IS ASKED OF THE SENDERS' DECISIONS: a sub-protocol that sends has no run of claims and no
run behind the batching, or Quiet ones.
  runs_guarded, runs_guardMark, runs_retype, runs_andThen, runs_same: RunsKeep
    (Johnson/Goal/Meaning/RunsKeep.lean) goes through the forms in which the proof file seats a
    lot's sub-protocol: each by striking the decision and calling the lemma on Whole.
  alone_runs, with_runs: so through the seats' two forms.
  hear_runs: every hearing sub-protocol of a link l < 24 has RunsKeep R: GIVEN AN ACCEPT OF THE
    LINK's FIRST ONE (at l ≥ 1 the seat's form has an arm "mute", which never accepts).
  rest_by: THE TOOL.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. No soundness.
-/
import Johnson.IMR.SeatKeeps
import Johnson.IMR.FoldTools
import Johnson.IMR.K1Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K5Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.FirstSeats
import Johnson.IMR.FrameSeat
import Johnson.IMR.FlatScope
import Johnson.IMR.CloseSeat
import Johnson.IMR.LinkSeat
import Johnson.Goal.Meaning.RunsKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

section Forms
variable {R : S → S → Prop}

theorem runs_guarded {C : Type} (hr : ∀ s, R s s) (same : S → S → Bool) (but : Place → Bool)
    {b : Block S C} (h : RunsKeep R b) : RunsKeep R (b.guarded same but) :=
  (guarded_whole same but (idle_whole hr h)).2

theorem runs_guardMark (hr : ∀ s, R s s) {b : Block S Cl} (h : RunsKeep R b) :
    RunsKeep R (ProofFile.guardMark b) := (guardMark_whole (idle_whole hr h)).2

theorem runs_retype {C C' : Type} (hr : ∀ s, R s s) {b : Block S C} (h : RunsKeep R b) :
    RunsKeep R (b.retype : Block S C') := (retype_whole (idle_whole hr h)).2

theorem runs_andThen {C : Type} (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (n : String) {p q : Block S C} (hp : RunsKeep R p) (hq : RunsKeep R q) :
    RunsKeep R (p.andThen n q) :=
  (Keeps.andThen_whole R ht n (idle p) (idle q) (idle_whole hr hp) (idle_whole hr hq)).2

theorem runs_same {C : Type} {b c : Block S C} (h : RunsKeep R b) (e2 : c.claims = b.claims)
    (e3 : c.after = b.after) : RunsKeep R c :=
  ⟨fun x hx => h.1 x (e2 ▸ hx), fun x hx => h.2 x (e3 ▸ hx)⟩

theorem alone_runs (hr : ∀ s, R s s) {b x : Block S Cl} {name : String} {a : Place}
    (la : IM.LaidAlone ProofFile.sameReply b x name a) (h : RunsKeep R x) : RunsKeep R b := by
  subst la
  exact runs_guarded hr _ _ (runs_same (runs_guardMark hr h) rfl rfl)

theorem with_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {b x q : Block S Cl}
    {name : String} {a : Place} (e : b = IM.seatedWith ProofFile.sameReply x q name a)
    (h : RunsKeep R x) (hq : RunsKeep R q) : RunsKeep R b := by
  subst e
  exact runs_guarded hr _ _ (runs_same (runs_andThen hr ht name
    (runs_same (runs_guardMark hr h) rfl rfl) (runs_guarded hr _ _ hq)) rfl rfl)

end Forms

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {R : S → S → Prop}

/-- A joined first place: the lot's sub-protocol's runs; "opened" has none. -/
theorem joined_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) {l : Nat}
    {b x : Block S Cl} {a : Place} (J : IM.Joined Z l b x a) (h : RunsKeep R x) :
    RunsKeep R b := by
  obtain ⟨fs, f, -, -, e⟩ := J
  exact with_runs hr ht e h (runs_guardMark hr (runs_retype hr (runs_none rfl rfl)))

theorem quiet_runs (hr : ∀ s, R s s) (hQ : ∀ s t, Quiet s t → R s t) {b x : Block S Cl}
    {a : Place} (la : IM.LaidAlone ProofFile.sameReply b x b.name a) (W : Whole Quiet x) :
    RunsKeep R b := alone_runs hr la (whole_mono hQ W).2

theorem runs_k3 (hr : ∀ s, R s s) (hQ : ∀ s t, Quiet s t → R s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} {b : Block S Cl} (eL : c.links[l]? = some Lk)
    (dg : Bool) (e : Lk.hear[if dg = true then 6 else 1]? = some b) : RunsKeep R b := by
  obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O l (by omega) dg
  have ix : IM.k3Ix l dg = if dg = true then 6 else 1 := by
    show (if dg = true then 6 else 1) + (if l = 24 then 1 else 0) = _
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  rw [ix] at e'
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  exact quiet_runs hr hQ la (theStated_quiet _ _ _ _ _ _ k3)

theorem runs_own (hr : ∀ s, R s s) (hQ : ∀ s t, Quiet s t → R s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} {b : Block S Cl} (eL : c.links[l]? = some Lk)
    (e : Lk.hear[2]? = some b) : RunsKeep R b := by
  rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
  · obtain ⟨Lk', b', y, eL', e', -, la, -⟩ := IM.k4_of hS hR O g (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la
      (whole_same (blockAtC_quiet { y.2 with k3Runs := true }) rfl (fun _ hx => hx) rfl)
  · obtain ⟨Lk', b', x, a, eL', e', k5, la, -⟩ := IM.k5_of hS hR O g (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (whole_same (k5AtN_quiet _ _ _ _ k5) rfl (fun _ hx => hx) rfl)

theorem runs_k8 (hr : ∀ s, R s s) (hQ : ∀ s t, Quiet s t → R s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} {b : Block S Cl} (eL : c.links[l]? = some Lk)
    (e : Lk.hear[4]? = some b) : RunsKeep R b := by
  rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
  · obtain ⟨Lk', b', Xl, hp, eL', e', -, la, -⟩ := IM.k8_of_layers hS hR O g (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (k8Whole_quiet _)
  · obtain ⟨Lk', b', Xl, a, eL', e', -, la, -⟩ := IM.k8_of_attention hS hR O g (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact quiet_runs hr hQ la (k8Whole_quiet _)

theorem runs_k1 (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} {b : Block S Cl} (eL : c.links[l]? = some Lk)
    {j : Nat} (hj' : j = 3 ∨ j = 5) (e : Lk.hear[j]? = some b) : RunsKeep R b := by
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    rcases hj' with rfl | rfl <;> split <;> cases (l == 0) <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) j hk
      (by rcases hj' with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_runs hr la (runs_retype hr (runs_andThen hr ht _ (runs_none rfl rfl)
      (whole_mono hQ (orLoud_whole fun b hb => readsQuietAt_quiet hb)).2))
  · exact alone_runs hr la (runs_retype hr (runs_none rfl rfl))

theorem runs_first (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} {b : Block S Cl} (eL : c.links[l]? = some Lk)
    (e : Lk.hear[0]? = some b) (hy : ∃ s rs gs t, b.decide s rs gs = .ok t) : RunsKeep R b := by
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨Lk', b', eL', e', J⟩ := IM.k1_first_sits hS hR O
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    exact joined_runs hr ht J (runs_retype hr (runs_none rfl rfl))
  · obtain ⟨Lk', b', x, eL', e', -, J, hx⟩ := IM.k2_link_sits hS hR O l (by omega) hl
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
    obtain ⟨s, rs, gs, t, d⟩ := hy
    obtain ⟨-, -, m, -, -, y1, -⟩ := J.yes d
    refine joined_runs hr ht J (runs_retype hr ?_)
    rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
    · obtain ⟨er, he⟩ := hm s (rs.take x.retype.rounds.length) (gs.take x.retype.openings)
      have y1' : x.decide s (rs.take x.retype.rounds.length) (gs.take x.retype.openings) =
          .ok m := y1
      rw [he] at y1'
      cases y1'
    · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
      · cases hn
      · rw [ex]
        exact runs_none rfl rfl
      · rw [ex]
        exact runs_none rfl rfl

/-- **Every hearing sub-protocol of a link l < 24**, given an accept of the first. -/
theorem hear_runs (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk)
    (hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t) :
    ∀ b ∈ Lk.hear, RunsKeep R b := by
  intro b hb
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hb
  have e : Lk.hear[j]? = some b := by rw [List.getElem?_eq_getElem hj, e']
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, eL', hlen, -⟩ := hfr l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  · exact runs_first hr ht hS hR O hl eL e (hy b e)
  · exact runs_k3 hr hQ hS hR O hl eL false e
  · exact runs_own hr hQ hS hR O hl eL e
  · exact runs_k1 hr ht hQ hS hR O hl eL (Or.inl rfl) e
  · exact runs_k8 hr hQ hS hR O hl eL e
  · exact runs_k1 hr ht hQ hS hR O hl eL (Or.inr rfl) e
  · exact runs_k3 hr hQ hS hR O hl eL true e

/-- **THE TOOL: numbers 14 l + 9 + n, n ≤ 4, of the flat list keep R.** -/
theorem rest_by (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t)
    (hBat : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R claims →
      Decides R (K9.batch K9.atS p claims))
    (hClo : ∀ (p : K9.Where) (Q : Close.Par), ∀ x ∈ K9.closeOf (Cl := Unit) p Q, Decides R x)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk)
    (hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t)
    {n : Nat} (hn : n ≤ 4) {b : Block S Cl} (hb : c.blocksInOrder[14 * l + 9 + n]? = some b) :
    Decides R b := by
  have hruns := hear_runs hr ht hQ hS hR O hl eL hy
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', f, bL, bB, bC, eL', hlen, -, -, -, -, -, -, -, -, iB, -, dB, -⟩ := hfr l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  obtain rfl | rfl | hn' : n = 0 ∨ n = 1 ∨ (2 ≤ n ∧ n ≤ 4) := by omega
  · obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, ifl, -⟩ := (IM.k9_of hS hR O).2 l (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    rw [hlen] at ifl
    obtain rfl := Option.some.inj (ifl.symm.trans hb)
    intro s rs gs t h
    exact hBat p (link_claims_runs hr ht Lk hruns) s rs gs t
      ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro k; cases k) s t rs gs).1 h).1
  · rw [hlen] at iB
    obtain rfl := Option.some.inj (iB.symm.trans hb)
    intro s rs gs t h
    rw [dB] at h
    exact link_behind_runs hr ht Lk hruns s t h
  · obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain ⟨k, hk⟩ : ∃ k, closeKinds[n - 2]? = some k := by
      obtain rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      all_goals exact ⟨_, rfl⟩
    obtain ⟨b', x, e1, e2, la⟩ := hall (n - 2) k hk
    have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
    rw [hlen, show 14 * l + 7 + 4 + (n - 2) = 14 * l + 9 + n by omega] at ib
    obtain rfl := Option.some.inj (ib.symm.trans hb)
    intro s rs gs t h
    have hk7 : (IM.cAt l (IM.subAt l) (n - 2) k).kind ≠ KindName.K7 := by
      obtain rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      all_goals
        obtain rfl := Option.some.inj hk
        intro q
        cases q
    exact hClo p Q x (List.mem_of_getElem? e2) s rs gs t ((IM.yes_alone la hk7 s t rs gs).1 h).1

end

#print axioms with_runs
#print axioms hear_runs
#print axioms rest_by

end Meaning.K2
