-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HeadRest.lean: A LIGHT FILE: TOOLS FOR WHOEVER WALKS THE HEAD's LINK
(number 24) BY PLACE, AND ONE TOOL AT EVERY LINK. It imports Johnson/IMR/LinkRest.lean and four
seats (Johnson/IMR/K2Seat.lean, K6Seat.lean, K7Seat.lean, K11Seat.lean) alone.
THE HEAD's LINK IN THE FLAT LIST: 337 "laid"; 338 to 346 its nine hearing sub-protocols (kinds K7
"H:1", K2 "H:2", K3, K6, K1, K8, K1, K3, K11); 347 the batching; 348 what runs behind it; 349 to 351
the one equation, the closing, the shutting; 352 "cleared".
  QuietSeat b: b is the seat's form "alone" (IM.LaidAlone), at a place of a kind other than K7, of a
    sub-protocol x with Whole Quiet x: x's decision and its runs are Quiet steps.
  head_k3, head_k6, head_k8, head_k11: five of the nine seats are such.
  head_k1_by, head_k1_runs: kind K1's two later sendings. head_k7_runs, head_k2_runs: "H:1", "H:2".
  hear_by24: hearing sub-protocols number 2 to 8 keep every transitive relation that a Quiet step
    and kind K1's later sending keep. hear_runs24: all nine have RunsKeep Rl, for Rl reflexive,
    transitive and kept by a Quiet step, GIVEN AN ACCEPT OF "H:2".
  rest_of_runs: A TOOL, GENERAL IN THE LINK (l < 25) AND IN THE NUMBER OF HEARING SUB-PROTOCOLS: the
    five from the batching to the shutting keep Rl, for Rl reflexive and transitive, kept by the
    batching's maker where the gathered claims keep it and by the three makers of "what closes a
    link", given RunsKeep Rl of the hearing ones.
    (Johnson/IMR/LinkRest.lean's rest_by says the like at l < 24, with the runs paid by its
      hear_runs.)
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. No soundness.
-/
import Johnson.IMR.LinkRest
import Johnson.IMR.K2Seat
import Johnson.IMR.K6Seat
import Johnson.IMR.K7Seat
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- b is the seat's form "alone", at a place of a kind other than K7, of a sub-protocol whose
decision and runs are Quiet steps. -/
def QuietSeat (b : Block S Cl) : Prop :=
  ∃ (x : Block S Cl) (a : Place), a.kind ≠ KindName.K7 ∧
    IM.LaidAlone ProofFile.sameReply b x b.name a ∧ Whole Quiet x

theorem QuietSeat.decides {Rl : S → S → Prop} (hQ : ∀ s t, Quiet s t → Rl s t) {b : Block S Cl}
    (q : QuietSeat b) : Decides Rl b := by
  obtain ⟨x, a, hk, la, W⟩ := q
  exact fun s rs gs t h => hQ _ _ (W.1 s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1)

theorem QuietSeat.runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s) (hQ : ∀ s t, Quiet s t → Rl s t)
    {b : Block S Cl} (q : QuietSeat b) : RunsKeep Rl b := by
  obtain ⟨x, a, -, la, W⟩ := q
  exact quiet_runs hr hQ la W

/-- Kind K3's two seats: number 2 (the calls) and number 7 (the digits). -/
theorem head_k3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (dg : Bool)
    (e : Lk.hear[if dg = true then 7 else 2]? = some b) : QuietSeat b := by
  obtain ⟨Lk', b', x, eL', e', k3, la⟩ := IM.k3_of hS hR O 24 (by omega) dg
  have ix : IM.k3Ix 24 dg = if dg = true then 7 else 2 := by cases dg <;> rfl
  rw [ix] at e'
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  exact ⟨x, _, (by intro k; cases k), la, theStated_quiet _ _ _ _ _ _ k3⟩

/-- Kind K6's seat: number 3. -/
theorem head_k6 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (e : Lk.hear[3]? = some b) : QuietSeat b := by
  obtain ⟨Lk', b', x, ms, eL', e', -, k6, la, -⟩ := IM.k6_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  exact ⟨x, _, (by intro k; cases k), la, seatedClaims_quiet k6⟩

/-- Kind K8's seat: number 5. -/
theorem head_k8 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (e : Lk.hear[5]? = some b) : QuietSeat b := by
  obtain ⟨Lk', b', Xl, eL', e', -, la, -⟩ := IM.k8_of_head hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  exact ⟨_, _, (by intro k; cases k), la, k8Whole_quiet _⟩

/-- Kind K11's seat: number 8. -/
theorem head_k11 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (e : Lk.hear[8]? = some b) : QuietSeat b := by
  obtain ⟨Lk', b', eL', e', la, -⟩ := IM.k11_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  exact ⟨_, _, (by intro k; cases k), la,
    whole_same (headMerge11_quiet (K11.parAt Z "H.8.call" Bs.G₀)) rfl (fun _ hx => hx) rfl⟩

/-- Kind K1's two later sendings, number 4 and number 6: the decision. -/
theorem head_k1_by {Rl : S → S → Prop} (ht : ∀ a b c, Rl a b → Rl b c → Rl a c)
    (hQ : ∀ s t, Quiet s t → Rl s t)
    (hC : ∀ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (s v : S)
      (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v → Rl s v)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) {i : Nat} (hi : i = 4 ∨ i = 6)
    (e : Lk.hear[i]? = some b) : Decides Rl b := by
  have hk : (kindsBeforeBatching (IM.subAt 24) (24 == 0))[i]? = some KindName.K1 := by
    rcases hi with rfl | rfl <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O 24 (IM.subAt 24) (IM.subs_scope hS hR O 24 (by omega)) i hk
      (by rcases hi with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  intro s rs gs t h
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · have h' : (IM.k1Reads Z Bs.G₀ 24 Xl pr reads).decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain ⟨v, a1, a2⟩ := andThen_yes h'
    exact ht _ _ _ (hC _ _ _ _ s v _ _ a1)
      (hQ _ _ ((orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2))
  · exact hC _ _ _ _ s t rs gs ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1

/-- Kind K1's two later sendings: the runs. -/
theorem head_k1_runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (ht : ∀ a b c, Rl a b → Rl b c → Rl a c) (hQ : ∀ s t, Quiet s t → Rl s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) {i : Nat} (hi : i = 4 ∨ i = 6)
    (e : Lk.hear[i]? = some b) : RunsKeep Rl b := by
  have hk : (kindsBeforeBatching (IM.subAt 24) (24 == 0))[i]? = some KindName.K1 := by
    rcases hi with rfl | rfl <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O 24 (IM.subAt 24) (IM.subs_scope hS hR O 24 (by omega)) i hk
      (by rcases hi with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · exact alone_runs hr la (runs_retype hr (runs_andThen hr ht _ (runs_none rfl rfl)
      (whole_mono hQ (orLoud_whole fun b hb => readsQuietAt_quiet hb)).2))
  · exact alone_runs hr la (runs_retype hr (runs_none rfl rfl))

/-- The place "H:1", number 0: the runs. -/
theorem head_k7_runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (ht : ∀ a b c, Rl a b → Rl b c → Rl a c) (hQ : ∀ s t, Quiet s t → Rl s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (e : Lk.hear[0]? = some b) :
    RunsKeep Rl b := by
  obtain ⟨Lk', b', eL', e', J, -⟩ := IM.k7_sits hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  refine joined_runs hr ht J (runs_retype hr ?_)
  unfold IM.k7Block
  exact runs_andThen hr ht _ (runs_guarded hr _ _ (runs_none rfl rfl))
    (whole_mono hQ (k7Of_quiet _ _)).2

/-- The place "H:2", number 1: the runs, GIVEN AN ACCEPT (the seat's form has an arm "mute", which
never accepts). -/
theorem head_k2_runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} (eL : c.links[24]? = some Lk) (e : Lk.hear[1]? = some b)
    (hy : ∃ s rs gs t, b.decide s rs gs = .ok t) : RunsKeep Rl b := by
  obtain ⟨Lk', b', x, eL', e', -, la, hx⟩ := IM.k2_head_of hS hR O
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  obtain ⟨s, rs, gs, t, d⟩ := hy
  have y1 : x.decide s rs gs = .ok t := ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 d).1
  refine alone_runs hr la (runs_retype hr ?_)
  rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
  · obtain ⟨er, he⟩ := hm s rs gs
    rw [he] at y1
    cases y1
  · rcases h3 with ⟨hn, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases hn
    · rw [ex]
      exact runs_none rfl rfl
    · rw [ex]
      exact runs_none rfl rfl

/-- **Hearing sub-protocols number 2 to 8 of the head's link keep every transitive relation that a
Quiet step and kind K1's later sending keep.** -/
theorem hear_by24 {Rl : S → S → Prop} (ht : ∀ a b c, Rl a b → Rl b c → Rl a c)
    (hQ : ∀ s t, Quiet s t → Rl s t)
    (hC : ∀ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (s v : S)
      (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v → Rl s v)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {j : Nat} (h2 : 2 ≤ j) (h8 : j ≤ 8) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[24]? = some Lk) (e : Lk.hear[j]? = some b) : Decides Rl b := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  · exact (head_k3 hS hR O eL false e).decides hQ
  · exact (head_k6 hS hR O eL e).decides hQ
  · exact head_k1_by ht hQ hC hS hR O eL (Or.inl rfl) e
  · exact (head_k8 hS hR O eL e).decides hQ
  · exact head_k1_by ht hQ hC hS hR O eL (Or.inr rfl) e
  · exact (head_k3 hS hR O eL true e).decides hQ
  · exact (head_k11 hS hR O eL e).decides hQ

/-- **The runs of every hearing sub-protocol of the head's link keep Rl** (reflexive, transitive,
kept by a Quiet step), given an accept of the place "H:2". -/
theorem hear_runs24 {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (ht : ∀ a b c, Rl a b → Rl b c → Rl a c) (hQ : ∀ s t, Quiet s t → Rl s t)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    (eL : c.links[24]? = some Lk)
    (hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t) :
    ∀ b ∈ Lk.hear, RunsKeep Rl b := by
  intro b hb
  obtain ⟨j, hj, e'⟩ := List.getElem_of_mem hb
  have e : Lk.hear[j]? = some b := by rw [List.getElem?_eq_getElem hj, e']
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', -, -, -, -, eL', hlen, -⟩ := hfr 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_pos rfl] at hlen
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  · exact head_k7_runs hr ht hQ hS hR O eL e
  · exact head_k2_runs hr hS hR O eL e (hy b e)
  · exact (head_k3 hS hR O eL false e).runs hr hQ
  · exact (head_k6 hS hR O eL e).runs hr hQ
  · exact head_k1_runs hr ht hQ hS hR O eL (Or.inl rfl) e
  · exact (head_k8 hS hR O eL e).runs hr hQ
  · exact head_k1_runs hr ht hQ hS hR O eL (Or.inr rfl) e
  · exact (head_k3 hS hR O eL true e).runs hr hQ
  · exact (head_k11 hS hR O eL e).runs hr hQ

/-- **A TOOL, AT EVERY LINK l < 25: numbers 14 l + (the number of hearing sub-protocols) + 2 + n,
n ≤ 4, of the flat list (the batching, what runs behind it, the one equation, the closing, the
shutting) keep Rl**: reflexive, transitive, kept by the batching's maker where the gathered claims
keep it and by the three makers of "what closes a link"; given that the hearing sub-protocols' runs
keep it. -/
theorem rest_of_runs {Rl : S → S → Prop} (hr : ∀ s, Rl s s)
    (ht : ∀ a b c, Rl a b → Rl b c → Rl a c)
    (hBat : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl Rl claims →
      Decides Rl (K9.batch K9.atS p claims))
    (hClo : ∀ (p : K9.Where) (Q : Close.Par), ∀ x ∈ K9.closeOf (Cl := Unit) p Q, Decides Rl x)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk) (hruns : ∀ b ∈ Lk.hear, RunsKeep Rl b)
    {n : Nat} (hn : n ≤ 4) {b : Block S Cl}
    (hb : c.blocksInOrder[14 * l + Lk.hear.length + 2 + n]? = some b) : Decides Rl b := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', f, bL, bB, bC, eL', -, -, -, -, -, -, -, -, -, iB, -, dB, -⟩ := hfr l hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl | rfl | hn' : n = 0 ∨ n = 1 ∨ (2 ≤ n ∧ n ≤ 4) := by omega
  · obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, ifl, -⟩ := (IM.k9_of hS hR O).2 l hl
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain rfl := Option.some.inj (ifl.symm.trans hb)
    intro s rs gs t h
    exact hBat p (link_claims_runs hr ht Lk hruns) s rs gs t
      ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro k; cases k) s t rs gs).1 h).1
  · rw [show 14 * l + Lk.hear.length + 2 + 1 = 14 * l + Lk.hear.length + 3 by omega] at hb
    obtain rfl := Option.some.inj (iB.symm.trans hb)
    intro s rs gs t h
    rw [dB] at h
    exact link_behind_runs hr ht Lk hruns s t h
  · obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l hl
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain ⟨k, hk⟩ : ∃ k, closeKinds[n - 2]? = some k := by
      obtain rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      all_goals exact ⟨_, rfl⟩
    obtain ⟨b', x, e1, e2, la⟩ := hall (n - 2) k hk
    have ib := IM.close_numbers hS hR O hl eL e1
    rw [show 14 * l + Lk.hear.length + 4 + (n - 2) = 14 * l + Lk.hear.length + 2 + n by
      omega] at ib
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

#print axioms hear_by24
#print axioms hear_runs24
#print axioms rest_of_runs

end Meaning.K2
