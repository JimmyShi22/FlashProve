-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FormsMade.lean: THE SUB-PROTOCOL AT THE OUTPUT HEAD MAKES THE PUBLIC TESTS
formsInT 24 4 "own" AND formsInT 24 4 "join" ("every form that the run's reader gives names only
what is there, or a cell of an array that the segment's next sending will bring"), AT THE COMPOSED
MEANING OF THE OPEN CLAIMS (Johnson/Desc/Sound/MgAll.lean: mgAll). Statements and proofs.

By two lemmas of K6's files: Law/K6FormsInT.lean's k6_formsInT (the test accepts where the silent
reader answers) and Law/SilentAnswers.lean's four_answer (it answers behind the accept). What these
two ask of what the lookup on the calls heard and of its debts comes from the public sentence "what
the lookup on the calls left" (Law/K6LeftSays.lean: left_says).

WHAT IT IS NOT. Implications. Nothing on soundness. A TOTALITY: it says that a later test of the
verifier's will find what it looks for; nothing on what the forms are worth. PREMISES THAT NOBODY
PAYS HERE: ON THE IOP AS WRITTEN IN LEAN: KS, KB (which runs stand under the four names, both
ways), readers · ON THE STATE IN FRONT: K6Left, the sentence (left), Z1 and hwo (no tables are laid;
the merge has laid no end value: no clause of the table's promise says these two), tree (the reads'
array has one row and the planned width) · ON THE STATE BEHIND: K6After, hcov (the covered positions
are there), haK, hMask, hEnt (an entry of row 0 of the reads' array below the planned width passes
the table's test on entries) · ON PUBLIC PARAMETERS ALONE: planB, hB and hRB (two tests with code),
hnU, h4, hpub (five facts on numbers). No values are shown here at which the premises hold
together.

  made_forms       the test accepts at each of the four runs behind an accept.
  made_own, made_join   MAIN: the two public tests.

LETTERS. No letter stands under "there is" in a conclusion. In premises: tree's G, tr: pinned by
the state's ledger and its list of arrays; hcov's cov: pinned by the equation.

-/
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.Desc.Kinds.Law.K6LeftSays
import Johnson.Desc.Kinds.Law.SilentAnswers
import Johnson.Desc.Kinds.Law.KeepsOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Model (Fork Ent)
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **BEHIND AN ACCEPT OF THE SUB-PROTOCOL AT THE OUTPUT HEAD THE TABLE's TEST ON THE FORMS ACCEPTS
AT EACH OF THE HEAD's FOUR RUNS.** a: the state in front; b: behind; aK: b's part. -/
theorem made_forms (H : Seated Wp fld Fr q 24 bef B bS) (hplan : planB Wp = true) (piece6 : ℕ)
    (Lk : Link S Claim) (small : S → Option K9.Read)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (KB : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (hb : q.ior.red.out a τ = some b) (hL : K6Left Wp a.1.2) (hA : K6After Wp b.1.2)
    (Z1 : noTablesB a.1.2 = true) (hwo : K9.mergeOf a.1.2 = none)
    (left : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.1.2)
    (tree : ∃ G tr, a.1.2.fork? = some G ∧ G.trees[readsOf Wp]? = some tr ∧ tr.R = 1 ∧
      tr.K = Wp.H.nU.getD 2 0)
    (hnU : Wp.H.nU.getD 2 0 ≠ 0) (hB : tabsPlanB Wp.hS Wp.HLy Wp.H = true)
    (hRB : readsPlanB Wp.hS Wp.H = true)
    (hcov : ∃ cov, b.1.2.covered Wp.hS.T Wp.hS.V = .ok cov) (h4 : 5 ≤ Wp.hS.lmbH)
    (hpub : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC = 6 ∧ h3.calls.size = 6 ∧ Wp.hS.lmbH ≤ h3.kT + 5 ∧
        Wp.hS.ls ≤ (Wp.HLy.calls.getD 0 default).lJ ∧
        Wp.hS.ls ≤ ((h3.calls[0]?).map (·.n)).getD 0)
    (aK : K9.Part) (haK : K9.segAt? b.1.2 = some aK)
    (hMask : (K9.maskSeat (D.N.sent 24 0) aK).isSome = true)
    (hEnt : ∀ x : Ent, x.tree = readsOf Wp → x.row = 0 → x.idx < Wp.H.nU.getD 2 0 →
      K9.entInT (D.N.sent 24 0) aK x = true)
    (name : String) (hn : K6Name name) :
    K9.formsInT (D.Rd 24) (D.N.sent 24 0) 3 name b.1.2 = true := by
  obtain ⟨p3, hp3, L3⟩ := left
  obtain ⟨h3, F, g, hs3, hF, hg, Y, _⟩ := left_says p3 a.1.2 L3
  obtain ⟨q1, q2, q3, q4, q5⟩ := hpub p3 h3 hp3 hs3
  obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ hb
  have hOn := k6On_front H hplan a b τ hb hL
  obtain ⟨G0, tr, hG0, htr0, hR1, hK⟩ := tree
  obtain rfl : G0 = F := Option.some.inj (hG0.symm.trans hF)
  obtain ⟨F1, hF1⟩ := fork_behind H a b τ hb
  obtain ⟨hcan, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
  have et := blockOf_trees Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd'
  have eo := blockOf_owed Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd'
  rw [hF, hF1] at et eo
  have et' : F1.trees = G0.trees := et
  have eo' : F1.owed = G0.owed := eo
  have htr1 : F1.trees[readsOf Wp]? = some tr := by
    rw [et']
    exact htr0
  have hgb : b.1.2.lookHeard? = some g := (lookHeard_behind H a b τ hb).trans hg
  have one : ∀ gk, a.1.2.lookHeard? = some gk → gk = g := fun gk hgk =>
    Option.some.inj (hgk.symm.trans hg)
  have hKne : tr.K ≠ 0 := by
    rw [hK]
    exact hnU
  have hwide : (p8K6 Wp 24).hp.nU.getD 2 0 ≤ tr.K := by
    rw [hK]
    exact Nat.le_refl _
  have Z2 : readsWideB (readsOf Wp) ((p8K6 Wp 24).hp.nU.getD 2 0) a.1.2 = true := by
    unfold readsWideB
    rw [hF]
    show (match G0.trees[readsOf Wp]? with
      | some tr => Decidable.decide ((p8K6 Wp 24).hp.nU.getD 2 0 ≤ tr.K)
      | none => false) = true
    rw [htr0]
    exact decide_eq_true hwide
  have hzj : ∀ gk, a.1.2.lookHeard? = some gk →
      Wp.hS.ls ≤ (OnBytes.Model.Head.zjOf (p8K6 Wp 24).L gk 0).size := by
    intro gk hgk
    rw [one gk hgk]
    have z0 := Y.zkLen 0 (by rw [q1]; decide)
    show Wp.hS.ls ≤ ((g.zk.getD 0 #[]).extract 0 (Wp.HLy.calls.getD 0 default).lJ).size
    rw [Array.size_extract, z0]
    omega
  have h5 : ∀ gk, a.1.2.lookHeard? = some gk → Wp.hS.lmbH ≤ gk.shape.kT + 5 := by
    intro gk hgk
    rw [one gk hgk, Y.shape]
    exact q3
  have hun : K3.unpaid F1 g.owedJoin = true := by
    have := Y.join
    unfold K3.unpaid at this ⊢
    rw [eo']
    exact this
  obtain ⟨f1, f2, _, _⟩ := four_behind Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd hOn (p8K6 Wp 24) Z1 Z2 24
    piece6 3 Lk KS small
  obtain ⟨R, hR⟩ := four_answer Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd hOn (p8K6 Wp 24) rfl hB hRB hcov
    hzj h4 h5 F1 tr hF1 htr1 hKne hwide hR1 piece6 3 (K9.statesOfLink Lk) KS KB g hgb hun Y.cEnd
    (by rw [Y.shape]; exact q2) (by rw [Y.e]; exact q1) name hn
  have hFree : K9.mergeOf b.1.2 = none := by
    obtain ⟨o, F1', X, Q, ho, _, _, e⟩ := k6_behind H a b τ hb
    rw [e]
    unfold K9.mergeOf at hwo ⊢
    rw [ho] at hwo
    exact hwo
  have hRow : ∀ e v, withTables (p8K6 Wp 24) b.1.2 = some e →
      lettersAt (parOf Wp.hS (workOf Wp)) (seatAt Wp.hS (readsOf Wp)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesRow0 (readsOf Wp) tr.K v.2.2.final v.2.2.head) := by
    obtain ⟨i, hu, hbb⟩ := Option.map_eq_some_iff.mp h6
    have hr : readsOf Wp = i := by
      unfold readsOf
      rw [hu]
      rfl
    subst hr
    subst hbb
    obtain ⟨e0, v0, he0, hv0, _, _, _, _, _, hRow0, _⟩ := letters_behind Wp 24 hd' hOn.1 hcan
      hOn.2.1 (p8K6 Wp 24) rfl hB hRB hcov hOn.2.2.1 hzj h4 h5 F1 tr hF1 htr1 hKne hwide
    intro e v he hv
    obtain rfl : e0 = e := Option.some.inj (he0.symm.trans he)
    obtain rfl : v0 = v := Except.ok.inj (hv0.symm.trans hv)
    exact hRow0
  rw [readers]
  exact k6_formsInT Wp (p8K6 Wp 24) 24 piece6 3 (K9.statesOfLink Lk) KS _ (D.N.sent 24 0) b.1.2 aK
    haK f1 hOn.2.1 f2 hA.2.1 hA.2.2.1
    (fun gk hgk => by rw [Option.some.inj (hgk.symm.trans hgb)]; exact Y.cEnd) tr.K hRow
    (by rw [hK]; exact hEnt) hMask hFree name hn R hR

/-- **The public test formsInT 24 4 "own"**, where the table's test on the forms accepts at the
four runs. -/
theorem made_own (hown : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")])
    (x : P × S)
    (hall : ∀ name, K6Name name → K9.formsInT (D.Rd 24) (D.N.sent 24 0) 3 name x.2 = true) :
    (mgAll D Mg).pub (.formsInT 24 4 "own") x = true := by
  rw [Sound.mgAll_pub, First.pubAll_formsInT]
  have e : D.pubD.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")] := hown
  rw [e]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hall "norm" (Or.inl rfl), hall "policy" (Or.inr (Or.inl rfl)),
    hall "logits" (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- **The public test formsInT 24 4 "join".** -/
theorem made_join (hjoin : D.runs 24 4 "join" = [(3, "join")]) (x : P × S)
    (hall : ∀ name, K6Name name → K9.formsInT (D.Rd 24) (D.N.sent 24 0) 3 name x.2 = true) :
    (mgAll D Mg).pub (.formsInT 24 4 "join") x = true := by
  rw [Sound.mgAll_pub, First.pubAll_formsInT]
  have e : D.pubD.runs 24 4 "join" = [(3, "join")] := hjoin
  rw [e]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact hall "join" (Or.inr (Or.inr (Or.inr rfl)))

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.made_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.made_join
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.made_forms
