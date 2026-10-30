-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptAtLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: LAWS ON THE TERMS OF Honest/K1/ScriptAt.lean. Statements and proofs; no
definition.

  find_due, look_due, cut_isSome, ok_of_bind_map   tools: the count of what a purse holds at an
                address is the table's · so Coins.look's, at the first and the shared chain · a cut
                from 0 is there just where the counts allow it · what a bind over a map returns
  lentCut_isSome   AT THE FIRST AND THE SHARED CHAIN THE CUT IS THERE JUST WHERE THE PUBLIC TEST
                bookCovers ACCEPTS: no run stands on the right: at all coins or at none
  cut_of_lend   wherever the frame's lendPart returns, lentCut is the part's own coins
  rowsLaid_part   where the job's data reads of Front what was heard alone: rowsLaid at the state's
                input and at what was heard in front of the part IS SendJob.rows: the part's own
                rows, in both moves
  main_noData   tool: at a place that padB names in a main row rowsR's entry reads no data
  pad_same      AT EVERY PLACE THAT padB NAMES scriptPad AND scriptMsg AGREE: NO OTHER PREMISE
  scriptPad_off   off these places scriptPad is 0
  pad_only      AT A MESSAGE OF ONE ANSWER, OFF padB's PLACES, A MAIN ENTRY INSIDE THE MESSAGE's
                RANGES (a row below its main rows, a place below the code's message length) IS WHAT
                THE DATA SAYS: no coin is written there
  table_said    where the job fits its place and its data reads of Front what was heard alone: the
                part's first move says no item and tables whose number tau is scriptTable's, at
                every tree of the plan

  answers_words   where the job fits its place, its data reads of Front what was heard alone and the
                challenge holds the seeds: the part's second move says no table and the answers
                "answers" (Johnson/Prover/Send/Core.lean) at the words "held" of rowsLaid at what
                was heard in front of the part

What is WRITTEN where: no sentence on what a coin, a pad or a mask row is for.

Limits. pad_only has the premise "one answer": at two, rowsR writes pad coins off padB's places: no
law here says so: a test does (Honest/K1/ScriptAtSmall.lean). lentCut_isSome says nothing at the
second chain, where Coins.look reads all three tables. Nothing here holds the terms against any
Script. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.K1.CoinLaw
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.TableShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (Rows shapeAt answers)

variable {Bk : ProverCoinCounts} {V W X : Type}

theorem find_due : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    ((Purse.find? l c a).getD ⟨⟨0, 0⟩, Cs.empty⟩).1 = dueAt l a
  | [], _, _ => rfl
  | r :: l, c, a => by
    unfold Purse.find? dueAt
    rw [List.lookup_cons]
    by_cases h : (r.1 == a) = true
    · have h' : (a == r.1) = true := by rw [beq_iff_eq] at h ⊢; exact h.symm
      simp only [h, h', if_true, Option.getD_some]
    · have h' : (a == r.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun q => h (by rw [beq_iff_eq]; exact q.symm)
      simp only [h, h', Bool.false_eq_true, if_false]
      exact find_due l c.2 a

theorem look_due (k : Coins Bk) (ch : Nat) (hc : ch ≤ 1) (a : Addr) :
    (k.look ch a).1 = dueAt (Bk.rowsOf ch) a := by
  have h2 : ch = 0 ∨ ch = 1 := by omega
  rcases h2 with rfl | rfl
  · exact find_due Bk.first k.first a
  · exact find_due Bk.shared k.shared a

theorem cut_isSome {d : Due} (c : Cs d) (n : Due) :
    (c.cut ⟨0, 0⟩ n).isSome = decide (n.f ≤ d.f ∧ n.e ≤ d.e) := by
  unfold Cs.cut
  by_cases h : n.f ≤ d.f ∧ n.e ≤ d.e
  · have h' : (⟨0, 0⟩ : Due).f + n.f ≤ d.f ∧ (⟨0, 0⟩ : Due).e + n.e ≤ d.e := by
      constructor
      · show 0 + n.f ≤ d.f
        omega
      · show 0 + n.e ≤ d.e
        omega
    rw [dif_pos h', decide_eq_true h]
    rfl
  · have h' : ¬ ((⟨0, 0⟩ : Due).f + n.f ≤ d.f ∧ (⟨0, 0⟩ : Due).e + n.e ≤ d.e) := by
      intro q
      apply h
      have q1 : 0 + n.f ≤ d.f := q.1
      have q2 : 0 + n.e ≤ d.e := q.2
      constructor <;> omega
    rw [dif_neg h', decide_eq_false h]
    rfl

/-- **At the first and the shared chain (ch ≤ 1) the cut is there just where the public test
accepts.** -/
theorem lentCut_isSome (k : Coins Bk) (ch : Nat) (hc : ch ≤ 1) (a : Addr) (d : Due) :
    (lentCut k ch a d).isSome = bookCovers Bk ch a d := by
  unfold lentCut bookCovers
  rw [cut_isSome, look_due k ch hc a]

theorem ok_of_bind_map {ε α β γ : Type} (x : Except ε α) (y : Except ε β) (f : α → β → γ) (c : γ)
    (h : (x.bind fun a => y.map fun b => f a b) = .ok c) : ∃ a b, c = f a b := by
  cases x with
  | error _ => simp [Except.bind] at h
  | ok a =>
    cases y with
    | error _ => simp [Except.bind, Except.map] at h
    | ok b =>
      simp only [Except.bind, Except.map, Except.ok.injEq] at h
      exact ⟨a, b, h.symm⟩

/-- **Wherever the frame's lending returns, lentCut is the part's own coins.** -/
theorem cut_of_lend (rows : List (Addr × Due)) (k : Coins Bk) (ch : Nat) (a : Addr)
    (p : Part V W X) (c : p.Coins) (h : lendPart Bk rows (k.look ch) a p = .ok c) :
    lentCut k ch a p.takes = some c.1 := by
  unfold lendPart at h
  unfold lentCut
  split at h
  · cases h
  · cases e : ((k.look ch a).2.cut ⟨0, 0⟩ p.takes) with
    | none => simp [e] at h
    | some own =>
      simp only [e] at h
      obtain ⟨sp, ca, hc⟩ := ok_of_bind_map _ _ (fun sp ca => (own, sp, ca)) c h
      rw [hc]

/-- **The part's own rows.** -/
theorem rowsLaid_part (J : SendJob W X) (own₀ : X)
    (hd : ∀ w (f f' : Front X), f.heard = f'.heard → J.data w f = J.data w f')
    (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X) (n : Nat) :
    rowsLaid J own₀ c t.input (t.heard.take (t.heard.length - n)) = J.rows c s t n := by
  unfold rowsLaid SendJob.rows
  exact congrArg (fun D => rowsR J.P J.ride D c) (hd t.input _ _ rfl)

/-- At a place that padB names in a main row rowsR's entry reads no data. -/
theorem main_noData (P : K1.Par) (ride : Nat → Option Ride)
    (d d' : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k r j : Nat)
    (hp : padB P.codes (shapeAt P k) false r j = true) :
    (rowsR P ride d cs k).main ((shapeAt P k).mainDeg == 3) r j =
      (rowsR P ride d' cs k).main ((shapeAt P k).mainDeg == 3) r j := by
  unfold padB at hp
  simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hp
  obtain ⟨⟨hz, hr⟩, hj⟩ := hp
  have hrr : r < (shapeAt P k).mainRows := by omega
  unfold Rows.main
  by_cases hl : (P.codes.base.getD (shapeAt P k).code default).ell ≤ j
  · have g : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = true :=
      decide_eq_true hl
    simp only [rowsR, g, Bool.or_true, if_true]
  · have hl' : j < (P.codes.base.getD (shapeAt P k).code default).ell := by omega
    by_cases ha : (shapeAt P k).answers = 0
    · by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
      · simp only [h3, if_true]
        rw [word_coin_e P ride d cs k r j h3 ha hrr hl',
          word_coin_e P ride d' cs k r j h3 ha hrr hl']
      · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
        simp only [h3', Bool.false_eq_true, if_false]
        rw [word_coin_f P ride d cs k r j h3' ha hrr hl',
          word_coin_f P ride d' cs k r j h3' ha hrr hl']
    · have hw0 : ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = false := by
        have : ((shapeAt P k).answers == 0) = false := beq_eq_false_iff_ne.2 ha
        simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false, bne_self_eq_false]
      have hzb : ((shapeAt P k).maskRows == 0) = true := by rw [beq_iff_eq]; exact hz
      have hab : ((shapeAt P k).answers != 0) = true := by rw [bne_iff_ne]; exact ha
      have hpd : (stepsOf P.codes (shapeAt P k) (ride k)).pad =
          (if (shapeAt P k).mainDeg == 3 then 1 else 3) * (shapeAt P k).answers := by
        simp only [stepsOf, hzb, hab, Bool.and_self, if_true]
      have n1 : decide ((shapeAt P k).mainRows ≤ r) = false := decide_eq_false (by omega)
      have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false :=
        decide_eq_false hl
      have n3 : (r + 1 == (shapeAt P k).mainRows) = true := by rw [beq_iff_eq]; exact hr
      have n5 : decide (j < (P.codes.base.getD (shapeAt P k).code default).ell) = true :=
        decide_eq_true hl'
      by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
      · have h3e : (shapeAt P k).mainDeg = 3 := by rw [beq_iff_eq] at h3; exact h3
        rw [if_pos h3e] at hj
        rw [h3, if_pos rfl] at hpd
        have hp0 : ((stepsOf P.codes (shapeAt P k) (ride k)).pad != 0) = true := by
          rw [bne_iff_ne]
          omega
        have n4 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
            (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤ j) = true := decide_eq_true (by omega)
        simp only [rowsR, h3, n1, n2, n3, n4, n5, hw0, hp0, Bool.not_true, Bool.or_self,
          Bool.and_self, Bool.false_eq_true, if_false, if_true, Option.map_some]
      · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
        have h3n : (shapeAt P k).mainDeg ≠ 3 := by
          intro q
          rw [q] at h3'
          cases h3'
        rw [if_neg h3n] at hj
        rw [h3', if_neg (by simp)] at hpd
        have hp0 : ((stepsOf P.codes (shapeAt P k) (ride k)).pad != 0) = true := by
          rw [bne_iff_ne]
          omega
        have n4 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
            (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤ j) = true := decide_eq_true (by omega)
        simp only [rowsR, h3', n1, n2, n3, n4, n5, hw0, hp0, Bool.not_false, Bool.or_self,
          Bool.and_self, Bool.false_eq_true, if_false, if_true, Option.map_some]

/-- **At every place that padB names the pad's component and the message agree.** -/
theorem pad_same (J : SendJob W X) (own₀ : X) (n : Nat) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) (mask : Bool) (r j : Nat)
    (hp : padB J.P.codes (shapeAt J.P n) mask r j = true) :
    scriptPad J n c mask r j = scriptMsg J own₀ n c w h mask r j := by
  unfold scriptPad scriptMsg rowsLaid rowsMsg
  rw [if_pos hp]
  cases mask with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact main_noData J.P J.ride _ _ c n r j hp

/-- Off these places the pad's component is 0. -/
theorem scriptPad_off (J : SendJob W X) (n : Nat) (c : Cs (dueR J.P J.ride)) (mask : Bool)
    (r j : Nat) (hp : padB J.P.codes (shapeAt J.P n) mask r j = false) :
    scriptPad J n c mask r j = 0 := by
  unfold scriptPad
  rw [hp]
  rfl

/-- **At a message of one answer, off padB's places, a main entry inside the message's ranges is
what the data says.** Over the base field an element of the extension field counts as nothing, as in
rowsR. The data: at the text's own record, where nothing seen and no column is handed (.bare []); at
what a move is handed in a run:
where the job's data reads neither (heardOnly). -/
theorem pad_only (J : SendJob W X) (own₀ : X) (n : Nat) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) (r j : Nat) (ha : (shapeAt J.P n).answers = 1)
    (hp : padB J.P.codes (shapeAt J.P n) false r j = false)
    (hr : r < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell) :
    scriptMsg J own₀ n c w h false r j =
      if (shapeAt J.P n).mainDeg == 3 then
        match J.data w { heard := h, own := own₀, seen := .bare [] } n r j with
        | some (.inr x) => x
        | some (.inl x) => algebraMap GF GE x
        | none => 0
      else
        algebraMap GF GE (match J.data w { heard := h, own := own₀, seen := .bare [] } n r j with
        | some (.inl x) => x
        | _ => 0) := by
  have ha0 : (shapeAt J.P n).answers ≠ 0 := by omega
  have hq : (r, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n) := by
    intro hm
    unfold padInMain at hm
    by_cases hz : ((shapeAt J.P n).maskRows != 0 || (shapeAt J.P n).mainRows == 0) = true
    · rw [if_pos hz] at hm
      cases hm
    · rw [if_neg hz] at hm
      simp only [Bool.or_eq_true, bne_iff_ne, beq_iff_eq, not_or, not_not] at hz
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq, ha, Nat.mul_one] at hm
      obtain ⟨i, hi, h1, h2⟩ := hm
      have : padB J.P.codes (shapeAt J.P n) false r j = true := by
        unfold padB
        simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        refine ⟨⟨hz.1, by omega⟩, ?_⟩
        by_cases h3 : (shapeAt J.P n).mainDeg = 3
        · simp only [h3, beq_self_eq_true, if_true] at hi h2 ⊢
          omega
        · have h3b : ((shapeAt J.P n).mainDeg == 3) = false := beq_eq_false_iff_ne.2 h3
          simp only [h3, h3b, Bool.false_eq_true, if_false] at hi h2 ⊢
          omega
      rw [this] at hp
      cases hp
  unfold scriptMsg rowsLaid rowsMsg Rows.main
  simp only [Bool.false_eq_true, if_false]
  by_cases h3 : ((shapeAt J.P n).mainDeg == 3) = true
  · rw [if_pos h3, if_pos h3, main_data_e J.P J.ride _ c n r j h3 hr hj ha0 hq]
    generalize J.data w { heard := h, own := own₀, seen := .bare [] } n r j = v
    rcases v with _ | (x | x) <;> rfl
  · have h3' : ((shapeAt J.P n).mainDeg == 3) = false := by simpa using h3
    rw [if_neg h3, if_neg h3, main_data_f J.P J.ride _ c n r j h3' hr hj ha0 hq]
    generalize J.data w { heard := h, own := own₀, seen := .bare [] } n r j = v
    rcases v with _ | (x | x) <;> rfl

/-- **What the part's first move says**, where the job fits its place and its data reads of Front
what was heard alone. -/
theorem table_said (J : SendJob W X) (own₀ : X) (hf : sendFits J.P J.ride = true)
    (hd : ∀ w (f f' : Front X), f.heard = f'.heard → J.data w f = J.data w f') :
    ∃ m₁ m₂, (sendPart (V := V) J).moves = [m₁, m₂] ∧
      ∀ c s t, ∃ S, m₁.say c s t = .ok S ∧ S.vals = [] ∧
        ∀ τ, τ < J.P.trees.length →
          S.tables[τ]? = some (scriptTable J own₀ τ c.1 t.input t.heard).2 := by
  obtain ⟨m₁, m₂, h, hs⟩ := first_say (V := V) J hf
  refine ⟨m₁, m₂, h, fun c s t => ⟨_, hs c s t, rfl, fun τ hτ => ?_⟩⟩
  have e := rowsLaid_part J own₀ hd c.1 s t 0
  rw [Nat.sub_zero, List.take_length] at e
  unfold scriptTable
  rw [e]
  have hl : τ < (treeTables J.P (J.rows c.1 s t 0)).length := by
    rw [treeTables_length]
    exact hτ
  rw [List.getElem?_eq_getElem hl]
  rfl

/-- **What the part's second move says.** THE 0 BENEATH THE HELD WORDS: NO COIN: A CONSTANT; never
read at the job's own messages (answers_any, Honest/K1/Law/SendAtBlock.lean). -/
theorem answers_words (J : SendJob W X) (own₀ : X) (hf : sendFits J.P J.ride = true)
    (hd : ∀ w (f f' : Front X), f.heard = f'.heard → J.data w f = J.data w f') :
    ∃ m₁ m₂, (sendPart (V := V) J).moves = [m₁, m₂] ∧
      ∀ c s t, seedsFit J.P (t.lately 1) = true →
        m₂.say c s t = .ok
          ⟨(answers J.P (stAt J.P J.first) J.first
              (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
                (rowsLaid J own₀ c.1 t.input (t.heard.take (t.heard.length - 1))))
              (seedsAt J.P (t.lately 1))).map fun a => .answer (toE a), []⟩ := by
  refine ⟨_, _, rfl, fun c s t hs => ?_⟩
  rw [rowsLaid_part J own₀ hd c.1 s t 1]
  simp [hf, hs]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.find_due
#print axioms ProofFile.Honest.K1.look_due
#print axioms ProofFile.Honest.K1.cut_isSome
#print axioms ProofFile.Honest.K1.lentCut_isSome
#print axioms ProofFile.Honest.K1.ok_of_bind_map
#print axioms ProofFile.Honest.K1.cut_of_lend
#print axioms ProofFile.Honest.K1.rowsLaid_part
#print axioms ProofFile.Honest.K1.main_noData
#print axioms ProofFile.Honest.K1.pad_same
#print axioms ProofFile.Honest.K1.scriptPad_off
#print axioms ProofFile.Honest.K1.pad_only
#print axioms ProofFile.Honest.K1.table_said
#print axioms ProofFile.Honest.K1.answers_words
