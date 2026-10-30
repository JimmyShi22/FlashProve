--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Accepts.lean: kind K13, the members' batching: THE SUB-PROTOCOL ACCEPTS THE
HONEST PROVER's ROUNDS (`movesAtM3`, Johnson/Desc/K13/Honest/MovesAtM3.lean), AND THE ROW THAT IT
LAYS AS ITS CLAIM IS TRUE, where all rows of the pile are. Statements with their proofs. These are
the kind's statements on "the decision accepts the honest messages".

How much the two halves say. The decision tests no sent value (Johnson/Desc/K13/Kind.lean): under
the premises on the verifier's own state it accepts ANY elements that come in rounds of this form.
So the acceptance is no merit of the honest values. What distinguishes the honest prover from
another is the second half: the row that is laid as the claim is true.

True of what. Of w, which is a free parameter: any matrix of nR rows, nR free, and any values of the
mask entries, of which all rows of the pile are true. Nothing here ties w's matrix to a committed
table, w's mask entries to what the index masks' message holds, or nR to the shape's number of rows.

The steps: what is heard of the prover reads as what it computes, where σ is a section of the
reading; the batching's text returns; the joined sub-protocol accepts at the first chain's state.
Main names:
  `sent_length`: one pair for each variable. `codeRounds_read`, `codeRounds_chal`, `codeRounds_len`,
    `codeRounds_two`: the rounds' form.
  `codeHeard_reads`: what is heard reads as what the prover computes.
  `batt_returns_code`: the text. `atM3_accepts_code`: **the joined sub-protocol**, with the state
    that it leaves; its docstring tells the premises.
  `atM3_accepts_code_gl`: the same at the release's own reading: no section is left as a premise.

What is not claimed. That the premises on the state hold at the place: they are owed by the
sub-protocols in front and by the tests on the plan; among them, that the ledger of the index masks'
message has 1 + 2 kCol entries left (Johnson/Desc/K13/Honest/Room.lean brings that to a count). That
all rows on the pile are true: a premise. That a round's scalars read no later challenge is shown of
the scalars (`sent_take`, SumLaw.lean), not of `movesAtM3`. The sub-protocol's test on the plan and
the format's step in front of the decision are not treated. It is not claimed that the C++ prover
sends these scalars. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.CodeRow
import Johnson.Desc.K13.Honest.SubProtocols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model Cb Iop
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open OnBytes.Slice (GE ofE)
open VerifiableInference.Desc.K13.Law

/-- One pair for each variable. -/
theorem sent_length {K : Type} [CommRing K] (u : ℕ → K) (eps : K) : ∀ (n i : ℕ)
    (T : List (List K × List K)) (gs : List K), (sent u eps n i T gs).length = n
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | n + 2, i, _, gs => congrArg (· + 1) (sent_length u eps (n + 1) (i + 2) _ gs.tail)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {nR k : ℕ}
variable (σ : K → E) (hσ : ∀ a, ρ.val (σ a) = a)

omit [Fintype K] in
include hσ in
/-- Read again, the rounds are the pairs. -/
theorem codeRounds_read : ∀ (l : List (K × K)) (gs : List E), l.length = gs.length →
    readRounds ρ (codeRounds σ l gs) = l
  | [], [], _ => rfl
  | q :: l, g :: gs, h => by
    show (ρ.val (σ q.1), ρ.val (σ q.2)) :: readRounds ρ (codeRounds σ l gs) = q :: l
    rw [hσ, hσ, codeRounds_read l gs (by simp only [List.length_cons] at h; omega)]
  | [], _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

omit [Field K] [Fintype K] in
/-- Their challenges are the sampled elements. -/
theorem codeRounds_chal : ∀ (l : List (K × K)) (gs : List E), l.length = gs.length →
    (codeRounds σ l gs).map (·.2) = gs
  | [], [], _ => rfl
  | _ :: l, g :: gs, h =>
    congrArg (g :: ·) (codeRounds_chal l gs (by simp only [List.length_cons] at h; omega))
  | [], _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

omit [Field K] [Fintype K] in
/-- One round for each pair. -/
theorem codeRounds_len : ∀ (l : List (K × K)) (gs : List E), l.length = gs.length →
    (codeRounds σ l gs).length = l.length
  | [], [], _ => rfl
  | _ :: l, _ :: gs, h =>
    congrArg (· + 1) (codeRounds_len l gs (by simp only [List.length_cons] at h; omega))
  | [], _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

omit [Field K] [Fintype K] in
/-- Two elements are sent in each. -/
theorem codeRounds_two : ∀ (l : List (K × K)) (gs : List E),
    ∀ p ∈ codeRounds σ l gs, p.1.length = 2
  | q :: l, g :: gs, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · rfl
    · exact codeRounds_two l gs p hp
  | [], _, _, hp => by cases hp
  | _ :: _, [], _, hp => by cases hp

omit [Fintype K] in
include hσ in
/-- **What is heard of the prover reads as what it computes.** -/
theorem codeHeard_reads (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot) (x eps : E)
    (gs : List E) (hg : gs.length = k) :
    ReadsCode ρ w pile fresh x
      (codeHeard ρ σ (maskAt w fresh) (tabsOf ρ w pile (ρ.val x)) k eps gs) where
  mu := hσ _
  rounds := by
    have hl : (sent (maskAt w fresh) (ρ.val eps) k 0 (tabsOf ρ w pile (ρ.val x))
        (gs.map ρ.val)).length = gs.length := by rw [sent_length, hg]
    have hc : (codeRounds σ (sent (maskAt w fresh) (ρ.val eps) k 0 (tabsOf ρ w pile (ρ.val x))
        (gs.map ρ.val)) gs).map (fun p => ρ.val p.2) = gs.map ρ.val := by
      have e := codeRounds_chal σ _ gs hl
      have e2 : (codeRounds σ (sent (maskAt w fresh) (ρ.val eps) k 0 (tabsOf ρ w pile (ρ.val x))
          (gs.map ρ.val)) gs).map (fun p => ρ.val p.2) =
          ((codeRounds σ (sent (maskAt w fresh) (ρ.val eps) k 0 (tabsOf ρ w pile (ρ.val x))
            (gs.map ρ.val)) gs).map (·.2)).map ρ.val := by
        rw [List.map_map]
        rfl
      rw [e2, e]
    show readRounds ρ (codeRounds σ _ gs) = sent _ (ρ.val eps) k 0 _
      ((codeRounds σ _ gs).map fun p => ρ.val p.2)
    rw [hc, codeRounds_read ρ σ hσ _ gs hl]

include hσ in
/-- **The batching's text returns on these rounds, and the row that it hands on is true.** -/
theorem batt_returns_code (w : Wit K nR k) {owed : RowsOwed} {n : ℕ} {pile : List TensorRow}
    {ledger : ℕ} {d : St} {t : List ℕ × St} (h1 : owed.isNone = true)
    (hf : Batt.fits k pile = true) (h3 : pile.length = n)
    (ht : takeMasksP d ledger (Batt.masksOf k) = some t) (hrows : ∀ r ∈ pile, Holds ρ w r)
    (x eps : E) (gs : List E) (hg : gs.length = k) :
    ∃ row, batt owed k n pile ledger d
        (movesAtM3 ρ σ w pile (t.1.map fun i => ⟨ledger, i⟩) x eps gs) = .ok (row, t.2) ∧
      Holds ρ w row := by
  have hfr : (t.1.map fun i => (⟨ledger, i⟩ : Slot)).length = 1 + 2 * k := by
    rw [List.length_map, takeMasks_length ht]
    rfl
  have hl : (sent (maskAt w (t.1.map fun i => ⟨ledger, i⟩)) (ρ.val eps) k 0
      (tabsOf ρ w pile (ρ.val x)) (gs.map ρ.val)).length = gs.length := by rw [sent_length, hg]
  obtain ⟨o, ho⟩ := Law.run_some (x := x)
      (h := codeHeard ρ σ (maskAt w (t.1.map fun i => ⟨ledger, i⟩))
      (tabsOf ρ w pile (ρ.val x)) k eps gs) hf hfr
    (by
      show (codeRounds σ _ gs).length = k
      rw [codeRounds_len σ _ gs hl, sent_length])
    (codeRounds_two σ _ gs) rfl
  have h4 : o.rowMaps.length = pile.length := by
    obtain ⟨-, -, -, -, -, hmp, -⟩ := Law.run_fields hf ho
    rw [hmp, List.length_map, List.length_zip, OnBytes.Road.Hd.powers_len, Nat.min_self]
  exact ⟨Batt.rowOf pile o,
    batt_answers k owed n pile ledger d _ _ x t _ o h1 hf (oneDrawn_mk _ _ _) h3 ht
      (heard_roundsOf _ rfl) ho h4,
    code_row ρ w pile _ hf hrows x _ o (codeHeard_reads ρ σ hσ w pile _ x eps gs hg) ho⟩

variable {Cl : Type}

include hσ in
/-- **The joined sub-protocol accepts the prover's rounds, and the row that it lays as its claim is
true.** The premises, in the order of the sub-protocol's tests on its own state: the chain is out of
the finish and not yet at its end (`s.here = .fin f`); a reply was heard where one is due; the pile
has the plan's number of rows, and the form that the table's shape asks; no count of rows waits; the
pile has the form that the batching allows; the ledger of the index masks' message hands out 1 + 2
kCol entries; the shape is lawful, and names W's message. Beside these nine: all rows of the pile
are true of w; and there are as many challenges as variables. Then the decision returns the state
with the ledger moved on, W's message announced and one claim laid, made of a row that is true of
the same w. THE DECISION TESTS NO SENT VALUE: under the nine premises it returns so on any elements
in rounds of this form; what is said of the honest prover's values is that the row is true. -/
theorem atM3_accepts_code {P : Where} {s : S} {f : First.FinOwn} (w : Wit K nR P.lin.kCol)
    {t : List ℕ × St} {msg : Array OracleNotice} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hrows : ∀ r ∈ s.out.pending, Holds ρ w r) (x eps : E) (gs : List E)
    (hg : gs.length = P.lin.kCol) (cols : List (List (Nat × List UInt64))) :
    ∃ row, (atM3 (Cl := Cl) P).decide s
        (movesAtM3 ρ σ w s.out.pending (t.1.map fun i => ⟨s.out.indexMasks, i⟩) x eps gs)
        cols = .ok (withClaim s t.2.st msg row) ∧ Holds ρ w row := by
  have howed : (owedOf s).isNone = true := by
    unfold owedOf
    rw [if_pos hw]
    rfl
  obtain ⟨row, hb, hrow⟩ := batt_returns_code ρ σ hσ w howed hform hcount ht hrows x eps gs hg
  have hq : quiet t.2.st.codes P.lin = .ok msg := by
    rw [(takeMasks_same ht).1]
    exact quiet_returns hlin hmsg
  have hl : (sent (maskAt w (t.1.map fun i => ⟨s.out.indexMasks, i⟩)) (ρ.val eps) P.lin.kCol 0
      (tabsOf ρ w s.out.pending (ρ.val x)) (gs.map ρ.val)).length = gs.length := by
    rw [sent_length, hg]
  refine ⟨row, atM3_of_batt hs hreply hcount hfit hb ?_ hq cols, hrow⟩
  show (roundsOf x _).length = _
  rw [roundsOf_length]
  show 2 + (codeRounds σ _ gs).length = _
  rw [codeRounds_len σ _ gs hl, sent_length]

/-- **The same at the release's own reading** (`Reading.gl`: a word that is not below the prime
counts as its residue), where a section is at hand. The premises are those of `atM3_accepts_code`.
-/
theorem atM3_accepts_code_gl {P : Where} {s : S} {f : First.FinOwn} (w : Wit GE nR P.lin.kCol)
    {t : List ℕ × St} {msg : Array OracleNotice} (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg w r) (x eps : E) (gs : List E)
    (hg : gs.length = P.lin.kCol) (cols : List (List (Nat × List UInt64))) :
    ∃ row, (atM3 (Cl := Cl) P).decide s
        (movesAtM3 ρg (fun a => E.ofTriple (ofE a)) w s.out.pending
          (t.1.map fun i => ⟨s.out.indexMasks, i⟩) x eps gs)
        cols = .ok (withClaim s t.2.st msg row) ∧ Holds ρg w row :=
  atM3_accepts_code ρg (fun a => E.ofTriple (ofE a)) gl_section w hs hreply hcount hfit hw hform ht
    hlin hmsg hrows x eps gs hg cols

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.sent_length
#print axioms VerifiableInference.Desc.K13.Honest.codeRounds_read
#print axioms VerifiableInference.Desc.K13.Honest.codeRounds_chal
#print axioms VerifiableInference.Desc.K13.Honest.codeRounds_len
#print axioms VerifiableInference.Desc.K13.Honest.codeRounds_two
#print axioms VerifiableInference.Desc.K13.Honest.codeHeard_reads
#print axioms VerifiableInference.Desc.K13.Honest.batt_returns_code
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_code
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_code_gl
