-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FirstMakeFacts.lean: THREE CLOSED FACTS ON THE FIRST SEGMENT's OPENING, FROM THE
RETURN OF `ProofFile.pubPlain` ALONE: NO SCOPE: every o for the second hash function, all three public
files. (a) the opening's last message has mask rows; (b) its sample has at least one answer (the
field `answers` of its shape); (c) the first state's shape has a notice at the start. Theorems with
their proofs. Cut for the make of a fact on the index masks'
room in the link's frame's files.

WHY THEY HOLD. The first chain's parameters are read by the strict reader `Params.First.read`, which
rejects a shape without exactly one notice at the start; `pubBy` returns only where `S.startP` does,
whose test `OnBytes.reqShapeOk` asks of every such notice mask rows and the shape's own number of
answers, which is at least 1; and the opening's list of messages ends in that notice.

  `read_atStart`, `proofRead_first`, `chainsOf_first`, `planned_first`, **`pub_first_read`**.
  `startP_is`, `shapeOk_atStart`, `startOk_shape`; with ProofFile's own `pubBy_start` and `startP_ok`
    (Johnson/Desc/ProofFile/Law/PureMade.lean).
  `sent_last`: the opening's last message is the one notice at the start. **`pub_atStart`**.
  **`first_last_maskRows`** (a), **`first_last_answers`** (b): at `Z.first` and every gp;
  `ground_last_maskRows`, `ground_last_answers`: at the lots' letters G of `blankBy`, by
  `lettersBy_first`, **`blankBy_first`** : G.first = Z.first.
  **(c) HOLDS ONLY BEHIND A FENCE.** `startS_blank`, `startS_blank_empty`: where the tests on the
    request reject (the empty request is such a one) `ProofFile.startS` is the blank state, whose shape
    has NOTHING at the start. `startS_atStart`: at a first state without a mark it has a notice.
    `firstAtS_blank`: the opening rejects from the blank state. **`firstAtS_atStart`**: so wherever
    the opening accepts from the first state, that state's shape has a notice at the start.

Limits. Nothing on soundness. On the public data and the first state alone. That `pubPlain` returns
anywhere is a run's word.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.Desc.K1.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc

/-- The reader of a proof's first chain returns a shape with exactly one notice at the start. -/
theorem read_atStart {b : ByteArray} {p : Params.First} (h : Params.First.read b = some p) :
    p.shape.atStart.length = 1 := by
  unfold Params.First.read at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨g, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.1.1.1.1.1
    · cases h
  · cases h

theorem proofRead_first {a b c : ByteArray} {p : Params.ProofChains}
    (h : Params.ProofChains.read a b c = some p) : Params.First.read a = some p.first := by
  unfold Params.ProofChains.read at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨z, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact hx
  · cases h

theorem chainsOf_first {X : Verify.Public} {layout : Option ByteArray} {cfg : ByteArray}
    {c : Verify.Chains} (h : ProofFile.Plain.chainsOf X layout cfg = .ok c) :
    ∃ b, Params.First.read b = some c.proof.first := by
  unfold ProofFile.Plain.chainsOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (cases h
       exact ⟨_, proofRead_first (by assumption)⟩)

theorem planned_first {o : SecondHashFunctionArgument} {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Verify.Planned} (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    ∃ b, Params.First.read b = some p.chains.proof.first := by
  unfold ProofFile.Plain.planned at h
  obtain ⟨X, -, h⟩ := bind_ok h
  obtain ⟨c, hc, h⟩ := bind_ok h
  obtain ⟨bl, -, h⟩ := bind_ok h
  cases h
  exact chainsOf_first hc

/-- **The public part's first chain's parameters were read by the strict reader.** -/
theorem pub_first_read {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pubPlain o pol lay KL = .ok Z) : ∃ b, Params.First.read b = some Z.first :=
  planned_first (madeOf_planned (pubBy_made h))

/-- The value of `S.startP` is the first state written out. -/
theorem startP_is {P : VerifiableInference.Desc.First.Par} {codes : Codes}
    {shape : Params.ReqShape} {layout : Params.ReqLayout} {s : S}
    (h : S.startP P codes shape layout = some s) : s = S.firstRecord codes shape layout := by
  unfold S.startP at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- What the test on a request's shape says of its answers and of what rides at the start. -/
theorem shapeOk_atStart {s : Params.ReqShape} (h : OnBytes.reqShapeOk s = true) :
    1 ≤ s.answers ∧ ∀ n ∈ s.atStart, n.shape.maskRows ≠ 0 ∧ n.shape.answers = s.answers := by
  unfold OnBytes.reqShapeOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.2, fun n hn => ⟨(h.1.1.1.1.2 n hn).1.1.1.1.2, (h.1.1.1.1.2 n hn).1.2⟩⟩

theorem startOk_shape {P : VerifiableInference.Desc.First.Par} {codes : Codes}
    {shape : Params.ReqShape} {layout : Params.ReqLayout}
    (h : S.startOk P codes shape layout = true) : OnBytes.reqShapeOk shape = true := by
  unfold S.startOk OnBytes.reqOk at h
  simp only [Bool.and_eq_true] at h
  exact h.2.1.1.1

/-- The opening's last message is the one notice that rides at the start. -/
theorem sent_last (q : Params.First) (gp : _root_.Desc.Plain.GPar) (n : OracleNotice)
    (h : q.shape.atStart = [n]) :
    (K1.firstPar q gp).sent.getD
      ((K1.firstPar q gp).sent.size - 1) default = n := by
  have e : (K1.firstPar q gp).sent =
      ((ReqFrame.notices ((K1.frame₀ q).atMoment 0)).toList ++
        [foldMaskNotice ((K1.frame₀ q).foldShape 0 {})] ++ [n]).toArray := by
    unfold K1.Par.sent K1.firstPar
      K1.firstParts K1.firstLaid
    simp [h]
  rw [e]
  simp

section
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}

/-- The one notice at the start, with what the tests on the public parameters say of it. -/
theorem pub_atStart (h : pubPlain o pol lay KL = .ok Z) :
    ∃ n, Z.first.shape.atStart = [n] ∧ 0 < n.shape.maskRows ∧ 1 ≤ n.shape.answers := by
  obtain ⟨b, hb⟩ := pub_first_read h
  obtain ⟨n, hn⟩ := List.length_eq_one_iff.1 (read_atStart hb)
  obtain ⟨h1, h2⟩ := shapeOk_atStart (startOk_shape (startP_ok (pubBy_start h)))
  obtain ⟨m1, m2⟩ := h2 n (by rw [hn]; exact List.mem_singleton.2 rfl)
  exact ⟨n, hn, Nat.pos_of_ne_zero m1, by rw [m2]; exact h1⟩

/-- **(a)** -/
theorem first_last_maskRows (h : pubPlain o pol lay KL = .ok Z)
    (gp : _root_.Desc.Plain.GPar) :
    0 < ((K1.firstPar Z.first gp).sent.getD
      ((K1.firstPar Z.first gp).sent.size - 1) default).shape.maskRows := by
  obtain ⟨n, hn, h1, -⟩ := pub_atStart h
  rw [sent_last Z.first gp n hn]
  exact h1

/-- **(b)** -/
theorem first_last_answers (h : pubPlain o pol lay KL = .ok Z)
    (gp : _root_.Desc.Plain.GPar) :
    1 ≤ ((K1.firstPar Z.first gp).sent.getD
      ((K1.firstPar Z.first gp).sent.size - 1) default).shape.answers := by
  obtain ⟨n, hn, -, h2⟩ := pub_atStart h
  rw [sent_last Z.first gp n hn]
  exact h2

/-- **(c), fenced**: at a first state without a mark. -/
theorem startS_atStart (h : pubPlain o pol lay KL = .ok Z) (z : InstPub)
    (hz : (startS Z z).failed = none) : (startS Z z).check.frame.shape.atStart ≠ [] := by
  obtain ⟨n, hn, -, -⟩ := pub_atStart h
  have e0 := startP_is (pubBy_start h)
  unfold startS at hz ⊢
  dsimp only at hz ⊢
  split at hz
  · rename_i hc
    rw [if_pos hc]
    show Z.s₀.check.frame.shape.atStart ≠ []
    rw [e0]
    show Z.first.shape.atStart ≠ []
    rw [hn]
    exact List.cons_ne_nil _ _
  · cases hz

/-- **(c) without the fence fails**: where the tests on the request reject, the first state is the
blank one, whose shape has nothing at the start. -/
theorem startS_blank (Z : Pub) (z : InstPub)
    (hz : ((Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V) = false) :
    startS Z z = S.blank ∧ (startS Z z).check.frame.shape.atStart = [] := by
  have e : startS Z z = S.blank := by
    unfold startS
    dsimp only
    rw [if_neg (by rw [hz]; exact Bool.false_ne_true)]
  exact ⟨e, by rw [e]; rfl⟩

/-- Such an instance there is: the empty request. -/
theorem startS_blank_empty (Z : Pub) (k : TableKey) :
    (startS Z ⟨ByteArray.empty, k⟩).check.frame.shape.atStart = [] := by
  refine (startS_blank Z _ ?_).2
  have e : (Verify.words32 ByteArray.empty).size = 0 := by
    simp [Verify.words32, fileWords]
  unfold S.reqOk S.withReq
  simp [e]

/-- The first segment's opening rejects from the blank state: its shape has no link. -/
theorem firstAtS_blank {Cl : Type} (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (m : S) :
    (K1.firstSegmentOpening q gp : VerifiableInference.Desc.Block S Cl).decide
      S.blank rs gs ≠ .ok m := by
  intro h
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨cd, hcd, -⟩ := bind_ok h
  unfold K1.firstOwn at hcd
  dsimp only at hcd
  obtain ⟨_, hn, -⟩ := bind_ok hcd
  have hb : (!S.blank.check.inLink && decide (S.blank.check.link < S.blank.check.links)) =
      false := by decide
  rw [hb] at hn
  simp [VerifiableInference.Desc.need] at hn

/-- **(c), as the make wants it**: where the first segment's opening accepts from the first state,
that state's shape has a notice at the start. -/
theorem firstAtS_atStart {Cl : Type} (h : pubPlain o pol lay KL = .ok Z) (z : InstPub)
    (q : Params.First) (gp : _root_.Desc.Plain.GPar) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (m : S)
    (hd : (K1.firstSegmentOpening q gp :
      VerifiableInference.Desc.Block S Cl).decide (startS Z z) rs gs = .ok m) :
    (startS Z z).check.frame.shape.atStart ≠ [] := by
  cases hz : ((Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V) with
  | false =>
    rw [(startS_blank Z z hz).1] at hd
    exact absurd hd (firstAtS_blank q gp rs gs m)
  | true =>
    refine startS_atStart h z ?_
    have e0 := startP_is (pubBy_start h)
    unfold startS
    dsimp only
    rw [if_pos hz]
    show Z.s₀.failed = none
    rw [e0]
    rfl

/-- The lots' letters hold the public part's first chain's parameters. -/
theorem lettersBy_first {mk : LinksBy} {s : S} {G : Ground} (h : lettersBy mk Z s = .ok G) :
    G.first = Z.first := by
  unfold lettersBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

theorem blankBy_first {mk : LinksBy} {G : Ground} (h : blankBy mk Z = some G) :
    G.first = Z.first := by
  have h' : (lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption =
      some G := h
  cases hx : lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    have hG : G' = G := Option.some.inj h'
    exact hG ▸ lettersBy_first hx

/-- **(a), at the lots' letters.** -/
theorem ground_last_maskRows (h : pubPlain o pol lay KL = .ok Z) {mk : LinksBy} {G : Ground}
    (hG : blankBy mk Z = some G) (gp : _root_.Desc.Plain.GPar) :
    0 < ((K1.firstPar G.first gp).sent.getD
      ((K1.firstPar G.first gp).sent.size - 1) default).shape.maskRows := by
  rw [blankBy_first hG]
  exact first_last_maskRows h gp

/-- **(b), at the lots' letters.** -/
theorem ground_last_answers (h : pubPlain o pol lay KL = .ok Z) {mk : LinksBy} {G : Ground}
    (hG : blankBy mk Z = some G) (gp : _root_.Desc.Plain.GPar) :
    1 ≤ ((K1.firstPar G.first gp).sent.getD
      ((K1.firstPar G.first gp).sent.size - 1) default).shape.answers := by
  rw [blankBy_first hG]
  exact first_last_answers h gp

end

end ProofFile.Law

#print axioms ProofFile.Law.read_atStart
#print axioms ProofFile.Law.proofRead_first
#print axioms ProofFile.Law.chainsOf_first
#print axioms ProofFile.Law.planned_first
#print axioms ProofFile.Law.pub_first_read
#print axioms ProofFile.Law.startP_is
#print axioms ProofFile.Law.shapeOk_atStart
#print axioms ProofFile.Law.startOk_shape
#print axioms ProofFile.Law.sent_last
#print axioms ProofFile.Law.pub_atStart
#print axioms ProofFile.Law.first_last_maskRows
#print axioms ProofFile.Law.first_last_answers
#print axioms ProofFile.Law.startS_atStart
#print axioms ProofFile.Law.startS_blank
#print axioms ProofFile.Law.startS_blank_empty
#print axioms ProofFile.Law.firstAtS_blank
#print axioms ProofFile.Law.firstAtS_atStart
#print axioms ProofFile.Law.lettersBy_first
#print axioms ProofFile.Law.blankBy_first
#print axioms ProofFile.Law.ground_last_maskRows
#print axioms ProofFile.Law.ground_last_answers
