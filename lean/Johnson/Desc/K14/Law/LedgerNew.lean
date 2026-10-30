-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerNew.lean: WHAT A YES OF A SENDING ASKS AND WRITES FOR CERTAIN, AS TESTS
BESIDE shapeK. A sending's decision (K1's decideSend, Johnson/Desc/K1/Own.lean) REFUSES a record
whose codes are not the plan's, and writes each sampled message with the plan's shape, the mark, and
as many sample rows as it has answers. So two tests with code on the shared chain's record are
EARNED at its two sendings, at no price: what the tie of the two readers
(Johnson/Desc/K14/Law/LedgerReader.lean) and the last chain's door ask of the shared chain's last
record.

  decideSend_two, send_writes   K1's decision has two rounds; what it asks of the codes and writes
                  at a sampled message.
  sendAt_writes, sendAt_codes   the like at this chain's own sendings.
  codY, handsOn_codY   "the record's codes are the plan's" from border 3 on: earned at "send o_u",
                  handed on by the kind's blocks to border 9, and from 11 to 12.
  omY, hands_omY  "the message nO has the shape sO, the mark, and as many sample rows as sO has
                  answers" from border 6 on: earned at "send o_omega", where the record has nO
                  messages in front (asked of the test laid beside: membX says
                  it); handed on likewise.
  msgY, hands_msgY, msgY_onGu, msgY_onGomega   THE LIKE FOR EVERY SAMPLED MESSAGE OF EITHER SENDING
                  (o_u: number 0 behind border 2; o_sp: nO + 1 behind 5; omY is msgY at o_omega):
                  the record's message has THE PLAN's WHOLE SHAPE, the mark and its sample rows,
                  from its sending to the chain's last border.
  codY_onGu … omY_onGomega   OVER THE TWO PROXIMITY TESTS (9 to 10, 10 to 11), in the tests' own
                  decide-form, from onGu_leaves | onGomega_leaves
                  (Johnson/Desc/K12/Coin/SamplesThrough.lean). omY over the test on G_u wants that
                  the first mask is not o_omega.
  codX_first … codX_onGomega, handsOn_codX   THE CODES' LAW ALONG THE WHOLE CHAIN: codX
                  (Johnson/Desc/K14/Law/LedgerOne.lean: the record's codes are the plan's, at every
                  border) from the chain's first record BY MAKE, through the front, each of the
                  kind's eight ("LIN point" too), the two tests and the end.
  one_answer, shape_omega, shape_split, door_four_five   from omY to the door's two clauses: a
                  sampled message of a place that meets K1's condition has ONE answer; the first and
                  the second message of "send o_omega" have the plan's shapes for o_omega and o_sp.
WHAT WHOEVER LAYS SUCH A TEST BESIDE shapeK OWES, IN ALL: at the chain's first record, at the front
and at "LIN point" (codY and omY are true there for nothing: k ≤ 2, k ≤ 5) · at our eight clauses
(HandsOn | HandsAt, Johnson/Desc/K14/Law/LedgerFilled.lean) · AT THE TWO TESTS' CLAUSES: the four
lemmas here are the decide-form; that they are LAID into h9 | h10 (clause_beside at
nine_paid | ten_paid) is typed by nobody yet.
What is not claimed. No member. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerFilled
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend sendOwn decideSend_iff shapesOf shapeAt sampledAt
  outs_spec wr rowsOf rowsOf_size seedsOf answersIn cutSeeds_length msgAt_answers_le outs)
open Desc.K14.Law.Fence (KeepsSmp keepsSmp_k14 blocks_two behindU_book behindOmega_book)

section
variable {L : Type}

/-- K1's decision says yes at two rounds alone. -/
theorem decideSend_two (P : VerifiableInference.Desc.K1.Par) (owed : Option Nat) (d : DState L)
    (rs : List Fmt.RoundView) (z : Array Nat × DState L) (h : decideSend P owed d rs = .ok z) :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  unfold decideSend at h
  split at h
  · exact ⟨_, _, rfl⟩
  · cases h

/-- **What a yes asks of the codes, and writes at a sampled message.** -/
theorem send_writes (P : VerifiableInference.Desc.K1.Par) (owed : Option Nat) (d d' : DState L)
    (rs : List Fmt.RoundView) (ids : Array Nat) (hyes : decideSend P owed d rs = .ok (ids, d'))
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    d.st.codes = P.codes ∧ d'.st.codes = P.codes ∧
      ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.shape = shapeAt P k ∧
        x.sampled = true ∧ x.sampleRows.size = (shapeAt P k).answers := by
  obtain ⟨r₁, r₂, rfl⟩ := decideSend_two P owed d rs _ hyes
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (VerifiableInference.Desc.K1.behind P d (seedsOf P r₁)
      (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  refine ⟨hc, hc, _, hx, ?_, by simp [wr, hk'], ?_⟩
  · unfold wr
    split <;> rfl
  · have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    refine rowsOf_size _ _ _ _ _ ?_ hy
    rw [show (seedsOf P r₁).length = P.seeds from cutSeeds_length _ _ _]
    exact msgAt_answers_le P k

end

/-- **At this chain's own sendings.** -/
theorem sendAt_writes (P : P14) (n : String) (K : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n K inFront groups behind).decide d rs gs = .ok d')
    (k : Fin (shapesOf K).length) (hk : sampledAt K k) :
    d.st.codes = K.codes ∧ d'.st.codes = K.codes ∧
      ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.shape = shapeAt K k ∧
        x.sampled = true ∧ x.sampleRows.size = (shapeAt K k).answers := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨e1, _, _⟩ := hb _ _ _ (named_some h)
  rw [e1]
  exact send_writes K none _ x2 rs ids hx k hk

/-- The codes alone: asked in front, kept behind. -/
theorem sendAt_codes (P : P14) (n : String) (K : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n K inFront groups behind).decide d rs gs = .ok d') :
    d.st.codes = K.codes ∧ d'.st.codes = K.codes := by
  have ks := Fence.sendAt_smp P n K inFront groups behind hb d d' rs gs h
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨r₁, r₂, rfl⟩ := decideSend_two K none _ rs _ hx
  obtain ⟨⟨_, hc, _⟩, _⟩ := (decideSend_iff K none _ x2 r₁ r₂ ids).1 hx
  have hc' : d.st.codes = K.codes := hc
  exact ⟨hc', ks.1.trans hc'⟩

/-- **"The record's codes are the plan's"**, from border 3 on. -/
def codY (Q : P14) : ℕ → St → Bool := fun k s => decide (k ≤ 2) || decide (s.st.codes = Q.codes)

theorem codY_iff (Q : P14) (k : ℕ) (s : St) : codY Q k s = true ↔ k ≤ 2 ∨ s.st.codes = Q.codes := by
  unfold codY
  rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]

/-- **It is earned at "send o_u" and handed on by every later block of the kind.** -/
theorem handsOn_codY (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] (codY Q) := by
  refine ⟨fun i b hi hb d d' rs gs h hx => (codY_iff Q _ d').2 (Or.inr ?_),
    fun s z h => (codY_iff Q 8 _).2 (Or.inr (((codY_iff Q 7 s).1 h).resolve_left (by omega))),
    fun s h => (codY_iff Q 12 s).2 (Or.inr (((codY_iff Q 11 s).1 h).resolve_left (by omega)))⟩
  by_cases h1 : i = 1
  · subst h1
    obtain rfl : b2 = b := Option.some.inj hb
    obtain ⟨u, _, e2, _⟩ := blocks_two Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
    rw [e2] at h
    exact (sendAt_codes Q _ _ _ _ _ (behindU_book Q.par) d d' rs gs h).2
  · have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) d d' rs gs h
    exact ks.1.trans (((codY_iff Q _ d).1 hx).resolve_left (by omega))

/-- **"The message number nO has the shape sO, the mark, and as many sample rows as answers"**, from
border 6 on. -/
def omY (sO : OracleShape) (nO : ℕ) : ℕ → St → Bool := fun k s =>
  decide (k ≤ 5) || match s.st.oracles[nO]? with
    | some x => decide (x.shape = sO) && x.sampled && decide (x.sampleRows.size = sO.answers)
    | none => false

theorem omY_iff (sO : OracleShape) (nO k : ℕ) (s : St) : omY sO nO k s = true ↔
    k ≤ 5 ∨ ∃ x, s.st.oracles[nO]? = some x ∧ x.shape = sO ∧ x.sampled = true ∧
      x.sampleRows.size = sO.answers := by
  unfold omY
  rw [Bool.or_eq_true, decide_eq_true_iff]
  refine or_congr_right ?_
  cases s.st.oracles[nO]? with
  | none => simp
  | some x => simp [and_assoc]

/-- **It is earned at "send o_omega"**, where the test X laid beside says that the record has nO
messages in front, **and handed on by every later block of the kind.** -/
theorem hands_omY (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (X : ℕ → St → Bool)
    (hX : HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] X) (nO : ℕ)
    (hsz : ∀ d, X 5 d = true → d.st.oracles.size = nO)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩) :
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8]
      fun k s => X k s && omY (shapeAt (parO Q) ⟨0, h0⟩) nO k s := by
  refine ⟨fun i b hi hb d d' rs gs h hxy => ?_, fun s z hxy => ?_, fun s hxy => ?_⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    refine Bool.and_eq_true_iff.2 ⟨hX.step i b hi hb d d' rs gs h hx, (omY_iff _ nO _ d').2 ?_⟩
    by_cases h3 : i + 2 ≤ 5
    · exact Or.inl h3
    refine Or.inr ?_
    by_cases h4 : i = 4
    · subst h4
      obtain rfl : b5 = b := Option.some.inj hb
      obtain ⟨u, _, _, e5⟩ := blocks_two Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
      rw [e5] at h
      obtain ⟨_, _, x, h1, h2⟩ := sendAt_writes Q _ _ _ _ _ (behindOmega_book Q.par) d d' rs gs h
        ⟨0, h0⟩ hk
      rw [hsz d hx] at h1
      exact ⟨x, h1, h2⟩
    · obtain ⟨x, h1, h2, h5, h6⟩ := ((omY_iff _ nO _ d).1 hy).resolve_left (by omega)
      have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) d d' rs gs h
      have hlt : nO < d.st.oracles.size := (Array.getElem?_eq_some_iff.1 h1).1
      have e := ks.2.2 nO hlt
      rw [h1, Option.map_some] at e
      obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
      have e1 : x'.shape = x.shape := congrArg (·.1) ex
      have e2 : x'.sampled = x.sampled := congrArg (·.2.1) ex
      have e3 : x'.sampleRows = x.sampleRows := congrArg (·.2.2) ex
      exact ⟨x', hx', e1.trans h2, e2.trans h5, by rw [e3]; exact h6⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z hx,
      (omY_iff _ nO 8 _).2 (Or.inr (((omY_iff _ nO 7 s).1 hy).resolve_left (by omega)))⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.last s hx,
      (omY_iff _ nO 12 s).2 (Or.inr (((omY_iff _ nO 11 s).1 hy).resolve_left (by omega)))⟩

/-! ## The like for every sampled message of either sending: msgY -/

/-- **"The message number o has the shape sh, the mark, and as many sample rows as sh has
answers"**, behind border k₀. (omY sO nO is msgY sO nO 5.) -/
def msgY (sh : OracleShape) (o k₀ : ℕ) : ℕ → St → Bool := fun k s =>
  decide (k ≤ k₀) || match s.st.oracles[o]? with
    | some x => decide (x.shape = sh) && x.sampled && decide (x.sampleRows.size = sh.answers)
    | none => false

theorem omY_is (sO : OracleShape) (nO : ℕ) : omY sO nO = msgY sO nO 5 := rfl

theorem msgY_iff (sh : OracleShape) (o k₀ k : ℕ) (s : St) : msgY sh o k₀ k s = true ↔
    k ≤ k₀ ∨ ∃ x, s.st.oracles[o]? = some x ∧ x.shape = sh ∧ x.sampled = true ∧
      x.sampleRows.size = sh.answers := by
  unfold msgY
  rw [Bool.or_eq_true, decide_eq_true_iff]
  refine or_congr_right ?_
  cases s.st.oracles[o]? with
  | none => simp
  | some x => simp [and_assoc]

/-- What a reader of a sample reads of a message stands: so does msgY. -/
theorem msgY_of_part (sh : OracleShape) (o k₀ j k : ℕ) (hj : k₀ < j) (d d' : St)
    (e : (d'.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)) =
      (d.st.oracles[o]?).map (fun x : OnBytes.Oracle => (x.shape, x.sampled, x.sampleRows)))
    (hx : msgY sh o k₀ j d = true) : msgY sh o k₀ k d' = true := by
  obtain ⟨x, h1, h2, h5, h6⟩ := ((msgY_iff sh o k₀ j d).1 hx).resolve_left (by omega)
  rw [h1, Option.map_some] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  have e1 : x'.shape = x.shape := congrArg (·.1) ex
  have e2 : x'.sampled = x.sampled := congrArg (·.2.1) ex
  have e3 : x'.sampleRows = x.sampleRows := congrArg (·.2.2) ex
  exact (msgY_iff sh o k₀ k d').2 (Or.inr ⟨x', hx', e1.trans h2, e2.trans h5, by rw [e3]; exact h6⟩)

/-- **It is earned at the sending that writes the message**, where the test X laid beside says how
many messages the record has in front, **and handed on by every later block of the kind.** i₀: the
sending's place among the kind's eight, from 0. -/
theorem hands_msgY (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (X : ℕ → St → Bool)
    (hX : HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] X) (i₀ : ℕ) (n : String)
    (K : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St)
    (hbk : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (hblk : [b1, b2, b3, b4, b5, b6, b7, b8][i₀]? = some (sendAt Q n K inFront groups behind))
    (base : ℕ) (hsz : ∀ d, X (i₀ + 1) d = true → d.st.oracles.size = base)
    (k : Fin (shapesOf K).length) (hk : sampledAt K k) (h6 : i₀ + 1 ≤ 6) :
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8]
      fun j s => X j s && msgY (shapeAt K k) (base + k.val) (i₀ + 1) j s := by
  refine ⟨fun i b hi hb d d' rs gs h hxy => ?_, fun s z hxy => ?_, fun s hxy => ?_⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    refine Bool.and_eq_true_iff.2 ⟨hX.step i b hi hb d d' rs gs h hx, (msgY_iff _ _ _ _ d').2 ?_⟩
    by_cases h3 : i + 2 ≤ i₀ + 1
    · exact Or.inl h3
    refine Or.inr ?_
    by_cases h4 : i = i₀
    · subst h4
      obtain rfl : sendAt Q n K inFront groups behind = b := Option.some.inj (hblk.symm.trans hb)
      obtain ⟨_, _, x, h1, h2⟩ := sendAt_writes Q _ _ _ _ _ hbk d d' rs gs h k hk
      rw [hsz d hx] at h1
      exact ⟨x, h1, h2⟩
    · have ks := keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) d d' rs gs h
      obtain ⟨x, h1, _⟩ := ((msgY_iff _ _ _ _ d).1 hy).resolve_left (by omega)
      exact ((msgY_iff _ _ _ (i + 2) d').1 (msgY_of_part _ _ _ (i + 1) (i + 2) (by omega) d d'
        (ks.2.2 _ (Array.getElem?_eq_some_iff.1 h1).1) hy)).resolve_left (by omega)
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.zeta s z hx,
      (msgY_iff _ _ _ 8 _).2 (Or.inr (((msgY_iff _ _ _ 7 s).1 hy).resolve_left (by omega)))⟩
  · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.1 hxy
    exact Bool.and_eq_true_iff.2 ⟨hX.last s hx,
      (msgY_iff _ _ _ 12 s).2 (Or.inr (((msgY_iff _ _ _ 11 s).1 hy).resolve_left (by omega)))⟩

/-! ## Over the two proximity tests (borders 9 → 10 → 11), in the tests' own decide-form -/

section
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (onGu_leaves onGomega_leaves smpPart)

/-- The test on G_u hands codY on. -/
theorem codY_onGu (Q : P14) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : codY Q 9 d = true) : codY Q 10 d' = true :=
  (codY_iff Q 10 d').2 (Or.inr ((onGu_leaves p he ha d d' rs gs h).1.trans
    (((codY_iff Q 9 d).1 hx).resolve_left (by omega))))

/-- The test on G_omega hands codY on. -/
theorem codY_onGomega (Q : P14) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : codY Q 10 d = true) : codY Q 11 d' = true :=
  (codY_iff Q 11 d').2 (Or.inr ((onGomega_leaves p he ha d d' rs gs h).1.trans
    (((codY_iff Q 10 d).1 hx).resolve_left (by omega))))

/-- What a reader of a sample reads of a message stands: so does omY. -/
theorem omY_of_part (sO : OracleShape) (nO j k : ℕ) (hj : 5 < j) (d d' : St)
    (e : (d'.st.oracles[nO]?).map smpPart = (d.st.oracles[nO]?).map smpPart)
    (hx : omY sO nO j d = true) : omY sO nO k d' = true := by
  obtain ⟨x, h1, h2, h5, h6⟩ := ((omY_iff sO nO j d).1 hx).resolve_left (by omega)
  rw [h1, Option.map_some] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  have e1 : x'.shape = x.shape := congrArg (·.1) ex
  have e2 : x'.sampled = x.sampled := congrArg (·.2.1) ex
  have e3 : x'.sampleRows = x.sampleRows := congrArg (·.2.2) ex
  exact (omY_iff sO nO k d').2 (Or.inr ⟨x', hx', e1.trans h2, e2.trans h5, by rw [e3]; exact h6⟩)

/-- The test on G_u hands omY on, WHERE THE FIRST MASK IS NOT o_omega (the test takes the first
mask: membX 9 says that the record notes the message 1 for it; nO is the number of
o_u's sending's messages: 2 where the masks go ahead). -/
theorem omY_onGu (sO : OracleShape) (nO : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hm : d.loc.firstMask ≠ some nO) (hx : omY sO nO 9 d = true) : omY sO nO 10 d' = true := by
  obtain ⟨x, h1, _⟩ := ((omY_iff sO nO 9 d).1 hx).resolve_left (by omega)
  exact omY_of_part sO nO 9 10 (by omega) d d'
    ((onGu_leaves p he ha d d' rs gs h).2.1 nO (Array.getElem?_eq_some_iff.1 h1).1 hm) hx

/-- The test on G_u hands msgY on, where the first mask is not that message. -/
theorem msgY_onGu (sh : OracleShape) (o k₀ : ℕ) (h9 : k₀ < 9) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hm : d.loc.firstMask ≠ some o) (hx : msgY sh o k₀ 9 d = true) :
    msgY sh o k₀ 10 d' = true := by
  obtain ⟨x, h1, _⟩ := ((msgY_iff sh o k₀ 9 d).1 hx).resolve_left (by omega)
  exact msgY_of_part sh o k₀ 9 10 h9 d d'
    ((onGu_leaves p he ha d d' rs gs h).2.1 o (Array.getElem?_eq_some_iff.1 h1).1 hm) hx

/-- The test on G_omega hands msgY on. -/
theorem msgY_onGomega (sh : OracleShape) (o k₀ : ℕ) (h9 : k₀ < 10) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : msgY sh o k₀ 10 d = true) : msgY sh o k₀ 11 d' = true := by
  obtain ⟨x, h1, _⟩ := ((msgY_iff sh o k₀ 10 d).1 hx).resolve_left (by omega)
  exact msgY_of_part sh o k₀ 10 11 h9 d d'
    ((onGomega_leaves p he ha d d' rs gs h).2.1 o (Array.getElem?_eq_some_iff.1 h1).1) hx

/-- The test on G_omega hands omY on. -/
theorem omY_onGomega (sO : OracleShape) (nO : ℕ) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : omY sO nO 10 d = true) : omY sO nO 11 d' = true := by
  obtain ⟨x, h1, _⟩ := ((omY_iff sO nO 10 d).1 hx).resolve_left (by omega)
  exact omY_of_part sO nO 10 11 (by omega) d d'
    ((onGomega_leaves p he ha d d' rs gs h).2.1 nO (Array.getElem?_eq_some_iff.1 h1).1) hx

end

/-! ## The codes' law along the whole chain: codX (Johnson/Desc/K14/Law/LedgerOne.lean) at all
thirteen borders, from the chain's first record BY MAKE -/

section
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Coin (onGu_leaves onGomega_leaves)
open Desc.K14.Law.Fence (bookStep_front)

/-- The chain's first record has the plan's codes: by make. -/
theorem codX_first (Q : P14) (key : TableKey) : codX Q 0 (first Q.codes key) = true :=
  (codX_iff Q 0 _).2 rfl

/-- The front leaves the record. -/
theorem codX_front (Q : P14) (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hx : codX Q 0 d = true) : codX Q 1 d' = true := by
  rw [bookStep_front c d d' rs gs h]
  exact hx

/-- Each of the kind's eight, "LIN point" too, hands it on, from any border to any. -/
theorem codX_k14 (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (j k : ℕ) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hx : codX Q j d = true) : codX Q k d' = true :=
  codX_codes Q j k d d' (keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb d d' rs gs h).1 hx

theorem handsOn_codX (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    HandsOn [b1, b2, b3, b4, b5, b6, b7, b8] (codX Q) :=
  ⟨fun _ b _ hb d d' rs gs h hx =>
      codX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b (List.mem_of_getElem? hb) _ _ d d' rs gs h hx,
    fun _ _ h => h, fun _ h => h⟩

/-- The two proximity tests hand it on. -/
theorem codX_onGu (Q : P14) (p : P12) (he : p.early = true) (ha : p.answers = 1) (j k : ℕ)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : codX Q j d = true) : codX Q k d' = true :=
  codX_codes Q j k d d' (onGu_leaves p he ha d d' rs gs h).1 hx

theorem codX_onGomega (Q : P14) (p : P12) (he : p.early = true) (ha : p.answers = 1) (j k : ℕ)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d')
    (hx : codX Q j d = true) : codX Q k d' = true :=
  codX_codes Q j k d d' (onGomega_leaves p he ha d d' rs gs h).1 hx

/-- It gives codY at every border. -/
theorem codY_of_codX (Q : P14) (j k : ℕ) (s : St) (h : codX Q j s = true) : codY Q k s = true :=
  (codY_iff Q k s).2 (Or.inr ((codX_iff Q j s).1 h))

end

/-! ## From omY to the last chain's door's two clauses: two facts of the plan -/

/-- A sampled message of a place that meets K1's condition has ONE answer. -/
theorem one_answer (P : VerifiableInference.Desc.K1.Par) (rad : ℕ → ℕ)
    (hC : VerifiableInference.Desc.K1.condPort P rad = true) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) : (shapeAt P k).answers = 1 :=
  (VerifiableInference.Desc.K1.cond_tie P rad hC k hk).one

/-- The first message of "send o_omega" has the plan's shape for o_omega. -/
theorem shape_omega (Q : P14) (h0 : 0 < (shapesOf (parO Q)).length) :
    shapeAt (parO Q) ⟨0, h0⟩ = Q.par.S.omega := by
  have e : (shapesOf (parO Q))[0]? = some Q.par.S.omega := by
    cases h : Q.S.sharedSplitNeeded <;>
      simp [shapesOf, parO, parK1, withOmega, linMessageOmega, h,
        VerifiableInference.Desc.K1.Par.sent, P14.par]
  unfold shapeAt
  exact Option.some.inj ((List.getElem?_eq_getElem h0).symm.trans e)

/-- The second message of "send o_omega", where the chain has a split, has the plan's shape for
o_sp. -/
theorem shape_split (Q : P14) (hS : Q.S.sharedSplitNeeded = true)
    (h1 : 1 < (shapesOf (parO Q)).length) : shapeAt (parO Q) ⟨1, h1⟩ = Q.par.S.sharedSplit := by
  have e : (shapesOf (parO Q))[1]? = some Q.par.S.sharedSplit := by
    simp [shapesOf, parO, parK1, withOmega, linMessageOmega, hS,
      VerifiableInference.Desc.K1.Par.sent, P14.par]
  unfold shapeAt
  exact Option.some.inj ((List.getElem?_eq_getElem h1).symm.trans e)

/-- **The door's two clauses**: o_omega's own shape is the first of its sending's, and it has ONE
sample row. -/
theorem door_four_five (Q : P14) (rad : ℕ → ℕ)
    (hC : VerifiableInference.Desc.K1.condPort (parO Q) rad = true)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩) (nO k : ℕ) (h5 : 5 < k)
    (d : St) (hZ : omY (shapeAt (parO Q) ⟨0, h0⟩) nO k d = true) :
    ∃ x, d.st.oracles[nO]? = some x ∧ x.shape = shapeAt (parO Q) ⟨0, h0⟩ ∧
      x.sampleRows.size = 1 := by
  obtain ⟨x, h1, h2, _, h6⟩ := ((omY_iff _ nO k d).1 hZ).resolve_left (by omega)
  exact ⟨x, h1, h2, h6.trans (one_answer (parO Q) rad hC ⟨0, h0⟩ hk)⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.codX_first
#print axioms Desc.K14.Law.codX_front
#print axioms Desc.K14.Law.codX_k14
#print axioms Desc.K14.Law.handsOn_codX
#print axioms Desc.K14.Law.codX_onGu
#print axioms Desc.K14.Law.codX_onGomega
#print axioms Desc.K14.Law.hands_msgY
#print axioms Desc.K14.Law.msgY_onGu
#print axioms Desc.K14.Law.msgY_onGomega
#print axioms Desc.K14.Law.codY_onGu
#print axioms Desc.K14.Law.codY_onGomega
#print axioms Desc.K14.Law.omY_onGu
#print axioms Desc.K14.Law.omY_onGomega
#print axioms Desc.K14.Law.shape_omega
#print axioms Desc.K14.Law.shape_split
#print axioms Desc.K14.Law.door_four_five
#print axioms Desc.K14.Law.sendAt_codes
#print axioms Desc.K14.Law.handsOn_codY
#print axioms Desc.K14.Law.hands_omY
#print axioms Desc.K14.Law.send_writes
#print axioms Desc.K14.Law.sendAt_writes
