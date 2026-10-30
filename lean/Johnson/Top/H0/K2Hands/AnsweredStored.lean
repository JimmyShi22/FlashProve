-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/AnsweredStored.lean: the code switch's law: «EVERY MESSAGE WHOSE SHAPE COUNTS
AN ANSWER HAS A STORED SAMPLE ROW», an invariant of the statement between the sub-protocols of the
first chain; and what it gives in front of a code switch. A law file; no running text imports it.

Why. One of the tests with code that the law asks of a front (storedB,
Johnson/G/SwitchSampleTop.lean) says of each kept old message: it has the
typed entry's kept member's shape, AND A STORED SAMPLE ROW. The second half is no public number. It
follows from this invariant and the first half, since a kept member's shape counts one answer.
Why this sentence and not one on a group's members or on the mark `sampled`: a sending receives its
messages and admits the samples of all that count an answer INSIDE ONE sub-protocol; so between
sub-protocols the sentence holds of every message, joined or not, and it reads of a message its
shape and its stored rows alone: what SameRows (SampleChain.lean) keeps. THE FOLD's FRESH MASK,
which a switch's or a link's first sending announces and nobody samples or joins, counts NO answer
by its notice's own text (OnBytes/Iop/Fold.lean:289-291: answers := 0; foldMask_no_answer, by rfl):
the sentence says nothing of it. answered_kept leans on no such fact: it holds at every yes.

  AnsweredStored St   the invariant.
  answered_first      at the chain's first state: it has no message.
  answered_rows       SameRows A B carries it.
  NewAnswered n St, answered_oldRows   OldRows A B, with the sentence at B's messages from n on.
  answered_kept, answered_yes   a yes of the kind K2's own decision keeps it, and makes it at the
                      new messages (by K2Hears/SentRows.lean's sent_rows).
  Ans s, keepsAns_of_rows, keepsAns_k2, keepsAns_pureAt   in ChainKeeps.lean's letters; K2's blocks
                      as supplied.
  ans_at_pre          at the verifier's state behind the fold over blocks that all keep it.
  stored_of_shape     a message with a shape that counts an answer has a stored row: storedB's
                      second half from its first.
Kin: OnBytes.Means.SampledMembers (every member of a group is marked as sampled) and NoneYet (a
message that is not marked has no sample row), Johnson/Desc/Means/Entry.lean | FrameKeeps.lean: on
the mark; neither says that a row is there.
Limits. That the other parts of the first chain keep it is their files' debt: a block with SameRows
pays by answered_rows; a block that receives a message without sampling it must show that its notice
counts no answer; K1's three sendings owe the like of answered_kept. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.SampleSeatK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Keeps1
open _root_.Tw.K2 (switchNotices sendByL8)

/-- **Every message whose shape counts an answer has a stored sample row.** -/
def AnsweredStored (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), St.oracles[o]? = some x → x.shape.answers ≠ 0 →
    x.sampleRows.size ≠ 0

theorem answered_first (codes : Codes) (shape : Params.ReqShape) (layout : Params.ReqLayout) :
    AnsweredStored (S.firstRecord codes shape layout).st := by
  intro o x hx _
  exact absurd hx (by simp [S.firstRecord])

theorem answered_congr {A B : Statement} (ho : B.oracles = A.oracles) (h : AnsweredStored A) :
    AnsweredStored B := by
  intro o x hx
  rw [ho] at hx
  exact h o x hx

theorem answered_rows {A B : Statement} (h : SameRows A B) (hA : AnsweredStored A) :
    AnsweredStored B := by
  intro o x hx ha
  have e := h.2 o
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
  obtain ⟨e1, e3⟩ := Prod.mk.inj e0
  rw [← e3]
  exact hA o x0 hx0 (by rw [e1]; exact ha)

/-- The sentence at the messages from number n on. -/
def NewAnswered (n : Nat) (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), n ≤ o → St.oracles[o]? = some x → x.shape.answers ≠ 0 →
    x.sampleRows.size ≠ 0

theorem answered_oldRows {A B : Statement} (h : OldRows A B) (hn : NewAnswered A.oracles.size B)
    (hA : AnsweredStored A) : AnsweredStored B := by
  intro o x hx ha
  by_cases ho : o < A.oracles.size
  · have e := h.2 o ho
    rw [hx] at e
    obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
    obtain ⟨e1, e3⟩ := Prod.mk.inj e0
    rw [← e3]
    exact hA o x0 hx0 (by rw [e1]; exact ha)
  · exact hn o x (Nat.le_of_not_lt ho) hx ha

/-- The fold's fresh mask, which a switch's sending announces and nobody samples, counts no answer:
so the sentence says nothing of it. -/
theorem foldMask_no_answer (F : FoldShape) : (foldMaskNotice F).shape.answers = 0 := rfl

/-- **A yes keeps it, and makes it at the new messages.** -/
theorem answered_kept {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (h : AnsweredStored x.st) :
    AnsweredStored s'.st := by
  intro o xo hxo han
  have T := A.same.trans A.tables
  have hsh := T.shape o
  have hsm := T.samples o
  rw [hxo] at hsh hsm
  simp only [Option.map_some] at hsh hsm
  by_cases ho : o < x.st.oracles.size
  · rw [A.sent.old o ho] at hsh hsm
    obtain ⟨x0, hx0, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    obtain ⟨x1, hx1, e2⟩ := Option.map_eq_some_iff.1 hsm.symm
    rw [hx0] at hx1
    obtain rfl := Option.some.inj hx1
    rw [← e2]
    exact h o x0 hx0 (by rw [e1]; exact han)
  · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
    obtain ⟨bits, answers, seeds, -, -, hall, -⟩ := sent_rows A.sentBy
    rw [A.sent.shape i] at hsh
    obtain ⟨n, hn, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    have ha : n.shape.answers ≠ 0 := by rw [e1]; exact han
    obtain ⟨-, rws, hr, hR⟩ := hall i n hn ha
    rw [hr] at hsm
    have e2 := Option.some.inj hsm
    rw [e2, hR.1]
    exact ha

theorem answered_yes (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (s' : S) (h : decideWith sendByL8 p s [r₁, r₂] gs = .ok s') (hg : AnsweredStored s.st) :
    AnsweredStored s'.st := by
  obtain ⟨x, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  exact answered_kept A (answered_congr (front_tables A.front).2 hg)

/-! ## In ChainKeeps.lean's letters -/

variable {Cl : Type}

/-- The invariant at a state of the verifier. -/
def Ans (s : S) : Prop := AnsweredStored s.st

/-- No premise on the rounds is needed. -/
abbrev KeepsAns (b : Block S Cl) : Prop := KeepsD (fun _ => True) Ans b

theorem keepsAns_of_rows {b : Block S Cl}
    (h : ∀ s s' rs gs, b.decide s rs gs = .ok s' → SameRows s.st s'.st) : KeepsAns b :=
  fun s s' rs gs _ hy hg => answered_rows (h s s' rs gs hy) hg

theorem keepsAns_k2 (p : P2) : KeepsAns (codeSwitchKind p : Block S Cl) := by
  intro s s' rs gs _ h hg
  have h' : decideWith sendByL8 p s rs gs = .ok s' := h
  have h2 : rs.length = 2 := two _ p s rs gs s' h'
  match rs, h2, h' with
  | [r₁, r₂], _, h' => exact answered_yes p s r₁ r₂ gs s' h' hg

theorem ansFn {f : S → Except String S} (h : ∀ s s', f s = .ok s' → SameRows s.st s'.st) :
    ∀ s s', f s = .ok s' → Ans s → Ans s' := fun a b hy hg => answered_rows (h a b hy) hg

theorem keepsAns_headOpened (name : String) (place : VerifiableInference.Desc.Place)
    (P : HeadPar) : KeepsAns (headOpened name place P : Block S Cl) :=
  fun _ _ _ _ _ hy hg => answered_rows (headOpenQ_smp hy) hg

/-- **Every block that the lot's maker makes at a place of the kind.** -/
theorem keepsAns_pureAt (G : ProofFile.Ground) (x : ProofFile.Spot × P2) (b : Block S Unit)
    (h : P1K2.pureAt (fun _ _ => some none) G x = some b) : KeepsAns b := by
  unfold P1K2.pureAt at h
  dsimp only at h
  split at h
  · cases h
    exact keepsD_under (b := ((VerifiableInference.Desc.roundlessBlock (x.2.name ++ ": front")
        x.2.place.chain x.2.place.link x.2.place.piece finishFrontQ).andThen x.2.name
        (codeSwitchKind x.2)).andThen x.2.name (VerifiableInference.Desc.roundlessBlock (x.2.name ++ ": behind")
                    x.2.place.chain x.2.place.link x.2.place.piece finishBehindQ)) rfl
      (keepsD_andThen _
        (keepsD_andThen _ (keepsD_quiet (ansFn fun _ _ => finishFrontQ_smp)) (keepsAns_k2 x.2))
        (keepsD_quiet (ansFn fun _ _ => finishBehindQ_smp)))
  · obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact keepsD_under rfl (keepsD_andThen x.1.name (keepsAns_k2 x.2)
      (keepsAns_headOpened x.1.name x.1.place P))
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l, -, ho⟩ := Option.bind_eq_some_iff.1 ho
    cases ho
    exact keepsD_under (b := (codeSwitchKind x.2 : Block S Unit)) rfl (keepsAns_k2 x.2)

theorem ans_at_pre {ft : Nat} {pre : List (Block S Cl)} (hb : ∀ b ∈ pre, KeepsAns b) {s m : S}
    {rs rs' : List Fmt.RoundView} {cols cols' : List Col}
    (h : foldBlocks ft pre s rs cols = .ok (m, rs', cols')) (hs : AnsweredStored s.st) :
    AnsweredStored m.st :=
  fold_keeps (R := fun _ => True) (P := Ans) (fun _ _ => trivial) ft pre s m rs rs' cols cols' hb
    (fun _ _ => trivial) h hs

/-! ## What it gives in front of a code switch -/

/-- **The second half of the test on the kept old messages, from its first.** sh: the typed
entry's kept member's shape. -/
theorem stored_of_shape {St : Statement} (h : AnsweredStored St) {o : Nat} {x : OnBytes.Oracle}
    {sh : OracleShape} (hx : St.oracles[o]? = some x) (hs : x.shape = sh) (ha : sh.answers = 1) :
    x.sampleRows.size ≠ 0 := h o x hx (by rw [hs, ha]; exact Nat.one_ne_zero)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.answered_yes
#print axioms VerifiableInference.Desc.First.K2.keepsAns_pureAt
#print axioms VerifiableInference.Desc.First.K2.ans_at_pre
#print axioms VerifiableInference.Desc.First.K2.stored_of_shape
