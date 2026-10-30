-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0AtWords.lean: WHAT IS LEFT AT ROW 0 OF THE LAST CHAIN's TABLE
(RowZeroLeft, Johnson/Desc/Third/Law/Row0AtTable.lean) AT A CLOSED FAMILY OF FENCE, WORDS AND
READERS: the terms wordsLast | omegaWords | wWords and the fence AtStart
(Johnson/Desc/Sound/WordsAt.lean · ReadsAt.lean), EACH READ AT WHAT WAS HANDED TO THE CHAIN; the
shared chain's record is K14's own (St), the first chain's is read by a letter fs. SO THAT reads ·
fence · atDot · dot ARE HAD TOGETHER, BY LEAN, from "the record in front is the start's of what was
handed" and four public conditions. Definitions, one structure of Prop, theorems.

WHY. A reader of Omega's words that is not handed the shared chain's record cannot read that
record's book: with it the fields reads, fence and dot could not be met together. Here Omega's
reader is omegaWords at the shared record's own statement, book and
number.

OBJECT   startAtEnds p (Johnson/Desc/Third/Border.lean) · Desc.K14.ended
         (Johnson/Desc/K14/Blocks.lean) · (batchLinearConstraintsSecondPart p).decide · enterOwn.
USER     rowZero (through rowZeroLeft_atWords).
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
LETTERS  p · arr, t₁, t₂ (the file's map from a seat to a message's number; the numbers of the
         first and of the shared chain's trees) · fs : what was handed → the first chain's last
         record.

  oOf d · sharedOfEnd_ended   what the last chain's start is handed of d, as a total reader.
  w₁Of · OkW · omWW · wvW     the family.
  Started p fs a       the record in front is the start's of what was handed.
  started_inv · start_w       what that gives.
  reads_atWords        **reads**: Reads ITSELF at the family, at every handed part: by
                       readsOn_wordsLast (ReadsAt.lean): CALLED (reads_wordsLast, declared nowhere
                       in this library, stood at a copy of Reads).
  fence_atWords        **fence**: by atStart_of_yes (ReadsAt.lean): CALLED.
  atDot_atWords        **atDot**'s first half: by atDot_of_start_yes.
  dot_atWords          **dot**: DotOmAt at rg d := wordsShared arr t₁ d.st d.book.
  rows_atWords         **rows**: the body of rowsOpen, at enterOwn and the seat by
                       the record's own book, gives RowsHold of wordsLast, where its letter cs is
                       the record's own table of codes.
  RowZeroAtWords       WHAT IS LEFT THEN: the make (3) · what rides (5) · started · weights ·
                       names · placed · tenant (five public conditions inside the promise at border
                       0) · shape · rows · ev · dot (DotOmAt at that reading gives Mg.dot: at
                       Mg.dot := dotI … it is the identity).
  rowZeroLeft_atWords  **it gives RowZeroLeft.**   rowZero_atWords: so both conjuncts of EachOwn.
What is not claimed. NO MEMBER. The five public conditions are shown of no record. That arr, t₁, t₂
are the file's own is said nowhere. K14's law on the shared chain has its reader of words as ONE
letter in front of all records: that its DotOmAt is had at rg d for the chain's LAST record d is
owed there. No soundness of a verifier; nothing on hiding.

-/
import Johnson.Desc.Sound.ReadsAt
import Johnson.Desc.Third.Law.Row0DotOm
import Johnson.Desc.Third.Law.AtDotYes
import Johnson.Desc.Third.Law.Row0Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Means (Words)
open OnBytes.Maker OnBytes.Flat Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (DotOmAt omegaOf DotEq)
open _root_.Run.PQ (CK)

/-- What the last chain's start is handed of K14's own last record. -/
def oOf (d : St) : SharedOut :=
  { st := d.st, book := d.book, psi := d.loc.psiSh, omega := d.loc.oOmega }

theorem sharedOfEnd_ended (d : St) (e : Proof.SharedEnd) (h : _root_.Desc.K14.ended d = some e) :
    sharedOfEnd e = oOf d := by
  unfold _root_.Desc.K14.ended at h
  dsimp only at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

/-- W's number, as the first chain's last record names it. -/
def w₁Of (s : First.S) : ℕ := ((firstOfS s).map (·.w)).getD 0

/-- W's number in the record that the start returns is the number that it was handed. -/
theorem start_w (codes : Codes) (S : LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) : s₀.loc.w = w₁ := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, hw, _⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨_, _, e0⟩ := start₃_inv _ _ _ _ hst
  subst e0
  exact hw

section
variable {P S₁ Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (p : P₁₄) (fs : P × S₁ → First.S)

/-- The fence, at what was handed. -/
def OkW (u : P × S₁ × St) : S₃ → S₃ → Prop :=
  AtStart (fs (u.1, u.2.1)).st (fs (u.1, u.2.1)).book (w₁Of (fs (u.1, u.2.1))) (oOf u.2.2)

/-- Omega's reader, at what was handed. -/
def omWW (u : P × S₁ × St) : Wit Cells Tok MsgT → ℕ → GE :=
  omegaWords arr t₁ p (fs (u.1, u.2.1)).st.codes (oOf u.2.2)

/-- W's reader, at the first chain's last record. -/
def wvW (q : P × S₁) : Wit Cells Tok MsgT → ℕ → GE :=
  wWords arr p (fs q).st (fs q).book (w₁Of (fs q))

/-- **reads**: Reads itself, at every handed part. -/
theorem reads_atWords (u : P × S₁ × St) :
    Reads p (OkW fs u) (wordsLast (Cells := Cells) (Tok := Tok) arr t₁ t₂) (omWW arr t₁ p fs u)
      (wvW arr p fs (u.1, u.2.1)) where
  older := fun s s' w hA h n hn part i =>
    (readsOn_wordsLast arr t₁ t₂ p _ _ _ _).older s s' w h hA n hn part i
  omega := fun s s' w hA h y _ => (readsOn_wordsLast arr t₁ t₂ p _ _ _ _).omega s s' w y h hA
  w := fun s s' w hA h c _ => (readsOn_wordsLast arr t₁ t₂ p _ _ _ _).w s s' w c h hA

/-- **The record in front is the start's of what was handed.** -/
def Started {Y : Type} (a : ((P × S₁ × St) × S₃) × Y) : Prop :=
  ∃ e, _root_.Desc.K14.ended a.1.1.2.2 = some e ∧
    startAtEnds p a.1.1.1 (fs (a.1.1.1, a.1.1.2.1)) e = .ok a.1.2

variable {arr t₁ t₂ p fs}

/-- What that gives: the start's own yes, at the first record's own parts and at oOf. -/
theorem started_inv {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a) :
    ∃ f : FirstEnd₃, f.st = (fs (a.1.1.1, a.1.1.2.1)).st ∧ f.book = (fs (a.1.1.1, a.1.1.2.1)).book ∧
      f.pending = (fs (a.1.1.1, a.1.1.2.1)).rows ∧ f.w = w₁Of (fs (a.1.1.1, a.1.1.2.1)) ∧
      start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (oOf a.1.1.2.2) =
        .ok a.1.2 := by
  obtain ⟨e, he, hs⟩ := h
  unfold startAtEnds start₃F at hs
  cases hf : firstOfS (fs (a.1.1.1, a.1.1.2.1)) with
  | none => rw [hf] at hs; cases hs
  | some f =>
    rw [hf] at hs
    have hs' : start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (sharedOfEnd e) =
        .ok a.1.2 := hs
    rw [sharedOfEnd_ended _ e he] at hs'
    have hw : f.w = w₁Of (fs (a.1.1.1, a.1.1.2.1)) := by
      unfold w₁Of
      rw [hf]
      rfl
    have hp : f.st = (fs (a.1.1.1, a.1.1.2.1)).st ∧ f.book = (fs (a.1.1.1, a.1.1.2.1)).book ∧
        f.pending = (fs (a.1.1.1, a.1.1.2.1)).rows := by
      unfold firstOfS at hf
      cases hx : (fs (a.1.1.1, a.1.1.2.1)).firstEnd? with
      | none => rw [hx] at hf; cases hf
      | some x => rw [hx] at hf; cases hf; exact ⟨rfl, rfl, rfl⟩
    exact ⟨f, hp.1, hp.2.1, hp.2.2, hw, hs'⟩

/-- **fence.** -/
theorem fence_atWords {Y Cl₀ : Type} {a : ((P × S₁ × St) × S₃) × Y} {s' : S₃}
    (h : Started p fs a)
    (hy : ∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s')
    (placed : ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size)
    (tenant : ∀ q : ℕ × ℕ, a.1.1.2.2.book.place[a.1.1.2.2.loc.oOmega]? = some q → q.2 = 0) :
    OkW fs a.1.1 a.1.2 s' := by
  obtain ⟨f, e1, e2, _, e4, hs⟩ := started_inv h
  obtain ⟨rs, gs, hd⟩ := hy
  have hA := atStart_of_yes p p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending
    (oOf a.1.1.2.2) a.1.2 s' hs rs gs hd (by rw [e2]; exact placed) tenant
  rw [start_w _ _ _ _ _ _ _ _ _ _ _ hs, e1, e2, e4] at hA
  exact hA

/-- **atDot**'s first half. -/
theorem atDot_atWords {Y Cl₀ : Type} {a : ((P × S₁ × St) × S₃) × Y} {s' : S₃}
    (h : Started p fs a)
    (hy : ∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s')
    (weights : ∀ r ∈ (fs (a.1.1.1, a.1.1.2.1)).rows, ∀ g ∈ r.g, g.ok = true) : AtDot p a.1.2 := by
  obtain ⟨f, _, _, e3, _, hs⟩ := started_inv h
  obtain ⟨rs, gs, hd⟩ := hy
  exact atDot_of_start_yes p _ _ _ _ _ _ _ _ _ s' hs rs gs hd fun r hr g hg =>
    weights r (by rw [← e3, hr]; exact List.mem_singleton.2 rfl) g hg

/-- BorderIs, and one table of codes. -/
theorem border_atWords {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a) :
    BorderIs (gOfS (fs (a.1.1.1, a.1.1.2.1))) a.1.1.2.2 a.1.2 ∧
      a.1.1.2.2.st.codes = (fs (a.1.1.1, a.1.1.2.1)).st.codes := by
  obtain ⟨f, e1, _, _, _, hs⟩ := started_inv h
  obtain ⟨e, he, hs0⟩ := h
  obtain ⟨h1, _, _, _, h5, _⟩ := startIs _ _ _ _ _ _ _ _ _ _ _ hs
  refine ⟨borderIs_at_seat p _ _ _ e _ he hs0, ?_⟩
  have : (oOf a.1.1.2.2).st.codes = a.1.2.st.codes := h5
  rw [h1, e1] at this
  exact this

/-- **dot**: the semantic (Dot) at the family is DotOmAt at the shared record's own reading. -/
theorem dot_atWords {Y : Type} {a : ((P × S₁ × St) × S₃) × Y} (h : Started p fs a)
    (w : Wit Cells Tok MsgT)
    (hd : DotSem OnBytes.Model.Reading.gl p (omWW arr t₁ p fs a.1.1)
      (wvW arr p fs (a.1.1.1, a.1.1.2.1)) a.1.2 w) :
    DotOmAt p.S (gOfS (fs (a.1.1.1, a.1.1.2.1))) a.1.1.2.2
      (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr p fs (a.1.1.1, a.1.1.2.1) w) := by
  obtain ⟨hB, hc⟩ := border_atWords h
  refine dotOmAt_of_dotSem p _ _ a.1.2
    (fun w => wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) _ w hB ?_
  have e : omWW (Cells := Cells) (Tok := Tok) arr t₁ p fs a.1.1 =
      omOf p.S a.1.1.2.2 (fun w => wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) := by
    unfold omWW omOf omegaWords omegaOf
    rw [← hc]
    rfl
  rw [← e]
  exact hd

/-- **rows**: "rows", as the own test's row closes it (the body of rowsOpen cs arr enterOwn seatOwn,
Johnson/Flat/Last/LastAtArm.lean [not in this library], at seatOwn s := the seat by the
record's own book), gives RowsHold
of wordsLast: where cs is the record's own table of codes. -/
theorem rows_atWords {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (cs : Codes) (s : S₃)
    (w : Wit Cells Tok MsgT) (hcs : s.st.codes = cs)
    (h : ∃ t, VerifiableInference.Desc.K12.Seat.enterOwn s = .ok t ∧
      ∀ i, OnBytes.Means.OpenSays OnBytes.Model.Reading.gl t.st t.g i
        (OnBytes.Means.wordsOn t.st
          (tabAt cs arr (seatBy (noLast t₁ t₂ s.loc.firstTree) s.book) t.st w))) :
    RowsHold OnBytes.Model.Reading.gl s (wordsLast arr t₁ t₂ s w) := by
  subst hcs
  exact rowsHold_of_enterOwn OnBytes.Model.Reading.gl s
    (fun t => OnBytes.Means.wordsOn t.st
      (tabAt s.st.codes arr (seatBy (noLast t₁ t₂ s.loc.firstTree) s.book) t.st w)) h

end

section
variable {P S₁ Cells Tok Cl : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS St (P × S₁) (Wit Cells Tok MsgT)) (ML : MeaningL S₃ (Wit Cells Tok MsgT))
  (Pm : PromMeaning St) (PL : PromMeaningL St S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)

/-- **WHAT IS LEFT AT ROW 0, AT THE CLOSED FAMILY.** -/
structure RowZeroAtWords (Cl₀ : Type) (p : P₁₄)
    (x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)) (lo : ℕ) (arr : ℕ → ℕ → ℕ)
    (t₁ t₂ : ℕ) (fs : P × S₁ → First.S) : Prop where
  wrap : YesOf (fun t : (P × S₁ × St) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) x.b
  hand : ∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1
  idle : ∀ a τ w, x.ext a τ w = w
  ocBelow : OcReadsBelow lo Oc
  lo_le : lo ≤ x.base
  tree : ReadsTree Mg Pm
  omegaBelow : (N.tenant .oOmega).1 < x.base
  pins : PinsReadBelow (S₃ := S₃) N Mg ML x.base
  /-- inside the promise at border 0 the record is the start's of what was handed -/
  started : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a → Started p fs a
  /-- the pending rows' weights are well-formed -/
  weights : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ r ∈ (fs (a.1.1.1, a.1.1.2.1)).rows, ∀ g ∈ r.g, g.ok = true
  /-- the own group's open rows name messages of the statement alone -/
  names : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a → Names a.1.2
  /-- every place of the first chain's last book names a tree that is there -/
  placed : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size
  /-- in the shared chain's book Omega is part 0 of its tree -/
  tenant : ∀ a : ((P × S₁ × St) × S₃) × Fr.E.Str, onQ₃ N Mg Pm PL Oc 0 a →
    ∀ q : ℕ × ℕ, a.1.1.2.2.book.place[a.1.1.2.2.loc.oOmega]? = some q → q.2 = 0
  shape : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) (s' : S₃), onQ₃ N Mg Pm PL Oc 0 a →
    (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') → Says p a.1.2 s' →
    PL.shape 1 (a.1.1.1, a.1.1.2.1) a.1.1.2.2 s' = true
  rows : ∀ (b : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 1 b → ML.rows b.1.2 w →
    RowsHold OnBytes.Model.Reading.gl b.1.2 (wordsLast arr t₁ t₂ b.1.2 w)
  ev : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    RowsHold OnBytes.Model.Reading.gl a.1.2 (wordsLast arr t₁ t₂ a.1.2 w) →
    Mg.ev (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w
  /-- K14's law's DotOmAt, at the shared record's own reading of the words, gives the table's
  (Dot) -/
  dot : ∀ (a : ((P × S₁ × St) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    DotOmAt p.S (gOfS (fs (a.1.1.1, a.1.1.2.1))) a.1.1.2.2
      (wordsShared arr t₁ a.1.1.2.2.st a.1.1.2.2.book w) (wvW arr p fs (a.1.1.1, a.1.1.2.1) w) →
    Mg.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w

variable {N Mg ML Pm PL Oc}

/-- **It gives what is left at row 0, at the family.** -/
theorem rowZeroLeft_atWords {Cl₀ : Type} {p : P₁₄}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroAtWords N Mg ML Pm PL Oc Cl₀ p x lo arr t₁ t₂ fs) :
    RowZeroLeft OnBytes.Model.Reading.gl N Mg ML Pm PL Oc Cl₀ p x lo (OkW fs)
      (fun _ => wordsLast arr t₁ t₂) (omWW arr t₁ p fs) (fun u => wvW arr p fs (u.1, u.2.1)) where
  wrap := h.wrap
  hand := h.hand
  idle := h.idle
  ocBelow := h.ocBelow
  lo_le := h.lo_le
  tree := h.tree
  omegaBelow := h.omegaBelow
  pins := h.pins
  atDot := fun a _ ha hy => ⟨atDot_atWords (h.started a ha) hy (h.weights a ha), h.names a ha⟩
  fence := fun a _ ha hy _ => fence_atWords (h.started a ha) hy (h.placed a ha) (h.tenant a ha)
  shape := h.shape
  reads := fun u => reads_atWords arr t₁ t₂ p fs u
  rows := h.rows
  ev := h.ev
  dot := fun a w ha hd => h.dot a w ha (dot_atWords (h.started a ha) w hd)

/-- So both conjuncts of EachOwn at row 0. -/
theorem rowZero_atWords {Cl₀ : Type} {p : P₁₄}
    {x : Piece C Fr ((P × S₁ × St) × S₃) Cl (Wit Cells Tok MsgT)} {lo : ℕ} {arr : ℕ → ℕ → ℕ}
    {t₁ t₂ : ℕ} {fs : P × S₁ → First.S}
    (h : RowZeroAtWords N Mg ML Pm PL Oc Cl₀ p x lo arr t₁ t₂ fs) :
    x.Own (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (insQ₃ 0) (outsQ₃ 0) ∧
      x.Frames (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0) :=
  rowZero (rowZeroLeft_atWords h)

end

end VerifiableInference.Desc.Third.Law
