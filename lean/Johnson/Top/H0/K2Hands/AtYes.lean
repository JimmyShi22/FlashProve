-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/AtYes.lean: the code switch: EIGHT CLAUSES OF THE RECORD AtSwitch
(Paid.lean) FOLLOW FROM WHAT A YES OF THE KIND's OWN TEXT GIVES, at the sending that the kind runs
(sendByL8), under two premises beside the yes: KeptPos and logN ≤ 32.

Paid.lean's AtSwitch gathers what the last join (HandsOn.lean) asks of the program's frame and test.
yes_switch says what a yes of decideWith sendByL8 gives; atSwitch_of builds the record out of that,
RowsAt.lean's Laid (which laid_of gives from the maker's yes, and which holds the clause frame) and
the eight clauses that stay premises.
  yes_switch    A YES OF decide: the front x, what the sending returned (y), the statement S3 in
                which the rows are made, the one array Y and the rows, with: the target's test says
                yes at x.st (the text's guard G0, by TargetAgree.lean's targetOk_eq); SentOk x.st
                (the notices) y.ids y.st (SentKeeps.lean); SameTables y.st S3 (BehindSame.lean); the
                old main code stands in y.st with logN = the place's logN; switchRows S3 … Y = some
                rows
  switch_parts, YesSwitch  what a yes of the switch at a front is made of; yes_switch's statement as
                a closed proposition
  notices_size, notices_zero, notices_kept  the announcements of a switch's sending
  ids_at        the number of announcement i is (the number of messages in front) + i
  frame_g       the frame's g is the number that it was handed
  frame_code, plan_32  the frame's old main code is that code; the kind's planOk asks logN ≤ 32.
                atSwitch_of takes «logN ≤ 32» as a PREMISE: no theorem of this folder calls plan_32
  KeptOld       every kept member of the carried rows is a message of the statement in front of the
                sending
  KeptPos       A PREMISE, on the target alone, which is public: each message that takes a kept
                member has a main row
  below_of_rows, keptOld_of  KeptOld follows from the target's test's yes and KeptPos
  check_at_S3   the target's test says yes at S3 too (check_congr, Johnson/Top/H/SwitchPads.lean):
                THE SEAM that Paid.lean's head names is closed under KeptPos
  g_at_S3, copy_at_S3  g and the kept members' new copies stand in S3 with the target's shapes
  shape_old     an old message has in S3 the shape that it had in front of the sending
  six_paid      check and gRec at S3; the frame's g is n0, the number of messages in front of the
                sending; kept member a's new message is n0 + (1 + a)
  atSwitch_of   THE RECORD AtSwitch at ids := fun i => n0 + i: frame (from Laid), check, gRec, c32
                (from the premise logN ≤ 32, by frame_code), rowsPos, gIs, anewIs, notG are made;
                the eight other clauses are handed in
LIMITS. KeptPos is a premise: no test of the text that I have read asks it. logN ≤ 32 is a premise.
The other eight clauses of AtSwitch stay premises. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.Paid
import Johnson.Top.H0.K2Hears.SentKeeps
import Johnson.Top.H0.Tw.K2.TargetAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchE switchBehind switchNotices sendByL8 switchGuard)

theorem switch_parts {p : P2} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView}
    {cols w roots} (h : switchE switchBehind (par9 p) sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) :
    ∃ (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E) (rows : List OnBytes.Row),
      switchTargetCheck x.st x.f.rows x.T = true ∧
      SentOk x.st (switchNotices x.T x.others) y.ids y.st ∧ SameTables y.st S3 ∧
      (∃ c, y.st.codes.base[x.f.rows.code]? = some c ∧ c.logN = p.logN) ∧
      switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
        (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows := by
  obtain ⟨y, hs⟩ := switchE_inv h
  obtain ⟨y', S3, Y, rows, R, hS⟩ := rows_of_switch_same h
  have e : y' = y := by
    have a := R.sent
    rw [hs.hSend] at a
    exact (Except.ok.inj a).symm
  subst e
  refine ⟨y', S3, Y, rows, ?_, sent_ok hs.hSend, hS, R.code, R.made⟩
  rw [← _root_.Tw.K2.targetOk_eq]
  exact hs.hGuard

/-- **A yes of decide, at the sending that the kind runs.** -/
def YesSwitch : Prop := ∀ p s r₁ r₂ gs s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row),
    frontAt p s = some x ∧ switchTargetCheck x.st x.f.rows x.T = true ∧
    SentOk x.st (switchNotices x.T x.others) y.ids y.st ∧ SameTables y.st S3 ∧
    (∃ c, y.st.codes.base[x.f.rows.code]? = some c ∧ c.logN = p.logN) ∧
    switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows

theorem yes_switch : YesSwitch := fun p s r₁ r₂ gs s' h => by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨a, b, x, w, roots, S', f, mine, e, hl⟩ := link_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, h1, h2, h3, h4, h5⟩ := switch_parts hl.hSwitch
    exact ⟨x, y, S3, Y, rows, by simp [frontAt, hp, hl.hFront, Except.toOption], h1, h2, h3, h4, h5⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := head_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, h1, h2, h3, h4, h5⟩ := switch_parts hl.hSwitch
    exact ⟨_, y, S3, Y, rows, by simp [frontAt, hp, hl.hHere, hl.hGroup], h1, h2, h3, h4, h5⟩
  · obtain ⟨a, b, o, G, w, roots, e, hl⟩ := finish_inv hp h
    cases e
    obtain ⟨y, S3, Y, rows, h1, h2, h3, h4, h5⟩ := switch_parts hl.hSwitch
    exact ⟨_, y, S3, Y, rows, by simp [frontAt, hp, hl.hHere, hl.hLaid], h1, h2, h3, h4, h5⟩

/-! ## The announcements and their numbers -/

theorem notices_size (T : SwitchTarget) (others : Array OracleNotice) :
    (switchNotices T others).size = 1 + T.kept.size + others.size := by
  simp [switchNotices]
  omega

theorem notices_zero (T : SwitchTarget) (others : Array OracleNotice) :
    ((switchNotices T others)[0]?).map (·.shape) = some T.shape := by
  simp [switchNotices]

theorem notices_kept (T : SwitchTarget) (others : Array OracleNotice) (a : Nat)
    (h : a < T.kept.size) :
    ((switchNotices T others)[1 + a]?).map (·.shape) = some T.kept[a].shape := by
  have h1 : 1 + a < (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++
      T.kept.map (fun k => (⟨k.shape, k.leafClass⟩ : OracleNotice))).size := by
    simp
    omega
  unfold switchNotices
  rw [Array.getElem?_append_left h1, Array.getElem?_append_right (by simp)]
  simp [h]

theorem ids_at {S S' : Statement} {notices : Array OracleNotice} {ids : Array Nat}
    (h : SentOk S notices ids S') (i : Nat) (hi : i < notices.size) :
    ids.getD i noId = S.oracles.size + i := by
  rw [h.ids]
  simp [Array.getD, hi]
  omega

theorem frame_g (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (W : SwitchFrame) (h : switchFrame S old T g anew = some W) : W.g = g := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, -, -, -, rfl⟩ := h
  rfl

/-- The frame's old main code is the code that the statement behind the sending has at the carried
rows' number. -/
theorem frame_code {S2 S3 : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {W : SwitchFrame} {c : Code} (hj : SameTables S2 S3)
    (hW : switchFrame S3 old T g anew = some W) (hc : S2.codes.base[old.code]? = some c) :
    W.code = c := by
  have h := (Johnson.Top.H.frame_fields _ _ _ _ _ _ hW).1
  rw [hj.codes, hc] at h
  exact (Option.some.inj h).symm

/-- The kind's test on the plan asks logN ≤ 32. -/
theorem plan_32 {Cl : Type} {p : P2} (h : (codeSwitchKind (Cl := Cl) p).planOk = true) : p.logN ≤ 32 := by
  have h' : (Decidable.decide (0 < p.positions) && p.sent.length == p.roots &&
      increasing (p.read.map (·.1)) && Decidable.decide (p.logN ≤ 32)) = true := h
  rw [Bool.and_eq_true] at h'
  exact of_decide_eq_true h'.2

/-- Every kept member of the carried rows is a message of the statement S. -/
def KeptOld (S : Statement) (old : SingleRows) : Prop :=
  ∀ o, o ∈ (switchKept old).toList → o < S.oracles.size

/-- A number at which the statement's message, or the blank one, has a main row names a message. -/
theorem below_of_rows (S : Statement) (n : Nat)
    (h : 0 < (S.oracles.getD n default).shape.mainRows) : n < S.oracles.size := by
  by_cases hn : n < S.oracles.size
  · exact hn
  · have e : S.oracles.getD n default = default := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [e] at h
    exact absurd h (by decide)

/-- Each message that takes a kept member has a main row: a clause on the target, which is public.
-/
def KeptPos (T : SwitchTarget) : Prop := ∀ i (h : i < T.kept.size), 0 < T.kept[i].shape.mainRows

/-- **KeptOld follows from the target's test's yes and KeptPos.** The test alone does not give it:
the blank
message's shape has no main row, no answer, and a pad that can be made. -/
theorem keptOld_of {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (hc : switchTargetCheck S old T = true) (hp : KeptPos T) : KeptOld S old := by
  intro o ho
  have hf := Johnson.Top.H.check_facts hc
  have hsz : T.kept.size = (switchKept old).size := hf.2.2.2.2.2.2.1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have hi' : i < (switchKept old).size := by simpa using hi
  have h2 : i < T.kept.size := by omega
  have e := (hf.2.2.2.2.2.2.2 i hi' h2).1
  refine below_of_rows S _ ?_
  have hpos := hp i h2
  rw [e] at hpos
  simpa using hpos

section
variable {S0 S2 S3 : Statement} {old : SingleRows} {T : SwitchTarget} {others : Array OracleNotice}
  {ids : Array Nat} (hs : SentOk S0 (switchNotices T others) ids S2) (hj : SameTables S2 S3)
include hs hj

theorem shape_old (o : Nat) (ho : o < S0.oracles.size) :
    (S3.oracles.getD o default).shape = (S0.oracles.getD o default).shape := by
  have a := (hj.shape o).trans (congrArg (Option.map (·.shape)) (hs.old o ho))
  have h3 : o < S3.oracles.size := by
    rw [hj.size, hs.size]
    omega
  simpa [Array.getD, ho, h3] using a

/-- **The target's test says yes at S3 too.** -/
theorem check_at_S3 (hk : KeptOld S0 old) (hc : switchTargetCheck S0 old T = true) :
    switchTargetCheck S3 old T = true :=
  (Johnson.Top.H.check_congr S0 S3 old (hj.codes.trans hs.codes)
    (fun o ho => shape_old hs hj o (hk o ho)) T).trans hc

theorem g_at_S3 : ∃ x, S3.oracles[S0.oracles.size]? = some x ∧ x.shape = T.shape := by
  have a := (hj.shape (S0.oracles.size + 0)).trans ((hs.shape 0).trans (notices_zero T others))
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 a
  exact ⟨x, hx, e⟩

theorem copy_at_S3 (a : Nat) (h : a < T.kept.size) :
    ∃ x, S3.oracles[S0.oracles.size + (1 + a)]? = some x ∧ x.shape = T.kept[a].shape := by
  have b := (hj.shape (S0.oracles.size + (1 + a))).trans
    ((hs.shape (1 + a)).trans (notices_kept T others a h))
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 b
  exact ⟨x, hx, e⟩

end

/-- **Four facts, out of which atSwitch_of makes clauses of AtSwitch.** n0: the number of
messages in front of the sending. -/
theorem six_paid {S0 S2 S3 : Statement} {old : SingleRows} {T : SwitchTarget}
    {others : Array OracleNotice} {ids : Array Nat} {W : SwitchFrame}
    (hs : SentOk S0 (switchNotices T others) ids S2) (hj : SameTables S2 S3)
    (hk : KeptOld S0 old) (hc : switchTargetCheck S0 old T = true)
    (hW : switchFrame S3 old T (ids.getD 0 noId) (ids.extract 1 (1 + T.kept.size)) = some W) :
    switchTargetCheck S3 old T = true ∧
      (∃ x, S3.oracles[ids.getD 0 noId]? = some x ∧ x.shape = T.shape) ∧
      W.g = S0.oracles.size ∧
      ∀ (a : Nat) (k : KeptPlace), W.kept[a]? = some k → k.anew = S0.oracles.size + (1 + a) := by
  have hN := notices_size T others
  have h0 : ids.getD 0 noId = S0.oracles.size := by
    rw [ids_at hs 0 (by omega)]
    rfl
  have hc3 := check_at_S3 hs hj hk hc
  refine ⟨hc3, by rw [h0]; exact g_at_S3 hs hj, (frame_g _ _ _ _ _ _ hW).trans h0, fun a k ha => ?_⟩
  have hf := (Johnson.Top.H.frame_fields _ _ _ _ _ _ hW).2.2.2.2.2.2.2
  rw [hf] at ha
  obtain ⟨hlt, rfl⟩ := Johnson.Top.H.range_map_at _ _ _ _ ha
  have hsz : T.kept.size = (switchKept old).size := (Johnson.Top.H.check_facts hc3).2.2.2.2.2.2.1
  show (ids.extract 1 (1 + T.kept.size)).getD a noId = _
  have hsize : ids.size = 1 + T.kept.size + others.size := by
    rw [hs.ids]
    simp [hN]
  have e : (ids.extract 1 (1 + T.kept.size)).getD a noId = ids.getD (1 + a) noId := by
    simp [Array.getD, Array.size_extract]
    split <;> split <;> first | rfl | omega
  rw [e, ids_at hs (1 + a) (by omega)]

open VerifiableInference.Desc.First.K2Hands Johnson.Pack Johnson.Top.H OnBytes.Slice in
/-- **The record AtSwitch, out of what a yes gives.** -/
theorem atSwitch_of {S0 S2 S3 : Statement} {old : SingleRows} {T : SwitchTarget}
    {others : Array OracleNotice} {ids : Array Nat} {W : SwitchFrame} {pos : Positions}
    {Y : Array E} {rows : List OnBytes.Row} {carried : OnBytes.Row}
    (hs : SentOk S0 (switchNotices T others) ids S2) (hj : SameTables S2 S3)
    (hp : KeptPos T) (hc : switchTargetCheck S0 old T = true)
    (L : Laid S3 old T (ids.getD 0 noId) (ids.extract 1 (1 + T.kept.size)) pos Y rows W carried)
    (l : List (OracleShape × Nat)) (s : Sg) (K : Type) [Fintype K] [DecidableEq K]
    (mem row : K → Nat) (pl : K → KeptPlace)
    {c : Code} (hcode : S2.codes.base[old.code]? = some c) (c32 : c.logN ≤ 32)
    (z32 : W.zk.logN ≤ 32)
    (keptRows : old.keptRows = (W.kept.map (·.rows)).sum)
    (ell : ∀ (a : Nat) (k : KeptPlace), W.kept[a]? = some k →
      (S3.codes.base.getD (S3.oracles.getD k.old default).shape.code default).ell = W.code.ell)
    (first : ∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = T.shape)
    (next : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape)
    (codeC : s.C = codeOf W.code) (codeZ : s.Z = codeOf W.zk)
    (slots : SlotsAll K W mem row pl) :
    AtSwitch S3 old T (ids.getD 0 noId) (ids.extract 1 (1 + T.kept.size)) W l s K mem row pl
      (fun i => S0.oracles.size + i) := by
  obtain ⟨h1, h2, h3, h4⟩ := six_paid hs hj (keptOld_of hc hp) hc L.frame
  exact {
    frame := L.frame, check := h1, gRec := h2,
    c32 := by rw [frame_code hj L.frame hcode]; exact c32
    z32 := z32, keptRows := keptRows,
    rowsPos := fun a k ha => by
      obtain ⟨hi, -, hr, -⟩ := kept_rec S3 old T _ _ W L.frame a k ha
      have hf := Johnson.Top.H.check_facts h1
      have h2' : a < T.kept.size := by rw [hf.2.2.2.2.2.2.1]; exact hi
      rw [hr, ← (hf.2.2.2.2.2.2.2 a hi h2').1]
      exact hp a h2'
    ell := ell, first := first, next := next, codeC := codeC, codeZ := codeZ,
    slots := slots
    gIs := fun n => by
      rw [h3]
      constructor <;> intro e <;> omega
    anewIs := fun a k ha n => by
      rw [h4 a k ha]
      constructor <;> intro e <;> omega
    notG := fun a k ha => by
      rw [h4 a k ha, h3]
      omega }

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keptOld_of
#print axioms VerifiableInference.Desc.First.K2.atSwitch_of
#print axioms VerifiableInference.Desc.First.K2.six_paid
#print axioms VerifiableInference.Desc.First.K2.yes_switch
#print axioms VerifiableInference.Desc.First.K2.check_at_S3
#print axioms VerifiableInference.Desc.First.K2.g_at_S3
#print axioms VerifiableInference.Desc.First.K2.copy_at_S3
