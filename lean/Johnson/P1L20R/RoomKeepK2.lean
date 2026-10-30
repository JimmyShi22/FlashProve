-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomKeepK2.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach, PAID: THE FIELD k2 OF
KeepShares (RoomKeep.lean): every sub-protocol of the kind K2 (code switching) that its lot
makes, in each of its three dresses (at a link; at the head's link, with the quiet step that opens
the link joined behind; at the finish, between its two quiet steps), hands both clauses on.

Why it holds. An accepting code switch writes the statement by six calls: it pushes an empty group;
it sends fresh oracle messages, whose numbers begin at the statement's old size; it closes the
ledger of the first of these; it joins fresh numbers alone to the new group; it adds open rows.
An older message that is a member of no group keeps its ledger and stays out of every group.

  NoMem o T         the message number o is a member of no group of the statement T
  Off o T T'        from T to T': the ledger at number o is as it was, and NoMem o is handed on
  off_join, off_joins, off_close, off_rows, off_fresh, off_sent   the six calls, each at a number
                    other than o (the sending: at o below the old size)
  switch_off        an accepting switch: Off o at every o below the old size; the numbers that it
                    hands on as "others" are at or above the old size
  behind_off        the link's own messages' joins behind the switch
  link_off, head_off, finish_off   the three dresses, whole
  k2_keeps          THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent

Called: the closed forms of the kind's accepts (link_inv, head_inv, finish_inv, switchE_inv,
switchBehind_inv: Johnson/Top/H0/Tw/K2C/Closed.lean; firstBehind_iff, headOpenQ_iff: Asks.lean),
sent_ok (Johnson/Top/H0/K2Hears/SentKeeps.lean), firstFront_st, finishFrontQ_st, "what was put out
is left" (Johnson/Top/H0/Tw/K2C/LeavesOut.lean), and what a member of K2's lot is (lot_K2, k2_mem:
Johnson/IMR/K2Seat.lean).

Limits. One field of thirteen. A frame law: it says what these texts do not write. No soundness
statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.K2Seat
import Johnson.Top.H0.Tw.K2C.LeavesOut
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Top.H0.K2Hears.SentKeeps
import Johnson.Top.H0.K2Hears.RowsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open _root_.Tw.K2 (SwOut switchE switchBehind sendByL8 switchNotices closeLedgerG joinG addRowsG
  firstBehind)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- The message number o is a member of no group. -/
def NoMem (o : ℕ) (T : Statement) : Prop := ∀ (i : ℕ) G, T.groups[i]? = some G → o ∉ G.members

/-- The ledger at number o is as it was, and "a member of no group" is handed on. -/
def Off (o : ℕ) (T T' : Statement) : Prop :=
  (T'.oracles[o]?).bind (·.ledger) = (T.oracles[o]?).bind (·.ledger) ∧ (NoMem o T → NoMem o T')

theorem Off.refl (o : ℕ) (T : Statement) : Off o T T := ⟨rfl, id⟩

theorem Off.trans {o : ℕ} {A B C : Statement} (h : Off o A B) (k : Off o B C) : Off o A C :=
  ⟨k.1.trans h.1, fun x => k.2 (h.2 x)⟩

theorem off_same {o : ℕ} {T T' : Statement} (h1 : T'.oracles[o]? = T.oracles[o]?)
    (h2 : T'.groups = T.groups) : Off o T T' :=
  ⟨by rw [h1], fun h i G hG => h i G (by rw [← h2]; exact hG)⟩

theorem off_join {o g p : ℕ} {kept : Bool} {T T' : Statement} (h : joinG T g p kept = .ok T')
    (hp : p ≠ o) : Off o T T' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.joinP at hd
    split at hd
    · obtain ⟨G₀, hG₀, rfl⟩ := Option.map_eq_some_iff.1 hd
      refine ⟨?_, fun hN i G hG hm => ?_⟩
      · show ((OnBytes.Slice.withMessageInGroup T g p kept G₀).oracles[o]?).bind _ = _
        unfold OnBytes.Slice.withMessageInGroup
        simp only [Array.getElem?_modify]
        rw [if_neg hp]
      · have hG' : (OnBytes.Slice.withMessageInGroup T g p kept G₀).groups[i]? = some G := hG
        unfold OnBytes.Slice.withMessageInGroup at hG'
        simp only [Array.getElem?_modify] at hG'
        split at hG'
        · obtain ⟨G₁, hG₁, rfl⟩ := Option.map_eq_some_iff.1 hG'
          have hm' : o ∈ G₁.members.insertIdxIfInBounds (G₀.members.filter (· < p)).size p := hm
          unfold Array.insertIdxIfInBounds at hm'
          split at hm'
          · rcases Array.mem_insertIdx.1 hm' with e | e
            · exact hp e.symm
            · exact hN i G₁ hG₁ e
          · exact hN i G₁ hG₁ hm'
        · exact hN i G hG' hm
    · cases hd
  · cases h

theorem off_joins {α : Type} (o g : ℕ) (f : α → ℕ) (k : α → Bool) : ∀ (l : List α)
    (T T' : Statement), l.foldlM (fun T p => joinG T g (f p) (k p)) T = .ok T' →
    (∀ p ∈ l, f p ≠ o) → Off o T T'
  | [], T, T', h, _ => by
    cases h
    exact Off.refl o T
  | p :: l, T, T', h, hp => by
    rw [List.foldlM_cons] at h
    obtain ⟨T1, h1, h2⟩ := bindOk h
    exact (off_join h1 (hp p (by simp))).trans
      (off_joins o g f k l T1 T' h2 fun q hq => hp q (by simp [hq]))

theorem off_close {o p : ℕ} {T T' : Statement} (h : closeLedgerG T p = .ok T') (hp : p ≠ o) :
    Off o T T' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at hd
    split at hd
    · cases hd
      refine ⟨?_, fun hN => hN⟩
      show ((OnBytes.Slice.closeLedgers T [p]).oracles[o]?).bind _ = _
      simp only [OnBytes.Slice.closeLedgers, List.foldl_cons, List.foldl_nil,
        Array.getElem?_modify]
      rw [if_neg hp]
    · cases hd
  · cases h

theorem withRow_off (o g : ℕ) (r : OnBytes.Row) (T : Statement) :
    Off o T (OnBytes.Slice.withRow T g r) := by
  refine ⟨rfl, fun hN i G hG hm => ?_⟩
  have hG' : (T.groups.modify g fun G => { G with rows := G.rows.push r })[i]? = some G := hG
  simp only [Array.getElem?_modify] at hG'
  split at hG'
  · obtain ⟨G₁, hG₁, rfl⟩ := Option.map_eq_some_iff.1 hG'
    exact hN i G₁ hG₁ hm
  · exact hN i G hG' hm

theorem withRows_off (o g : ℕ) : ∀ (l : List OnBytes.Row) (T : Statement),
    Off o T (OnBytes.Slice.withRows T g l)
  | [], T => Off.refl o T
  | r :: l, T => (withRow_off o g r T).trans (withRows_off o g l _)

theorem off_rows {o g : ℕ} {rows : List OnBytes.Row} {T T' : Statement}
    (h : addRowsG T g rows = .ok T') : Off o T T' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.addRowsP at hd
    split at hd
    · rw [from_rows g rows _ d hd]
      exact withRows_off o g rows _
    · cases hd
  · cases h

theorem off_fresh (o c m : ℕ) (T : Statement) : Off o T (withFresh T c m) := by
  refine ⟨rfl, fun hN i G hG hm => ?_⟩
  have hG' : (T.groups.push (freshGroup c m))[i]? = some G := hG
  rw [Array.getElem?_push] at hG'
  split at hG'
  · obtain rfl := Option.some.inj hG'
    exact absurd hm (by simp [freshGroup])
  · exact hN i G hG' hm

theorem off_sent {o : ℕ} {T T' : Statement} {notices : Array OracleNotice} {ids : Array ℕ}
    (K : SentOk T notices ids T') (ho : o < T.oracles.size) : Off o T T' :=
  off_same (K.old o ho) K.groups

theorem ids_ge {n0 n : ℕ} {ids : Array ℕ} (h : ids = (Array.range n).map (· + n0)) :
    ∀ m ∈ ids, n0 ≤ m := by
  intro m hm
  subst h
  simp only [Array.mem_map, Array.mem_range] at hm
  obtain ⟨a, _, rfl⟩ := hm
  omega

theorem mem_of_extract {α : Type} {a : α} {xs : Array α} {i j : ℕ} (h : a ∈ xs.extract i j) :
    a ∈ xs := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 h
  rw [Array.getElem_extract]
  exact Array.getElem_mem _

/-- **An accepting switch.** -/
theorem switch_off {P : _root_.Tw.K2.Par9} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front}
    {r₁ r₂ : Fmt.RoundView} {cols : List _root_.Tw.K2.Col} {w : SwOut} {roots : ℕ}
    (hw : switchE switchBehind P sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) {o : ℕ}
    (ho : o < x.st.oracles.size) :
    Off o x.st w.st ∧ ∀ m ∈ w.out.others, x.st.oracles.size ≤ m := by
  obtain ⟨y, k⟩ := switchE_inv hw
  obtain ⟨c, Y, S1, S2, S3, rows, hB⟩ := switchBehind_inv k.hBehind
  have hK := sent_ok k.hSend
  have hge := ids_ge hK.ids
  have hs : 0 < y.ids.size := by
    rw [hK.ids]
    simp [switchNotices]
  have h0 : x.st.oracles.size ≤ y.ids.getD 0 noId := by
    apply hge
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
    exact Array.getElem_mem hs
  have g0 : Off o x.st y.st := off_sent hK ho
  have g1 : Off o y.st S1 := by
    have h := hB.hLedger
    split at h
    · exact off_close h (by show y.ids.getD 0 noId ≠ o; omega)
    · cases h
      exact Off.refl _ _
  have g2 : Off o S1 S2 := off_join hB.hJoinG (by show y.ids.getD 0 noId ≠ o; omega)
  have g3 : Off o S2 S3 := by
    have h := hB.hJoinKept
    rw [← Array.foldlM_toList] at h
    refine off_joins o _ (fun p : ℕ × KeptTarget => p.1) (fun p => p.2.keptAgain) _ S2 S3 h
      fun p hp => ?_
    rw [Array.toList_zip] at hp
    have h1 : p.1 ∈ y.ids := mem_of_extract (Array.mem_def.2 (List.of_mem_zip hp).1)
    have := hge _ h1
    show p.1 ≠ o
    omega
  have g4 : Off o S3 w.st := off_rows hB.hAdded
  refine ⟨(((g0.trans g1).trans g2).trans g3).trans g4, fun m hm => ?_⟩
  rw [hB.hOut] at hm
  exact hge m (mem_of_extract hm)

/-- The link's own messages' joins behind the switch. -/
theorem behind_off {T T' : Statement} {x : _root_.Tw.K2.Front} {sw : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array ℕ} (h : firstBehind T x sw plain = .ok (T', f, mine)) {o n0 : ℕ}
    (hge : ∀ m ∈ sw.others, n0 ≤ m) (ho : o < n0) : Off o T T' := by
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 h
  have hj := bA.joins
  rw [OnBytes.zipT_eq] at hj
  refine off_joins o _ (fun y : Params.ReqMessage × ℕ => y.2) (fun y => decide (0 < y.1.life)) _
    T T' hj fun q hq => ?_
  have h2 : q.2 ∈ mine := Array.mem_def.2 (List.of_mem_zip hq).2
  rw [bA.theOwn] at h2
  have := hge _ (mem_of_extract h2)
  show q.2 ≠ o
  omega

/-- **At a link.** -/
theorem link_off {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') {o : ℕ}
    (ho : o < s.st.oracles.size) : Off o s.st s'.st := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
  obtain ⟨e1, _⟩ := firstFront_st k.hFront
  have hsz : x.st.oracles.size = s.st.oracles.size := by rw [e1]; rfl
  have a0 : Off o s.st x.st := by
    rw [e1]
    exact off_fresh ..
  obtain ⟨a1, hge⟩ := switch_off k.hSwitch (by rw [hsz]; exact ho)
  have a2 := behind_off k.hBehind hge (by rw [hsz]; exact ho)
  rw [k.hOut]
  exact (a0.trans a1).trans a2

/-- **At the head's link**: the switch, then the quiet step that opens the link. -/
theorem head_off {p : P2} {nm : String} {pl : VerifiableInference.Desc.Place} {HP : HeadPar}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hp : p.stands = .head)
    (h : ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm pl HP)).decide s rs gs = .ok s') {o : ℕ}
    (ho : o < s.st.oracles.size) : Off o s.st s'.st := by
  simp only [Block.andThen, headOpened, roundlessBlock] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  obtain ⟨r₁, r₂, a, G₀, w, roots, _, k⟩ := head_inv hp h₁'
  obtain ⟨a1, hge⟩ := switch_off k.hSwitch (o := o) ho
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff HP m s').1 h₂
  have ha2 : a2 = { a with kept := w.out.kept, ids := w.out.others } := by
    have e := q.here
    rw [k.hOut] at e
    injection e with e
    exact e.symm
  have hms : m.st = w.st := by rw [k.hOut]
  have b1 : Off o m.st st := behind_off q.behind (n0 := s.st.oracles.size)
    (fun z hz => hge z (by rw [ha2] at hz; exact hz)) ho
  have e' : s'.st = st := by rw [q.out']
  rw [e']
  rw [hms] at b1
  exact a1.trans b1

/-- **At the finish**: the way in, the switch, the way out. -/
theorem finish_off {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hp : p.stands = .finish) (h : (finishPlace p : Block S Unit).decide s rs gs = .ok s') {o : ℕ}
    (ho : o < s.st.oracles.size) : Off o s.st s'.st := by
  simp only [finishPlace, Block.andThen, roundlessBlock] at h
  obtain ⟨s₂, h₂, h₃⟩ := bindOk h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h₂
  have e1 := finishFrontQ_st h₁
  have a0 : Off o s.st s₁.st := by
    rw [e1]
    exact off_fresh ..
  have hsz : s₁.st.oracles.size = s.st.oracles.size := by rw [e1]; rfl
  have h₂' : decideWith sendByL8 p s₁ _ _ = .ok s₂ := h₂
  obtain ⟨r₁, r₂, a, G₀, w, roots, _, k⟩ := finish_inv hp h₂'
  obtain ⟨a1, _⟩ := switch_off k.hSwitch (o := o) (by show o < s₁.st.oracles.size; omega)
  have e2 : s₂.st = w.st := by rw [k.hOut]
  have e3 : s'.st = s₂.st := by
    unfold finishBehindQ at h₃
    split at h₃
    · rename_i a' _
      cases hfb : _root_.Tw.K2.finishBehind a'.sw with
      | error e => rw [hfb] at h₃; cases h₃
      | ok m => rw [hfb] at h₃; cases h₃; rfl
    · cases h₃
  rw [e3, e2]
  exact a0.trans a1

/-- **THE FIELD k2 OF KeepShares.** -/
theorem k2_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    LotKeeps Z G₀ c start KindName.K2 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout n hn
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb hk
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have e' : x.decide s rs gs = .ok s' := e
  obtain ⟨l, hl1, hl2, hl3⟩ := leftIsB_iff.1 hn
  have hl1' : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := hl1
  have ho : s.out.indexMasks < s.st.oracles.size := by
    by_contra hlt
    rw [Array.getElem?_eq_none (by omega)] at hl1'
    cases hl1'
  have key : Off s.out.indexMasks s.st s'.st ∧ s'.out = s.out := by
    rcases IM.k2_mem hx with ⟨_, hno⟩ | ⟨P, nn, _, _, hform⟩
    · obtain ⟨er, her⟩ := hno s rs gs
      rw [her] at e'
      cases e'
    · rcases hform with ⟨_, ex⟩ | ⟨l', HP, _, _, ex⟩ | ⟨l', _, ex⟩
      · rw [ex] at e'
        exact ⟨finish_off (p := IM.k2P Z x.place x.name .finish nn) rfl e' ho,
          placeF1LeavesOut _ s rs gs s' e'⟩
      · rw [ex] at e'
        exact ⟨head_off (p := IM.k2P Z x.place x.name .head nn) rfl e' ho,
          andThenLeaves _ _ _ _ (k2LeavesOut _) (headOpenedLeavesOut _ _ _) s rs gs s' e'⟩
      · rw [ex] at e'
        exact ⟨link_off (p := IM.k2P Z x.place x.name .link nn) rfl e' ho,
          k2LeavesOut _ s rs gs s' e'⟩
  obtain ⟨⟨o1, o2⟩, eo⟩ := key
  refine ⟨leftIsB_iff.2 ⟨l, ?_, hl2, hl3⟩, outOfGroupsB_iff.2 fun G hG hm => ?_⟩
  · show (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) = some l
    rw [eo, o1]
    exact hl1'
  · obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hG
    rw [eo] at hm
    exact o2 (fun j G' hj => outOfGroupsB_iff.1 hout G' (Array.mem_iff_getElem?.2 ⟨j, hj⟩)) i G hi
      hm

end P1L20

#print axioms P1L20.switch_off
#print axioms P1L20.link_off
#print axioms P1L20.head_off
#print axioms P1L20.finish_off
#print axioms P1L20.k2_keeps
