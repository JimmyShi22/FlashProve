-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Law.SwSendP
/-
Johnson/Desc/K12/Law/BookWalk.lean: THE PROXIMITY TEST's BLOCK KEEPS EVERY RELATION ON THE BOOK OF TREES AND THE COUNT OF ROOTS THAT ITS TWO WRITERS KEEP: the ground's receiving (recvP) and one counted opening. A WALK ALONG THE BLOCK's OWN TEXT; BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  BR · brT · brD     the book and the count of roots, off the kind's record and off a carried state
  BookOwes ft Q      WHAT IS ASKED OF A RELATION Q ON THE TWO: reflexive · transitive · recv: kept by Ground.recvP AT THE ONE NUMBER ft OF THE CHAIN's FIRST TREE, at whatever statement · count: kept where ONE tree's count of lists rises by one. (ft is a letter so that a relation that is true at the chain's own ft alone, as «a tree's number in the book is its place in the order of sending», can be a member.)
  batJ_br · behindJ_br   the batching and the batching behind a switch leave the two as they are
  foldJ_br           the fold: at most one recvP (where the mask is the test's own)
  sampleLoop_br · sendP_br   a sending: one recvP; the admissions leave the two
  openOne_br · readOld_br    a reading of old rows: one count a tree
  switchJ_br         the switch: a sending, then a reading
  baseJ5_br          the base case: one count
  stages_br · k12_book_keeps   BookOwes p.nums.firstTree Q · a yes of the decision of proximityTestKind guardedProximityTestParts p, from t0 to tE ⇒ Q (brT t0) (brT tE): every receiving inside the block is at the place's own firstTree. NO PREMISE ON THE PLACE, THE RECORD OR THE VIEW
  bookOwes_counts · k12_roots   A MEMBER OF BookOwes (the roots rise just as trees come; none is lost), and what it gives: the first two clauses of OutK3 (Johnson/Desc/K12/Law/OutK3.lean) without that theorem's two premises on the place
WHAT FOR: three things that hang on a walk along a chain: that a tree's number in the book is its place in the order of sending · the record's count of roots at a border · (the codes). WHAT OF THEM IS PAID AT THIS BLOCK ALREADY, AT FIXED RELATIONS: the codes stand, with every message's shape and every tree's shape, number and parts (KeepsK: k12_out, Johnson/Desc/K12/Law/OutK.lean) · the roots rise just as trees come, none is lost, book and statement are in step (OutK3: k12_out3, Johnson/Desc/K12/Law/OutK3.lean): both under early masks and one answer.
WHAT IT DOES NOT SAY: NOTHING OF A RELATION THAT READS THE STATEMENT: the step behind a switch's sending (Tw.L9.switchBehind) shuts a ledger, joins and adds rows by texts of its own, not by the ground's plain functions closeLedgerP | joinP | addRowP; WHAT BARS THE WIDER FORM ARE THREE AGREEMENT LEMMAS, TYPED NOWHERE: (1) the ledger's shutting inside switchBehind (Johnson/Top/H0/Tw/L9/Switch.lean) against Ground.closeLedgerP · (2) Tw.L9.joinS's yes (its six guards) against Ground.joinP (joinL's clauses) · (3) Tw.L9.addRowS's yes against Ground.addRowP (rowL's eight clauses): each ties a text of the switch's files to a text of the plain ground's (Johnson/Desc/First/Base/Ground.lean); and the beginning of a test (beginRunP) stands outside the ground's ten. Until then «whatever the ground's functions keep, the block keeps» stands for the book and the roots alone · that any Q meets BookOwes: the spender's · nothing on the opened columns.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)
open _root_.Desc.Plain (DState GPar sendP sampleLoop)

/-- The book of trees and the count of roots. -/
abbrev BR : Type := TreeBook × ℕ

def brT (t : T12) : BR := (t.book, t.roots)
def brD (d : DState Unit) : BR := (d.book, d.roots)

/-- What is asked of a relation on the two. -/
structure BookOwes (ft : ℕ) (Q : BR → BR → Prop) : Prop where
  refl : ∀ x, Q x x
  trans : ∀ {a b c}, Q a b → Q b c → Q a c
  recv : ∀ (d d' : DState Unit) (sent : Array OracleNotice) (ids : Array ℕ),
    Ground.recvP ft d sent = some (ids, d') → Q (brD d) (brD d')
  count : ∀ (B : TreeBook) (r t : ℕ),
    Q (B, r) ({ B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }, r)

variable {ft : ℕ} {Q : BR → BR → Prop}

theorem batJ_br (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) : brT t1 = brT t := by
  unfold batJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨⟨row, L⟩, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.batE at hx
    split at hx
    · obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨_, _, hx⟩ := bind_ok hx
      cases hx
      rfl
    · cases hx
  · cases h

theorem behindJ_br (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (h : (behindJ p j nxt cut).decide t2 [] [] = .ok t3) : brT t3 = brT t2 := by
  simp only [behindJ] at h
  split at h
  · obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    replace hx := H2K.Sw.named_ok hx
    unfold VerifiableInference.Desc.Test.csTest at hx
    dsimp only at hx
    split at hx
    · cases hx
    · rename_i run s2 hb
      split at hx
      · cases hx
      · rename_i s3 ha
        split at hx
        · cases hx
        · cases hx
          obtain ⟨G, lay, _, _, _, a4⟩ := beginRunE_ok hb
          have a5 := askOwedE_ok ha
          show (s3.d.book, s3.d.roots) = _
          rw [a5, a4]
          rfl
  · cases h

theorem foldJ_br (p : P12) (H : BookOwes p.nums.firstTree Q) (j : ℕ) (cur : Fmt.M1.Stage)
    (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : Q (brT t) (brT t1) := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ :=
    foldJ_form p j cur cut t t1 rs gs h
  have hd' := spendP_form hsp
  subst hd'
  rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
  · exact H.refl _
  · exact H.recv _ _ _ _ hr

theorem sampleLoop_br (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DState Unit) (left : List E),
      sampleLoop Ground.groundG p codes seeds l ys d = some (d', left) → brD d' = brD d
  | [], ys, d, d', left, h => by
    cases h
    rfl
  | (o, s) :: l, ys, d, d', left, h => by
    rw [sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d1 had
        have h1 := sampleLoop_br p codes seeds l ys' d1 d' left h
        obtain ⟨x', places, _, _, rfl⟩ := admitP_ok had
        exact h1

theorem sendP_br (p : GPar) (H : BookOwes p.firstTree Q) (own : Bool) (d d₂ : DState Unit)
    (sent : Array OracleNotice) (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ) (sd an : List E) (took : ℕ)
    (h : sendP Ground.groundG p own d sent r₁ r₂ = some (ids, sd, an, took, d₂)) :
    Q (brD d) (brD d₂) := by
  unfold sendP at h
  obtain ⟨⟨ids', d₁⟩, hr, h⟩ := obind_ok h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := obind_ok h
  obtain ⟨seeds, _, h⟩ := obind_ok h
  obtain ⟨an', _, h⟩ := obind_ok h
  split at h
  · obtain ⟨⟨d₂', left⟩, hl, h⟩ := obind_ok h
    split at h
    · cases h
      have h1 := sampleLoop_br _ _ _ _ _ _ _ _ hl
      rw [h1]
      exact H.recv _ _ _ _ hr
    · cases h
  · cases h

theorem openOne_br (H : BookOwes ft Q) (r : ℕ) (S : Statement) (f0 : ℕ) (pos : Positions)
    (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : Tw.L9.openOne S f0 pos B0 t s = .ok s') : Q (s.1, r) (s'.1, r) := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact H.count _ _ _)
      | cases h
  · cases h

theorem foldlM_brE {α σ : Type} (R : σ → σ → Prop) (hr : ∀ s, R s s)
    (ht : ∀ a b c, R a b → R b c → R a c) (f : σ → α → Except String σ)
    (hf : ∀ s a s', f s a = .ok s' → R s s') : ∀ (l : List α) (s s' : σ),
    l.foldlM f s = .ok s' → R s s'
  | [], s, s', h => by cases h; exact hr s
  | a :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := bind_ok h
    exact ht _ _ _ (hf _ _ _ h1) (foldlM_brE R hr ht f hf l s1 s' h2)

theorem readOld_br (H : BookOwes ft Q) (r : ℕ) (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, y)) :
    Q (i.book, r) (B, r) := by
  unfold Tw.L9.readOld at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i B' left' cols hfold
        split at h
        · cases h
        · split at h
          · cases h
          · cases h
            exact foldlM_brE
              (fun (a b : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F))) =>
                Q (a.1, r) (b.1, r)) (fun _ => H.refl _) (fun _ _ _ h1 h2 => H.trans h1 h2) _
              (fun s a s' hs => openOne_br H r _ _ _ _ _ _ _ hs) _ _ _ hfold

theorem switchBehind_br (H : BookOwes ft Q) (r : ℕ) (i : Tw.L9.SwIn) (o : Tw.L9.SwOut)
    (h : Tw.L9.switchBehind i = .ok o) : Q (i.book, r) (o.book, r) := by
  rw [switchBehind_eq] at h
  cases hcode : i.st.codes.base[i.old.code]? with
  | none => simp only [hcode] at h; cases h
  | some code =>
  simp only [hcode, pure_bind] at h
  obtain ⟨pos, _, h⟩ := bind_ok h
  obtain ⟨⟨B, left, y⟩, hread, h⟩ := bind_ok h
  have hb : ∀ (out : Switched) (S1 : Statement), tailB i out B left y S1 = .ok o → o.book = B := by
    intro out S1 ht
    unfold tailB at ht
    obtain ⟨S2, _, ht⟩ := bind_ok ht
    obtain ⟨S3, _, ht⟩ := bind_ok ht
    dsimp only at ht
    split at ht
    · split at ht
      · cases ht
      · simp only [pure_bind] at ht
        split at ht
        · obtain ⟨S4, _, ht⟩ := bind_ok ht
          cases ht
          rfl
        · cases ht
    · cases ht
  have hB : o.book = B := by
    by_cases hm : 0 < i.T.shape.maskRows
    · rw [if_pos hm] at h
      obtain ⟨S1, _, h⟩ := bind_ok h
      exact hb _ _ h
    · rw [if_neg hm] at h
      exact hb _ _ h
  rw [hB]
  exact readOld_br H r i pos B left y hread

theorem switchJ_br (p : P12) (H : BookOwes p.nums.firstTree Q) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) (t1 t2 : T12) (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2) : Q (brT t1) (brT t2) := by
  simp only [switchJ] at h1
  split at h1
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out', theta⟩, s'⟩, hx, h1⟩ := bind_ok h1
    obtain ⟨rfl, _⟩ := back_ok h1
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    obtain ⟨e₁, e₂, es, ids, sd, an, took, d₂, x, o, _, hsend, _, _, hbeh, _, hd⟩ :=
      switchE_sendP rows _ gp _ _ s' out' theta r1 r2 hr hx
    have k1 := sendP_br _ H _ _ _ _ _ _ _ _ _ _ hsend
    have k2 := switchBehind_br H d₂.roots _ o hbeh
    show Q (t1.book, t1.roots) (s'.d.book, s'.d.roots)
    rw [hd]
    exact H.trans k1 k2
  · cases h1

theorem baseJ5_br (H : BookOwes ft Q) (p : P12) (j : ℕ) (cur : Fmt.M1.Stage)
    (cut : List Fmt.DeclaredRound) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) : Q (brT t) (brT tE) := by
  obtain ⟨star, a, _, _, rfl⟩ := baseJ5_form p j cur cut t tE rs gs h
  exact H.count _ _ _

/-- Along the stages. -/
theorem stages_br (p : P12) (H : BookOwes p.nums.firstTree Q) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE → Q (brT t) (brT tE)
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact baseJ5_br H p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
    have k1 := foldJ_br p H j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur l : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switchJ_br p H j cur nxt rest.isEmpty _ t1 t2 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2)
    have k3 := behindJ_br p (j + 1) nxt _ t2 t3 ((like_P5 p).behind _ _ _ _ _ f3)
    have k4 := stages_br p H rest (j + 1) nxt _ t3 tE _ _ f5
    rw [k3] at k4
    exact H.trans (H.trans k1 k2) k4


theorem k12_book_keeps (p : P12) (H : BookOwes p.nums.firstTree Q) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : Q (brT t0) (brT tE) := by
  obtain ⟨first, rest, ds, tF, t1, hs, hr, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  have k1 := batJ_br p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  have k2 := stages_br p H rest 0 first _ _ tE _ _ hst
  rw [k1] at k2
  exact k2

/-- A MEMBER, so that the frame is not empty: the roots rise just as trees come, and none is lost. -/
theorem bookOwes_counts (ft : ℕ) :
    BookOwes ft fun a b => b.2 + a.1.trees.size = a.2 + b.1.trees.size ∧ a.2 ≤ b.2 where
  refl := fun _ => ⟨rfl, Nat.le_refl _⟩
  trans := fun h1 h2 => ⟨by have := h1.1; have := h2.1; omega, h1.2.trans h2.2⟩
  recv := fun d d' sent ids h => by
    obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok h
    obtain ⟨b1, _⟩ := bookSentP_sizes ft d.roots d.st d.book sent lay
    refine ⟨?_, Nat.le_add_right _ _⟩
    show d.roots + lay.shapes.size + d.book.trees.size =
      d.roots + (bookSentP ft d.roots d.st d.book sent lay).trees.size
    rw [b1]
    omega
  count := fun B r t => by
    refine ⟨?_, Nat.le_refl _⟩
    show r + B.trees.size = r + (B.trees.modify t _).size
    rw [Array.size_modify]

/-- What that member gives: OutK3's first two clauses WITHOUT «early masks» and «one answer». -/
theorem k12_roots (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    tE.roots + t0.book.trees.size = t0.roots + tE.book.trees.size ∧ t0.roots ≤ tE.roots :=
  k12_book_keeps p (bookOwes_counts _) t0 tE rs gs h

end H2K.Out

#print axioms H2K.Out.sendP_br
#print axioms H2K.Out.readOld_br
#print axioms H2K.Out.switchJ_br
#print axioms H2K.Out.stages_br
#print axioms H2K.Out.k12_book_keeps
#print axioms H2K.Out.bookOwes_counts
#print axioms H2K.Out.k12_roots
