-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BookWalk
import Johnson.Desc.K12.Law.SwAgree
import Johnson.Desc.K12.Law.CallsDef
/-
Johnson/Desc/K12/Law/Calls.lean: A YES OF THE PROXIMITY TEST's BLOCK IS A RUN OF THE GROUND's PLAIN CALLS. A WALK ALONG THE BLOCK's OWN TEXT; BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  dT t l          the kind's record as a carried state of the ground: its statement, book and count of roots, with opened columns l
  Call ft d d' · Calls ft d d'   one step · a run of steps: H2K/CallsDef.lean: a yes of newGroupP · recvP AT ft · admitP OF ROWS THAT rowsFor HAS MADE at the state's codes and the message's own shape, a shape that fits the codes, from seeds long enough · joinP · addRowP · closeLedgerP · spendAsMaskP · beginRunP · one tree's count of lists + 1 · the opened columns alone
  k12_calls       a yes of the decision of proximityTestKind guardedProximityTestParts p, from t0 to tE ⇒ ∀ l l', Calls p.nums.firstTree (dT t0 l) (dT tE l'). NO PREMISE ON THE PLACE, THE RECORD OR THE VIEW
HOW: part by part: the batching and the batching behind a switch: beginRunP · the fold: recvP where the mask is the test's own, spendAsMaskP, newGroupP · the switch: sendP = recvP and an admitP a sampled message; the step behind it: a count a tree read, then the ledger's shutting, the joins and the rows, WHICH ARE THE GROUND's CALLS BY H2K/SwAgree.lean · the base case: spendAsMaskP (its guard lastPairOk holds that call's four clauses) and one count.
WHAT FOR: every invariant that is carried along a chain by «each plain function of the ground keeps it» crosses this block by one induction.
EMPTINESS: every statement here stands under «a yes of the block's decision»: no member of that is shown in Lean; the block's step has said yes at the four proximity tests of both stored example proofs (runs' words).
WHAT IT DOES NOT SAY: that the rows which rowsFor makes lie on their message: a law on the sample's row, owed by whoever wants an invariant that reads them · nothing on what the calls' yeses mean.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)
open _root_.Desc.Plain (DState GPar sendP sampleLoop rowsFor)

/-- The kind's record as a carried state of the ground. -/
def dT (t : T12) (l : List (Nat × Nat × List UInt64)) : DS := ⟨t.st, t.book, t.roots, l, ()⟩

variable {ft : ℕ}

/-- The beginning of a test reads the statement alone. -/
theorem beginRunP_at {L L' : Type} (d : DState L) (e : DState L') (hst : e.st = d.st) {g : ℕ}
    {run : RunInput} {d' : DState L} (h : Ground.beginRunP d g = some (run, d')) :
    Ground.beginRunP e g = some (run, { e with st := d'.st }) := by
  unfold Ground.beginRunP at h ⊢
  rw [hst]
  split at h
  · rename_i hok
    rw [if_pos hok]
    obtain ⟨G, hG, h⟩ := obind_ok h
    cases h
    rw [hG]
    rfl
  · cases h

theorem batJ_calls (p : P12) (cut : List Fmt.DeclaredRound) (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (batJ p cut).decide t rs gs = .ok t1) (l l' : List (Nat × Nat × List UInt64)) :
    Calls ft (dT t l) (dT t1 l') := by
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
      obtain ⟨⟨row', L', S'⟩, hb, hx⟩ := bind_ok hx
      cases hx
      have hb' := mapError_ok hb
      unfold First.Close.bat at hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨⟨input, d⟩, hbeg, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      obtain ⟨_, _, hb'⟩ := bind_ok hb'
      cases hb'
      have k := beginRunP_at (First.Close.onSt t.st) (dT t l) rfl (got_ok hbeg)
      exact (Calls.one (.begin k)).trans (Calls.toCols _ l')
    · cases hx
  · cases h

theorem beginRunE_call {g : ℕ} {s s' : H2K.PS} {run : RunInput}
    (h : (H2K.beginRunE g s).toOption = some (run, s')) :
    Ground.beginRunP s.d g = some (run, s'.d) := by
  unfold H2K.beginRunE at h
  cases hb : Ground.beginRunP s.d g with
  | none => rw [hb] at h; cases h
  | some v =>
    rw [hb] at h
    cases h
    rfl

theorem behindJ_calls (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (h : (behindJ p j nxt cut).decide t2 [] [] = .ok t3)
    (l l' : List (Nat × Nat × List UInt64)) : Calls ft (dT t2 l) (dT t3 l') := by
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
          have a5 := askOwedE_ok ha
          have hbp := beginRunE_call hb
          obtain ⟨G, lay', _, _, _, a4⟩ := beginRunE_ok hb
          have k := beginRunP_at (lay p [] (cut.getLast?.map (·.entry)) t2 [] []).d (dT t2 l) rfl hbp
          refine (Calls.one (.begin k)).trans ?_
          show Calls ft _ (⟨s3.d.st, s3.d.book, s3.d.roots, l', ()⟩ : DS)
          rw [a5, a4]
          exact Calls.toCols _ l'
  · cases h

theorem foldJ_calls (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1)
    (l l' : List (Nat × Nat × List UInt64)) : Calls p.nums.firstTree (dT t l) (dT t1 l') := by
  simp only [foldJ] at h
  split at h
  · rename_i row L c n e1 e2 e3
    obtain ⟨⟨rows, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨⟨gp, s2⟩, hy, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.foldE at hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨⟨rows', d'⟩, hf, hx⟩ := bind_ok hx
    cases hx
    obtain ⟨id, d1, hcase, hsp⟩ := foldD_state _ _ _ _ _ _ _ _ _ (mapError_ok hf)
    have k0 : Calls p.nums.firstTree (dT t l) (lay p cut none t rs gs).d := Calls.toCols _ _
    have k1 : Calls p.nums.firstTree (lay p cut none t rs gs).d d1 := by
      rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
      · exact .nil _
      · exact .one (.recv hr)
    have k2 : Calls p.nums.firstTree d1 d' := .one (.spend hsp)
    unfold H2K.newGroupE at hy
    cases hg : Ground.newGroupP d' n.1 n.2 with
    | none => simp [hg, H2K.opt, Except.map] at hy
    | some v =>
      simp only [hg, H2K.opt, Except.map] at hy
      cases hy
      have k3 : Calls p.nums.firstTree d' v.2 := .one (.newGroup hg)
      exact ((k0.trans k1).trans (k2.trans k3)).trans (Calls.toCols _ l')
  · cases h

theorem admitted_shape (S : Statement) (o : ℕ) (s : OracleShape) (pl : List PadPlace)
    (rows : Array Row) (o' : ℕ) :
    ((admitted S o s pl rows).oracles[o']?).map (·.shape) = (S.oracles[o']?).map (·.shape) := by
  show ((S.oracles.modify o _)[o']?).map (·.shape) = _
  rw [Array.getElem?_modify]
  split
  · cases S.oracles[o']? <;> rfl
  · rfl

theorem sampleLoop_calls (p : GPar) (codes : Codes) (seeds : List SampleSeed) :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DS) (left : List E),
      d.st.codes = codes → (∀ x ∈ l, (d.st.oracles[x.1]?).map (·.shape) = some x.2) →
      (∀ x ∈ l, Own.sentShapeFits codes x.2 = true ∧
        ∀ sd ∈ seeds, (Send.cube codes x.2).bits ≤ sd.z.length) →
      sampleLoop Ground.groundG p codes seeds l ys d = some (d', left) → Calls ft d d'
  | [], ys, d, d', left, _, _, _, h => by
    cases h
    exact .nil _
  | (o, s) :: l, ys, d, d', left, hc, hs, hq, h => by
    rw [sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' hrows
      split at h
      · cases h
      · rename_i d1 had
        have had' : Ground.admitP d o rows = some d1 := had
        obtain ⟨x', places, _, _, e1⟩ := admitP_ok had'
        have k1 : Call ft d d1 := .admit (hs (o, s) (List.mem_cons_self))
          (by rw [hc]; exact (hq (o, s) (List.mem_cons_self)).1)
          (by rw [hc]; exact (hq (o, s) (List.mem_cons_self)).2) (by rw [hc]; exact hrows) had'
        refine .cons k1 (sampleLoop_calls p codes seeds l ys' d1 d' left ?_ ?_
          (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h)
        · rw [e1]
          exact hc
        · intro x hx
          rw [e1]
          show ((admitted d.st o x'.shape places rows).oracles[x.1]?).map (·.shape) = _
          rw [admitted_shape]
          exact hs x (List.mem_cons_of_mem _ hx)

theorem mapM_zip {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ x ∈ l.zip r, f x.1 = some x.2
  | [], r, h, x, hx => by simp at hx
  | a :: l, r, h, x, hx => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := obind_ok h
    obtain ⟨r', hr', h⟩ := obind_ok h
    cases h
    rw [List.zip_cons_cons] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact mapM_zip f l r' hr' x hx

theorem seedsMade_long (bits : ℕ) : ∀ (n : ℕ) (l : List E) (seeds : List SampleSeed),
    Own.seedsMade bits n l = some seeds → ∀ sd ∈ seeds, bits ≤ sd.z.length
  | 0, [], seeds, h, sd, hsd => by
    cases h
    cases hsd
  | 0, _ :: _, seeds, h, sd, hsd => by cases h
  | n + 1, l, seeds, h, sd, hsd => by
    rw [Own.seedsMade] at h
    split at h
    · cases h
    · rename_i beta rest hdrop
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hsd with rfl | hsd
      · show bits ≤ (l.take bits).length
        rw [List.length_take]
        have : bits < l.length := by
          by_contra c
          rw [List.drop_eq_nil_of_le (by omega)] at hdrop
          cases hdrop
        omega
      · exact seedsMade_long bits n rest t ht sd hsd

theorem le_foldl_max' {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    a ≤ l.foldl (fun b s => max b (f s)) a
  | [], _ => Nat.le_refl _
  | x :: l, a => Nat.le_trans (Nat.le_max_left a (f x)) (le_foldl_max' f l _)

theorem mem_foldl_max' {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ) (x : α), x ∈ l →
    f x ≤ l.foldl (fun b s => max b (f s)) a
  | y :: l, a, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a (f x)) (le_foldl_max' f l _)
    · exact mem_foldl_max' f l _ x h

/-- A message that has just been received has a shape that fits the codes. -/
theorem recvP_fits {f0 : ℕ} {d d₁ : DS} {sent : Array OracleNotice} {ids : Array ℕ}
    (h : Ground.recvP f0 d sent = some (ids, d₁)) (o : ℕ) (ho : o ∈ ids.toList) (s : OracleShape)
    (hs : (d₁.st.oracles[o]?).map (·.shape) = some s) :
    Own.sentShapeFits d₁.st.codes s = true := by
  have hok : Ground.ok (Ground.recvL d.st d.book sent) = true := by
    unfold Ground.recvP at h
    split at h
    · assumption
    · cases h
  obtain ⟨lay, _, _, rfl, rfl⟩ := recvP_ok h
  simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at ho
  obtain ⟨i, hi, rfl⟩ := ho
  have e : (stSent d.st sent).oracles[i + d.st.oracles.size]? =
      (sent[i]?).map fun n => { shape := n.shape } := by
    rw [Nat.add_comm]
    exact stSent_new d.st sent i
  have hs' : ((stSent d.st sent).oracles[i + d.st.oracles.size]?).map (·.shape) = some s := hs
  rw [e, Array.getElem?_eq_getElem hi] at hs'
  obtain rfl : sent[i].shape = s := Option.some.inj hs'
  have hall : (sent.all fun n => Own.sentShapeFits d.st.codes n.shape) = true := by
    simp only [Ground.recvL, Ground.sentL, Ground.ok, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
    exact hok.1
  exact (Array.all_eq_true'.1 hall) sent[i] (Array.getElem_mem hi)

theorem sendP_calls (p : GPar) (own : Bool) (d d₂ : DS) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ) (sd an : List E) (took : ℕ)
    (h : sendP Ground.groundG p own d sent r₁ r₂ = some (ids, sd, an, took, d₂)) :
    Calls p.firstTree d d₂ := by
  unfold sendP at h
  obtain ⟨⟨ids', d₁⟩, hr, h⟩ := obind_ok h
  dsimp only at h
  obtain ⟨shapes, hsh, h⟩ := obind_ok h
  obtain ⟨seeds, hseeds, h⟩ := obind_ok h
  obtain ⟨an', _, h⟩ := obind_ok h
  split at h
  · obtain ⟨⟨d₂', left⟩, hl, h⟩ := obind_ok h
    split at h
    · cases h
      refine .cons (.recv hr) (sampleLoop_calls _ _ _ _ _ _ _ _ rfl (mapM_zip _ _ _ hsh) ?_ hl)
      intro x hx
      have hx1 : x.1 ∈ ids.toList := (List.mem_filter.1 (List.of_mem_zip hx).1).1
      refine ⟨recvP_fits hr x.1 hx1 x.2 (mapM_zip _ _ _ hsh x hx), fun sd hsd => ?_⟩
      exact Nat.le_trans (mem_foldl_max' (fun s => (Send.cube d₁.st.codes s).bits) shapes 0 x.2
        (List.of_mem_zip hx).2) (seedsMade_long _ _ _ _ hseeds sd hsd)
    · cases h
  · cases h

/-- A carried state with another book and other opened columns, reached by counts alone. -/
theorem openOne_calls (d : DS) (S : Statement) (f0 : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : Tw.L9.openOne S f0 pos B0 t s = .ok s') :
    Calls ft { d with book := s.1 } { d with book := s'.1 } := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact .one (.count { d with book := s.1 } t))
      | cases h
  · cases h

theorem readOld_calls (d : DS) (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, y)) :
    Calls ft { d with book := i.book } { d with book := B } := by
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
                Calls ft { d with book := a.1 } { d with book := b.1 }) (fun _ => .nil _)
              (fun _ _ _ h1 h2 => h1.trans h2) _
              (fun s a s' hs => openOne_calls d _ _ _ _ _ _ _ hs) _ _ _ hfold

/-- Joins one behind the other. -/
theorem joins_calls (d : DS) (g : ℕ) : ∀ (l : List (ℕ × KeptTarget)) (S S' : Statement),
    l.foldlM (fun S p => Tw.L9.joinS S g p.1 p.2.keptAgain) S = .ok S' →
    Calls ft { d with st := S } { d with st := S' }
  | [], S, S', h => by cases h; exact .nil _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bind_ok h
    exact .cons (.join (joinS_joinP { d with st := S } g a.1 a.2.keptAgain S1 h1))
      (joins_calls d g l S1 S' h2)

/-- Rows one behind the other. -/
theorem rows_calls (d : DS) (g : ℕ) : ∀ (l : List Row) (S S' : Statement),
    l.foldlM (fun S r => Tw.L9.addRowS S g r) S = .ok S' →
    Calls ft { d with st := S } { d with st := S' }
  | [], S, S', h => by cases h; exact .nil _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bind_ok h
    exact .cons (.addRow (addRowS_addRowP { d with st := S } g a S1 h1)) (rows_calls d g l S1 S' h2)

theorem tailB_calls (d : DS) (i : Tw.L9.SwIn) (out : Switched) (B : TreeBook)
    (left : List Tw.L9.Col) (y : Array E) (S1 : Statement) (o : Tw.L9.SwOut)
    (h : tailB i out B left y S1 = .ok o) :
    Calls ft { d with st := S1 } { d with st := o.st } ∧ o.book = B := by
  unfold tailB at h
  obtain ⟨S2, h2, h⟩ := bind_ok h
  obtain ⟨S3, h3, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · simp only [pure_bind] at h
      split at h
      · obtain ⟨S4, h4, h⟩ := bind_ok h
        cases h
        rw [← Array.foldlM_toList] at h3
        exact ⟨(Calls.one (.join (joinS_joinP { d with st := S1 } _ _ _ S2 h2))).trans
          ((joins_calls d _ _ S2 S3 h3).trans (rows_calls d _ _ S3 S4 h4)), rfl⟩
      · cases h
  · cases h

theorem switchBehind_calls (d : DS) (i : Tw.L9.SwIn) (o : Tw.L9.SwOut)
    (h : Tw.L9.switchBehind i = .ok o) :
    Calls ft { d with st := i.st, book := i.book } { d with st := o.st, book := o.book } := by
  rw [switchBehind_eq] at h
  cases hcode : i.st.codes.base[i.old.code]? with
  | none => simp only [hcode] at h; cases h
  | some code =>
  simp only [hcode, pure_bind] at h
  obtain ⟨pos, _, h⟩ := bind_ok h
  obtain ⟨⟨B, left, y⟩, hread, h⟩ := bind_ok h
  have k1 : Calls ft { d with st := i.st, book := i.book } { d with st := i.st, book := B } :=
    readOld_calls { d with st := i.st } i pos B left y hread
  refine k1.trans ?_
  by_cases hm : 0 < i.T.shape.maskRows
  · rw [if_pos hm] at h
    obtain ⟨S1, h1, h⟩ := bind_ok h
    split at h1
    · rename_i hlt
      cases h1
      obtain ⟨k2, hB⟩ := tailB_calls (ft := ft) { d with book := B } i _ B left y _ o h
      rw [hB]
      exact .cons (.closeLedger (shut_closeLedgerP { d with st := i.st, book := B } _ hlt)) k2
    · cases h1
  · rw [if_neg hm] at h
    obtain ⟨k2, hB⟩ := tailB_calls (ft := ft) { d with book := B } i _ B left y _ o h
    rw [hB]
    exact k2

theorem switchJ_calls (p : P12) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) (t1 t2 : T12) (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (l l' : List (Nat × Nat × List UInt64)) : Calls p.nums.firstTree (dT t1 l) (dT t2 l') := by
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
    have k0 : Calls p.nums.firstTree (dT t1 l) (lay p cut none t1 rs gs).d := Calls.toCols _ _
    have k1 : Calls p.nums.firstTree (lay p cut none t1 rs gs).d d₂ :=
      sendP_calls _ _ _ _ _ _ _ _ _ _ _ hsend
    have k2 := switchBehind_calls (ft := p.nums.firstTree) d₂ _ o hbeh
    show Calls _ _ (⟨s'.d.st, s'.d.book, s'.d.roots, l', ()⟩ : DS)
    rw [hd]
    exact ((k0.trans k1).trans k2).trans (Calls.toCols _ l')
  · cases h1

/-- The base case's guard holds the four clauses of the spending. -/
theorem lastPair_spend (P : Prox.BasePar) (d : DS) (c : IoppStage) (m star : ℕ)
    (h : lastPairOk P d.st c m star = true) :
    Ground.spendAsMaskP d star = some { d with st := { d.st with
      oracles := d.st.oracles.modify star fun x => { x with spentAsMask := true } } } := by
  unfold lastPairOk at h
  split at h
  · rename_i k z x o e1 e2 e3 e4
    simp only [Bool.and_eq_true] at h
    unfold Ground.spendAsMaskP
    rw [if_pos (by
      simp only [Ground.spendAsMaskL, Ground.ok, Ground.has, e4, List.all_cons, List.all_nil,
        Option.isSome_some, Option.map_some, Option.getD_some, Bool.and_true, Bool.and_eq_true]
      exact ⟨trivial, h.1.1.2, h.1.2, h.2⟩)]
  · cases h

theorem baseJ5_calls (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE)
    (l l' : List (Nat × Nat × List UInt64)) : Calls ft (dT t l) (dT tE l') := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨cl, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cl', _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨m, _, h⟩ := bind_ok h
    obtain ⟨star, hs, h⟩ := bind_ok h
    obtain ⟨_, hp, h⟩ := bind_ok h
    obtain ⟨a, _, h⟩ := bind_ok h
    cases h
    have k1 := lastPair_spend _ (dT t l) _ m star (H2K.FoldLaw.need_ok hp)
    exact (Calls.cons (.spend k1) (.one (.count _ a))).trans (Calls.toCols _ l')
  · cases h

/-- Along the stages. -/
theorem stages_calls (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (la : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (stagesFrom guardedProximityTestParts p j cur rest la : Blk').decide t rs gs = .ok tE →
    ∀ l l' : List (Nat × Nat × List UInt64), Calls p.nums.firstTree (dT t l) (dT tE l')
  | [], j, cur, la, t, tE, rs, gs, h, l, l' => by
    rw [stagesFrom_last] at h
    exact baseJ5_calls p _ _ _ _ _ _ _ (ranged_ok _ _ _ _ _ _ h).1 l l'
  | nxt :: rest, j, cur, la, t, tE, rs, gs, h, l, l' => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur nxt rest la t tE rs gs).1 h
    have k1 := foldJ_calls p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1) l []
    have hlen : ((rs.drop (foldAt guardedProximityTestParts p j cur la : Blk').rounds.length).take
        (switchAt guardedProximityTestParts p j cur nxt rest.isEmpty la : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((la.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switchJ_calls p j cur nxt rest.isEmpty _ t1 t2 _ _ hlen
      ((like_P5 p).switch _ _ _ _ _ _ _ _ _ f2) [] []
    have k3 := behindJ_calls (ft := p.nums.firstTree) p (j + 1) nxt _ t2 t3
      ((like_P5 p).behind _ _ _ _ _ f3) [] []
    have k4 := stages_calls p rest (j + 1) nxt _ t3 tE _ _ f5 [] l'
    exact ((k1.trans k2).trans k3).trans k4


theorem k12_calls (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE)
    (l l' : List (Nat × Nat × List UInt64)) : Calls p.nums.firstTree (dT t0 l) (dT tE l') := by
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
  exact (batJ_calls p _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat) l []).trans
    (stages_calls p rest 0 first _ _ tE _ _ hst [] l')

end H2K.Out

#print axioms H2K.Out.sendP_calls
#print axioms H2K.Out.switchBehind_calls
#print axioms H2K.Out.baseJ5_calls
#print axioms H2K.Out.k12_calls
