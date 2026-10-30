-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OutK.lean: what the record is that a yes of the decision of the proximity test
(the kind K12) leaves, first part: what stands.

An outright theorem on the text of the block: no premise on the view, and of the place only p.early
= true and p.answers = 1. Statements and proofs.
Of which text. It holds of proximityTestKind X p (Johnson/Desc/K12/Frame.lean) at any parts X that are `Like`:
their yes holds the yes of the front, the batching, the fold, the switch and the batching behind it
of Johnson/Desc/K12/Join.lean, and their base case keeps the record and ends the test. Both `proximityTestParts`
(Join.lean) and `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean) are such.
Main names:
  `KeepsK`: what every part keeps: the group's number; the codes; each oracle message with its shape
    (ShapesKeep); each place, and each tree's shape, number and parts (BookKeeps). It is reflexive
    and transitive.
  `bat_st`: the batching leaves `begun S g G`.
  `foldD_state`, `foldJ_keeps`: the fold: the mask enters (or has come) and is spent; a group is
    made.
  `switchE_two`, `switch_keeps`: the switch and the batching behind it, through switchUnfolds
    (Johnson/Desc/K12/Law/SwUnfold.lean) and Did.codes, Did.shapesKeep, Did.bookKeepsB,
    Did.bookKeepsR (Johnson/Desc/K12/Law/SwTies.lean). Its two rounds come out of the frame's "take
    2" and the first case split of switchE: no count of the rounds is assumed.
  `baseJ5_form`, `baseJ5_keeps`: the base case of JoinGuarded.lean in closed form: the masking message
    that the record names is marked as spent, one tree's count of lists rises by one, nothing passes
    and no mask is named; so it keeps the record.
  `baseEW_state`, `spendPlain_keeps`, `readPlain_keeps`, `baseJ_keeps`: the base case of Join.lean.
  `Like`, `like_P5`, `like_joined`, `stages_out`: the parts; by recursion along the stages.
  `OutK`, `k12_out_of`, `k12_out`, `k12_out_joined`: pass = .nothing; mask = none; g stands; the
    codes stand; ShapesKeep; BookKeeps.
Limits: No soundness is claimed, and nothing is said on hiding.
This is a law on what the record is, not on what a yes is worth. Parts that say no to all meet it by
its form. Parts that say yes to all and hand on any record are not Like (their yes does not hold
foldJ's). Parts with a base case that tests nothing but keeps the record are Like.
p.early and p.answers = 1 are spent by the switch alone.
Of the 23 clauses of outOk (Johnson/Desc/K12/Law/OutOk.lean) this file proves seven: pass, mask, g,
codes, old.shape, old.place, old.tree. More are proved in Johnson/Desc/K12/Law/OutK2.lean and
Johnson/Desc/K12/Law/OutK3.lean.
Of `verify-on-bytes` and the library it uses the plain records and pure functions begun,
closeLedgers, stSent, ShapesKeep, BookKeeps, and the lemmas closeLedgers_codes, closeLedgers_shape,
stSent_old (OnBytes/Slice/BlkStLaws.lean), ShapesKeep.refl, ShapesKeep.trans, BookKeeps.refl,
BookKeeps.trans (OnBytes/Slice/BlkSeat.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

/-- What every part of the test keeps of the record. -/
structure KeepsK (t t' : T12) : Prop where
  g : t'.g = t.g
  codes : t'.st.codes = t.st.codes
  shapes : ShapesKeep t.st t'.st
  book : BookKeeps t.book t'.book

theorem KeepsK.refl (t : T12) : KeepsK t t := ⟨rfl, rfl, ShapesKeep.refl _, BookKeeps.refl _⟩

theorem KeepsK.trans {a b c : T12} (h1 : KeepsK a b) (h2 : KeepsK b c) : KeepsK a c :=
  ⟨h2.g.trans h1.g, h2.codes.trans h1.codes, h1.shapes.trans h2.shapes, h1.book.trans h2.book⟩

theorem shapesKeep_of_map (S S' : Statement)
    (h : ∀ i : ℕ, (S'.oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape)) : ShapesKeep S S'
        := by
  intro o x hx
  have h1 := h o
  rw [hx] at h1
  cases hx' : S'.oracles[o]? with
  | none => rw [hx'] at h1; cases h1
  | some x' => rw [hx'] at h1; exact ⟨x', rfl, Option.some.inj h1⟩

theorem begun_keeps (S : Statement) (g : ℕ) (G : Group) :
    (begun S g G).codes = S.codes ∧ ShapesKeep S (begun S g G) :=
  ⟨closeLedgers_codes _ _, shapesKeep_of_map _ _ fun i => closeLedgers_shape _ _ i⟩

theorem stSent_keeps (S : Statement) (sent : Array OracleNotice) : ShapesKeep S (stSent S sent) :=
    by
  intro o x hx
  have ho : o < S.oracles.size := by
    rcases Nat.lt_or_ge o S.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  exact ⟨x, by rw [stSent_old S _ o ho]; exact hx, rfl⟩

/-- What the batching leaves of the statement: the test on the group has begun. -/
theorem bat_st (S S' : Statement) (g : ℕ) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) :
    ∃ G, S.groups[g]? = some G ∧ S' = begun S g G := by
  unfold First.Close.bat at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  obtain ⟨G, lay, a1, _, _, rfl⟩ := beginRunP_ok (got_ok hb)
  exact ⟨G, a1, rfl⟩

/-- What is received keeps the record's public part; the roots rise by the trees laid. -/
theorem recvP_keeps {F : ℕ} {d d1 : _root_.Desc.Plain.DState Unit} {sent : Array OracleNotice}
    {ids : Array ℕ} (h : Ground.recvP F d sent = some (ids, d1)) :
    d1.st.codes = d.st.codes ∧ ShapesKeep d.st d1.st ∧ BookKeeps d.book d1.book := by
  obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok h
  exact ⟨rfl, stSent_keeps _ _, bookSentP_keeps _ _ _ _ _ _⟩

/-- What a yes of the plain fold leaves of the carried record, on any rounds. -/
theorem foldD_state (F : ℕ) (d d' : _root_.Desc.Plain.DState Unit) (Fs : FoldShape)
    (row : GroupRow) (mask : Option ℕ) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (out : SingleRows)
    (h : First.Close.foldD F d Fs row mask es rs = .ok (out, d')) :
    ∃ (id : ℕ) (d1 : _root_.Desc.Plain.DState Unit),
      ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
        Ground.recvP F d #[foldMaskNotice Fs] = some (ids, d1) ∧ ids[0]? = some id)) ∧
      Ground.spendAsMaskP d1 id = some d' := by
  cases es with
  | nil => cases h
  | cons eE eR =>
    cases rs with
    | nil => cases h
    | cons rE rR =>
      rw [First.Close.foldD] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      have h1 : ∃ (id : ℕ) (d1 : _root_.Desc.Plain.DState Unit),
          ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
            Ground.recvP F d #[foldMaskNotice Fs] = some (ids, d1) ∧ ids[0]? = some id)) ∧
          (do
            First.Close.need "K10.maskfits" (Own.foldMaskFits d1.st Fs id)
            First.Close.named (Ground.spendAsMaskL d1.st id)
            let d2 ← First.Close.got "K10.maskfits" (Ground.spendAsMaskP d1 id)
            match ← First.Close.heard "FOLD epsilon" 1 eE rE (d1.roots - d.roots) with
            | ([sum], eps) =>
              First.Close.need "K10.rowfits" (Own.foldRowFits d2.st Fs row)
              let (gamma, claim) ← First.Close.rounds eR rR (maddE sum eps row.target)
              pure (foldOutput d2.st Fs row id eps gamma claim, d2)
            | _ => .error "K10.items") = Except.ok (out, d') := by
        cases mask with
        | some o => exact ⟨o, d, .inl ⟨rfl, rfl⟩, h⟩
        | none =>
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨⟨ids, dd⟩, hr, h⟩ := bind_ok h
          obtain ⟨i0, hi, h⟩ := bind_ok h
          exact ⟨i0, dd, .inr ⟨rfl, ids, got_ok hr, got_ok hi⟩, h⟩
      obtain ⟨id, d1, hcase, h⟩ := h1
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨d2, hsp, h⟩ := bind_ok h
      obtain ⟨⟨xs, eps⟩, _, h⟩ := bind_ok h
      split at h
      · obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨⟨gamma, claim⟩, _, h⟩ := bind_ok h
        cases h
        exact ⟨id, d1, hcase, got_ok hsp⟩
      · cases h

theorem spendP_roots {d d' : _root_.Desc.Plain.DState Unit} {o : ℕ}
    (h : Ground.spendAsMaskP d o = some d') : d'.roots = d.roots := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h
    rfl
  · cases h

/-- What a yes of the fold's part leaves. -/
theorem foldJ_keeps (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    KeepsK t t1 := by
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
    have hs2 : s2.d = { d' with st := Ground.withGroup d'.st n.1 n.2 } := by
      unfold H2K.newGroupE at hy
      cases hg : Ground.newGroupP d' n.1 n.2 with
      | none => simp [hg, H2K.opt, Except.map] at hy
      | some v =>
        simp only [hg, H2K.opt, Except.map] at hy
        cases hy
        unfold Ground.newGroupP at hg
        split at hg
        · cases hg
          rfl
        · cases hg
    obtain ⟨hbk, hsk⟩ := spend_st _ _ _ hsp
    have hcd := H2K.FoldLaw.spend_codes _ _ _ hsp
    have h1 : d1.st.codes = t.st.codes ∧ ShapesKeep t.st d1.st ∧ BookKeeps t.book d1.book := by
      rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
      · exact ⟨rfl, ShapesKeep.refl _, BookKeeps.refl _⟩
      · exact recvP_keeps hr
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show s2.d.st.codes = _
      rw [hs2]
      exact hcd.trans h1.1
    · show ShapesKeep t.st s2.d.st
      rw [hs2]
      exact h1.2.1.trans hsk
    · show BookKeeps t.book s2.d.book
      rw [hs2]
      show BookKeeps t.book d'.book
      rw [hbk]
      exact h1.2.2
  · cases h

theorem switchE_two {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice}
    {w : Bool} {s : H2K.PS} {x : (Switched × E) × H2K.PS}
    (h : H2K.switchE old T gp others w s = .ok x) : ∃ r1 r2 rest, s.rounds = r1 :: r2 :: rest := by
  unfold H2K.switchE at h
  split at h
  · rename_i e₁ e₂ es r₁ r₂ rs he hr
    exact ⟨r₁, r₂, rs, hr⟩
  · cases h

/-- What a yes of the switch's part and of the batching behind it leaves. rs: at most two rounds
(the frame deals "take 2"). -/
theorem switch_keeps (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) : KeepsK t1 t3 := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out, theta⟩, s'⟩, hx, h1'⟩ := bind_ok h1'
    obtain ⟨ht2, _⟩ := back_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out', row, L, th, D, _, _, hd, _, _⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    have hg : t3.g = t1.g := by
      have h2' := h2
      rw [ht2] at h2'
      simp only [behindJ] at h2'
      obtain ⟨x, _, h2'⟩ := bind_ok h2'
      obtain ⟨rfl, _⟩ := back_ok h2'
      rfl
    exact ⟨hg, hd.codes, hd.shapesKeep, hd.bookKeepsB.trans hd.bookKeepsR⟩
  · cases h1'

/-- What a yes of the elder base step leaves: the masking message is spent; the book is what the
reading leaves. -/
theorem baseEW_state (test : First.Base.TestFn) (spend : First.Base.SpendFn)
    (read : First.Base.ReadFn) (P : First.Base.ParB) (s : First.Base.SB) (rounds : List Fmt.RoundView)
    (cols : List First.Base.Col) (out : First.Base.SB × ℕ)
    (h : First.Base.baseEW test spend read P s rounds cols = .ok out) :
    ∃ (star : ℕ) (S1 : Statement) (ids : Array ℕ) (pos : Positions) (o : First.Base.Got),
      s.mask = some star ∧ spend s.st star = some S1 ∧
      read S1 s.book P.firstTree cols ids pos = some o ∧ out.1.st = S1 ∧ out.1.book = o.book := by
  unfold First.Base.baseEW at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨R, _, h⟩ := bind_ok h
    obtain ⟨code, _, h⟩ := bind_ok h
    obtain ⟨zk, _, h⟩ := bind_ok h
    obtain ⟨star, hstar, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨S1, hS1, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      split at h
      · obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨o, ho, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        cases h
        exact ⟨star, S1, _, _, o, optB_ok hstar, optB_ok hS1, optB_ok ho, rfl, rfl⟩
      · obtain ⟨_, hth, _⟩ := bind_ok h
        cases hth
    · obtain ⟨_, hth, _⟩ := bind_ok h
      cases hth
  · cases h

theorem spendPlain_keeps (S S1 : Statement) (o : ℕ) (h : First.Base.spendPlain S o = some S1) :
    S1.codes = S.codes ∧ ShapesKeep S S1 := by
  unfold First.Base.spendPlain at h
  split at h
  · split at h
    · cases h
      refine ⟨rfl, fun o' x hx => ?_⟩
      show ∃ x', (S.oracles.modify o fun x => { x with spentAsMask := true })[o']? = some x' ∧ _
      rw [Array.getElem?_modify, hx]
      by_cases e : o = o'
      · exact ⟨{ x with spentAsMask := true }, by simp [e], rfl⟩
      · exact ⟨x, by simp [e], rfl⟩
    · cases h
  · cases h

theorem openOneB_keeps (S : Statement) (ft : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List First.Base.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : First.Base.openOne S ft pos B0 t s = some s') : BookKeeps s.1 s'.1 := by
  unfold First.Base.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h; exact modify_keeps _ _)
      | cases h
  · cases h

theorem foldlM_keepsO {α σ : Type} (R : σ → σ → Prop) (hr : ∀ s, R s s)
    (ht : ∀ a b c, R a b → R b c → R a c) (f : σ → α → Option σ)
    (hf : ∀ s a s', f s a = some s' → R s s') : ∀ (l : List α) (s s' : σ),
    l.foldlM f s = some s' → R s s'
  | [], s, s', h => by cases h; exact hr s
  | a :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact ht _ _ _ (hf _ _ _ h1) (foldlM_keepsO R hr ht f hf l s1 s' h2)

theorem readPlain_keeps (S : Statement) (B : TreeBook) (ft : ℕ) (cols : List First.Base.Col)
    (ids : Array ℕ) (pos : Positions) (o : First.Base.Got)
    (h : First.Base.readPlain S B ft cols ids pos = some o) : BookKeeps B o.book := by
  unfold First.Base.readPlain at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i B' left' got' hfold
        obtain ⟨opened, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact foldlM_keepsO
          (fun (a b : TreeBook × List First.Base.Col × Array (ℕ × Array ℕ × Array (Array F))) =>
            BookKeeps a.1 b.1) (fun _ => BookKeeps.refl _)
          (fun _ _ _ h1 h2 => h1.trans h2) _
          (fun s a s' hs => openOneB_keeps _ _ _ _ _ _ _ hs) _ _ _ hfold

/-- The variant's base case in closed form: the masking message that the record names is marked as
spent, one tree's count of lists rises by one, nothing passes and no mask is named. -/
theorem baseJ5_form (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    ∃ star a : ℕ, t.mask = some star ∧ star < t.st.oracles.size ∧
      tE = { t with
        st := { t.st with
          oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true } }
        book := { t.book with
          trees := t.book.trees.modify a fun x => { x with lists := x.lists + 1 } }
        pass := .nothing, mask := none } := by
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
    refine ⟨star, a, H2K.Sw.named_ok hs, ?_, rfl⟩
    have hp' := H2K.FoldLaw.need_ok hp
    unfold lastPairOk at hp'
    split at hp'
    · rename_i k z x o e1 e2 e3 e4
      exact (Array.getElem?_eq_some_iff.1 e4).1
    · cases hp'
  · cases h

/-- What a yes of the variant's base case leaves. -/
theorem baseJ5_keeps (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    KeepsK t tE ∧ tE.pass = .nothing ∧ tE.mask = none ∧ tE.roots = t.roots := by
  obtain ⟨star, a, _, _, rfl⟩ := baseJ5_form p j cur cut t tE rs gs h
  refine ⟨⟨rfl, rfl, fun o' x hx => ?_, modify_keeps _ _⟩, rfl, rfl, rfl⟩
  show ∃ x', (t.st.oracles.modify star fun x => { x with spentAsMask := true })[o']? = some x' ∧ _
  rw [Array.getElem?_modify, hx]
  by_cases e : star = o'
  · exact ⟨{ x with spentAsMask := true }, by simp [e], rfl⟩
  · exact ⟨x, by simp [e], rfl⟩

/-! ## The induction along the stages, and the top -/

/-- Parts whose yes holds Join.lean's own parts' yes (front · batching · fold · switch · the
batching behind it), and whose base case keeps the record and ends the test. -/
structure Like (X : Parts T12) (p : P12) : Prop where
  front : ∀ (t t' : T12), (X.front p).decide t [] [] = .ok t' → (frontJ p).decide t [] [] = .ok t'
  bat : ∀ (cut : List Fmt.DeclaredRound) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (X.bat p cut).decide t rs gs = .ok t' → (batJ p cut).decide t rs gs = .ok t'
  fold : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs), (X.fold p j cur cut).decide t rs gs = .ok t' →
    (foldJ p j cur cut).decide t rs gs = .ok t'
  switch : ∀ (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound)
    (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (X.switch p j cur nxt last cut).decide t rs gs = .ok t' →
    (switchJ p j cur nxt last cut).decide t rs gs = .ok t'
  behind : ∀ (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12),
    (X.batBehind p j nxt cut).decide t [] [] = .ok t' → (behindJ p j nxt cut).decide t [] [] = .ok
        t'
  base : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
    (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' →
    KeepsK t t' ∧ t'.pass = .nothing ∧ t'.mask = none

/-- The variant's parts are such. -/
theorem like_P5 (p : P12) : Like guardedProximityTestParts p where
  front := fun _ _ h => (frontK_ok p _ _ _ _ h).1
  bat := fun _ _ _ _ _ h => (batK_ok p _ _ _ _ _ h).1
  fold := fun _ _ _ _ _ _ _ h => (ranged_ok _ _ _ _ _ _ h).1
  switch := fun _ _ _ _ _ _ _ _ _ h => (ranged_ok _ _ _ _ _ _ h).1
  behind := fun _ _ _ _ _ h => h
  base := fun j cur cut t t' rs gs h => by
    obtain ⟨a, b, c, _⟩ := baseJ5_keeps p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1
    exact ⟨a, b, c⟩

/-- The stages keep the record's public part, and end the test. -/
theorem stages_out (X : Parts T12) (p : P12) (hX : Like X p) (he : p.early = true)
    (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
      (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE →
      KeepsK t tE ∧ tE.pass = .nothing ∧ tE.mask = none
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    exact hX.base _ _ _ _ _ _ _ h
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have k1 := foldJ_keeps p j cur _ t t1 _ _ (hX.fold _ _ _ _ _ _ _ f1)
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    have k2 := switch_keeps p he ha j cur nxt rest.isEmpty _ t1 t2 t3 _ _ hlen
      (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    obtain ⟨k3, k4, k5⟩ := stages_out X p hX he ha rest (j + 1) nxt _ t3 tE _ _ f5
    exact ⟨(k1.trans k2).trans k3, k4, k5⟩

/-- What a yes of the test leaves, first part. t0: the record that the test is handed; tE: what its
yes leaves. -/
structure OutK (t0 tE : T12) : Prop where
  /-- Nothing passes, and no mask is named -/
  pass : tE.pass = .nothing
  mask : tE.mask = none
  /-- The number of the group under test stands -/
  g : tE.g = t0.g
  /-- The codes stand -/
  codes : tE.st.codes = t0.st.codes
  /-- Each oracle message that stood, stands, with its shape -/
  shapes : ShapesKeep t0.st tE.st
  /-- Each place stands; each tree that stood keeps its shape, its number and its parts -/
  book : BookKeeps t0.book tE.book

/-- A yes of the test's decision leaves OutK: no premise on the view, none on the plan but the two
numbers. -/
theorem k12_out_of (X : Parts T12) (p : P12) (hX : Like X p) (he : p.early = true)
    (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) : OutK t0 tE := by
  obtain ⟨first, rest, ds, tF, t1, _, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  obtain ⟨c1, c2⟩ := begun_keeps tF.st tF.g G
  obtain ⟨k, k1, k2⟩ := stages_out X p hX he ha rest 0 first _ _ tE _ _ hst
  exact ⟨k1, k2, k.g, k.codes.trans c1, c2.trans k.shapes, k.book⟩

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_out (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    OutK t0 tE := k12_out_of guardedProximityTestParts p (like_P5 p) he ha t0 tE rs gs h

/-- What a yes of Join.lean's own base case leaves. -/
theorem baseJ_keeps (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ p j cur cut).decide t rs gs = .ok tE) :
    KeepsK t tE ∧ tE.pass = .nothing ∧ tE.mask = none ∧ tE.roots = t.roots := by
  simp only [baseJ] at h
  split at h
  · obtain ⟨R, _, h⟩ := bind_ok h
    obtain ⟨s, hs, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.baseE' at hs
    split at hs
    · obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨_, _, hs⟩ := bind_ok hs
      obtain ⟨⟨b, took⟩, h3, hs⟩ := bind_ok hs
      cases hs
      obtain ⟨star, S1, ids, pos, o, _, k2, k3, k4, k5⟩ :=
        baseEW_state _ _ _ _ _ _ _ _ (mapError_ok h3)
      have k4' : b.st = S1 := k4
      have k5' : b.book = o.book := k5
      obtain ⟨c1, c2⟩ := spendPlain_keeps _ _ _ k2
      refine ⟨⟨rfl, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
      · show b.st.codes = _
        rw [k4']
        exact c1
      · show ShapesKeep t.st b.st
        rw [k4']
        exact c2
      · show BookKeeps t.book b.book
        rw [k5']
        exact readPlain_keeps _ _ _ _ _ _ _ k3
    · cases hs
  · cases h

/-- Join.lean's own parts are such. -/
theorem like_joined (p : P12) : Like K12.proximityTestParts p where
  front := fun _ _ h => h
  bat := fun _ _ _ _ _ h => h
  fold := fun _ _ _ _ _ _ _ h => h
  switch := fun _ _ _ _ _ _ _ _ _ h => h
  behind := fun _ _ _ _ _ h => h
  base := fun j cur cut t t' rs gs h => by
    obtain ⟨a, b, c, _⟩ := baseJ_keeps p j cur cut t t' rs gs h
    exact ⟨a, b, c⟩

/-- Of proximityTestKind proximityTestParts p (Join.lean's own parts). -/
theorem k12_out_joined (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind K12.proximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    OutK t0 tE := k12_out_of K12.proximityTestParts p (like_joined p) he ha t0 tE rs gs h

end H2K.Out
