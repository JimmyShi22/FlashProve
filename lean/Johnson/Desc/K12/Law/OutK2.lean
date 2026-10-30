-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OutK2.lean: what the record is that a yes of the decision of the proximity test
(the kind K12) leaves, second part: the statement's groups and oracle messages, counted and marked.

An outright theorem on the text of the block: no premise on the view, and of the place only p.early
= true and p.answers = 1. It stands over Johnson/Desc/K12/Law/OutK.lean (Like, foldD_state,
baseJ5_form, baseEW_state, bat_st) and holds of proximityTestKind X p at parts that are Like and whose base case
leaves `BaseSt`; both `proximityTestParts` and `guardedProximityTestParts` are such. Statements and proofs.
Main names:
  `foldJ_form`, `spendP_form`, `spendP_there`: the fold's part in closed form.
  `closeLedgers_groups`, `closeLedgers_size`, `closeLedgers_other`, `closeLedgers_shut`,
    `withRows_groups_other`, `withRows_groups_size`: what the statement's pure effects leave
    untouched.
  `did_groups`, `did_new`, `did_oracles`: of Did (what a switch and the batching behind it have
    done): every group but the new one stands; the new one is marked and empty; where it had no
    member every older message stands to the letter; the messages sent have come.
  `switch_did`, `maskNo`, `own`, `stage_st`: a stage but the last, whole.
  `BaseSt`, `baseJ5_st`, `baseJ_st`: the base case: the masking message that the record names is
    spent; nothing else of the statement turns. Of JoinGuarded.lean's base case this is read off its
    closed form.
  `StagesSt`, `stages_st`: by recursion along the stages.
  `Shut`, `OutK2`, `k12_out2_of`, `k12_out2`, `k12_out2_joined`: the group under test becomes { G
    with inRun := true, rows := #[] }; every other group that stood is what it was; one group has
    come for each switch, marked and with no open row; two messages have come for each switch, and
    one more where the record named no mask; a message that is neither a member nor the first mask
    is what it was; each member's ledger, if it has one, is shut; the first mask and the second
    message of each switch are marked as spent.
Limits: No soundness is claimed, and nothing is said on hiding.
This is a law on what the record is, not on what a yes is worth: parts with a base case that tests
nothing, but spends the mask and keeps the rest, meet Like and BaseSt.
`own t0` is 1 where the record names no mask (the fold then sends its own). That this is the plan's
ownMask is the clause own of outOk (Johnson/Desc/K12/Law/OutOk.lean), which is proved nowhere.
The clause on the ledgers speaks of a member that is not the first mask. Of a member nothing else is
said than that its ledger is shut.
Of the 23 clauses of outOk this file proves, beside the seven of Johnson/Desc/K12/Law/OutK.lean:
g.begun, g.members, other.groups, groups.n, new.begun, oracles.n, old.rest, g.ledgers, masks.spent;
several in a stronger form (to the letter).
Of the library it uses the pure functions begun, closeLedgers, withRows, withRow, ledgerShut,
withMessageInGroup, admitted, stSent, sentOf, and the lemmas ledgerShut_groups (OnBytes/Slice/BlkCsRun.lean),
withRows_oracles (OnBytes/Slice/BlkCalls.lean), stSent_old (OnBytes/Slice/BlkStLaws.lean).
Johnson/Desc/K12/Law/SwRoots.lean is imported and is spent in Johnson/Desc/K12/Law/OutK3.lean.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.OutK
import Johnson.Desc.K12.Law.SwRoots

set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.FoldLaw (bind_ok got_ok)

/-! ## Closed forms of what a part leaves -/

/-- The fold's part, in closed form: the mask has come or enters (d1); it is spent (d'); a group is
made behind all groups. -/
theorem foldJ_form (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    ∃ (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : ℕ × ℕ) (id : ℕ)
      (d1 d' : _root_.Desc.Plain.DState Unit) (rows : SingleRows),
      t.pass = .claim row L ∧ stageAt p j cur = some c ∧
      ((t.mask = some id ∧ d1 = ⟨t.st, t.book, t.roots, keyed p cut gs, ()⟩) ∨ (t.mask = none ∧ ∃
          ids,
        Ground.recvP p.nums.firstTree ⟨t.st, t.book, t.roots, keyed p cut gs, ()⟩
          #[foldMaskNotice (ioppFoldShape c L)] = some (ids, d1) ∧ ids[0]? = some id)) ∧
      Ground.spendAsMaskP d1 id = some d' ∧
      t1 = { t with st := Ground.withGroup d'.st n.1 n.2, book := d'.book, roots := d'.roots,
                    pass := .single rows d'.st.groups.size, mask := t.mask } := by
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
    refine ⟨row, L, c, n, id, d1, d', rows', e1, e2, hcase, hsp, ?_⟩
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
  · cases h

theorem spendP_form {d d' : _root_.Desc.Plain.DState Unit} {o : ℕ}
    (h : Ground.spendAsMaskP d o = some d') :
    d' = { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
      { x with spentAsMask := true } } } := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h
    rfl
  · cases h

/-! ## What the statement's pure effects leave untouched -/

theorem closeLedgers_groups : ∀ (l : List ℕ) (S : Statement), (closeLedgers S l).groups = S.groups
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_groups l _

theorem closeLedgers_size : ∀ (l : List ℕ) (S : Statement),
    (closeLedgers S l).oracles.size = S.oracles.size
  | [], _ => rfl
  | a :: l, S => by
    show (closeLedgers _ l).oracles.size = _
    rw [closeLedgers_size l]
    simp

/-- Closing ledgers leaves every message that is not listed as it was. -/
theorem closeLedgers_other : ∀ (l : List ℕ) (S : Statement) (o : ℕ), o ∉ l →
    (closeLedgers S l).oracles[o]? = S.oracles[o]?
  | [], _, _, _ => rfl
  | a :: l, S, o, h => by
    show (closeLedgers _ l).oracles[o]? = _
    rw [closeLedgers_other l _ o fun hm => h (List.mem_cons_of_mem _ hm)]
    have hne : a ≠ o := fun e => h (e ▸ List.mem_cons_self)
    simp [Array.getElem?_modify, hne]

theorem withRows_groups_other (g q : ℕ) (hq : q ≠ g) : ∀ (l : List OnBytes.Row) (S : Statement),
    (withRows S g l).groups[q]? = S.groups[q]?
  | [], _ => rfl
  | r :: l, S => by
    show (withRows (withRow S g r) g l).groups[q]? = _
    rw [withRows_groups_other g q hq l]
    simp [withRow, Array.getElem?_modify, hq.symm]

theorem withRows_groups_size (g : ℕ) : ∀ (l : List OnBytes.Row) (S : Statement),
    (withRows S g l).groups.size = S.groups.size
  | [], _ => rfl
  | r :: l, S => by
    show (withRows (withRow S g r) g l).groups.size = _
    rw [withRows_groups_size g l]
    simp [withRow]

section
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S : Statement} {Bk : TreeBook} {roots : ℕ} {S' : Statement}
  {Bk' : TreeBook} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- A switch and the batching behind it leave every group but the new one as it was; no group comes
or goes. -/
theorem did_groups (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    S'.groups.size = S.groups.size ∧ ∀ q, q ≠ gp → S'.groups[q]? = S.groups[q]? := by
  rw [h.st]
  constructor
  · show ((closeLedgers (D.stR T gp others S) _).groups.modify gp _).size = _
    rw [Array.size_modify, closeLedgers_groups]
    unfold Taken.stR Taken.stJ
    rw [withRows_groups_size]
    show ((ledgerShut (D.stA T others S) T S.oracles.size).groups.modify gp _).size = _
    rw [Array.size_modify, ledgerShut_groups]
    rfl
  · intro q hq
    show ((closeLedgers (D.stR T gp others S) _).groups.modify gp _)[q]? = _
    rw [Array.getElem?_modify, if_neg hq.symm, closeLedgers_groups]
    unfold Taken.stR Taken.stJ
    rw [withRows_groups_other gp q hq]
    show ((ledgerShut (D.stA T others S) T S.oracles.size).groups.modify gp _)[q]? = _
    rw [Array.getElem?_modify, if_neg hq.symm, ledgerShut_groups]
    rfl

/-- The new group behind them: marked, with no open row. -/
theorem did_new (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    ∃ G', S'.groups[gp]? = some G' ∧ G'.inRun = true ∧ G'.rows = #[] := by
  have hsz := (did_groups h).1
  have hgp : gp < S.groups.size := by
    have hg := h.group
    rw [ledgerShut_groups] at hg
    have hg' : S.groups[gp]? = some D.G := hg
    rcases Nat.lt_or_ge gp S.groups.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hg'
      cases hg'
  rw [h.st]
  show ∃ G', ((closeLedgers (D.stR T gp others S) _).groups.modify gp _)[gp]? = some G' ∧ _
  rw [Array.getElem?_modify, if_pos rfl]
  have hlt : gp < (closeLedgers (D.stR T gp others S) (D.grown S).members.toList).groups.size := by
    rw [closeLedgers_groups]
    unfold Taken.stR Taken.stJ
    rw [withRows_groups_size]
    show gp < ((ledgerShut (D.stA T others S) T S.oracles.size).groups.modify gp _).size
    rw [Array.size_modify, ledgerShut_groups]
    exact hgp
  rw [Array.getElem?_eq_getElem hlt]
  exact ⟨_, rfl, rfl, rfl⟩

/-- Where the new group had no member, they leave every older message as it was, to the letter; and
the messages sent have come. -/
theorem did_oracles (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (hG : D.G.members = #[]) :
    S'.oracles.size = S.oracles.size + (OnBytes.Slice.sentOf T others).size ∧
      ∀ o, o < S.oracles.size → S'.oracles[o]? = S.oracles[o]? := by
  have hmem : (D.grown S).members.toList = [S.oracles.size] := by
    unfold Taken.grown
    rw [hG]
    simp [Array.insertIdxIfInBounds]
  rw [h.st]
  constructor
  · show (closeLedgers (D.stR T gp others S) _).oracles.size = _
    rw [closeLedgers_size]
    unfold Taken.stR Taken.stJ
    rw [(withRows_oracles gp D.rows _).1]
    show ((ledgerShut (D.stA T others S) T S.oracles.size).oracles.modify _ _).size = _
    rw [Array.size_modify]
    unfold ledgerShut
    split
    · rw [closeLedgers_size]
      simp [Taken.stA, admitted, stSent]
    · simp [Taken.stA, admitted, stSent]
  · intro o ho
    have hne : S.oracles.size ≠ o := by omega
    show (closeLedgers (D.stR T gp others S) _).oracles[o]? = _
    rw [hmem, closeLedgers_other _ _ _ (by simp; omega)]
    unfold Taken.stR Taken.stJ
    rw [(withRows_oracles gp D.rows _).1]
    show ((ledgerShut (D.stA T others S) T S.oracles.size).oracles.modify _ _)[o]? = _
    rw [Array.getElem?_modify, if_neg hne]
    have hA : (D.stA T others S).oracles[o]? = S.oracles[o]? := by
      unfold Taken.stA
      show ((stSent S (OnBytes.Slice.sentOf T others)).oracles.modify _ _)[o]? = _
      rw [Array.getElem?_modify, if_neg hne, stSent_old S _ o ho]
    unfold ledgerShut
    split
    · rw [closeLedgers_other _ _ _ (by simp; omega)]
      exact hA
    · exact hA

end

/-! ## A stage but the last, whole -/

theorem spendP_there {d d' : _root_.Desc.Plain.DState Unit} {o : ℕ}
    (h : Ground.spendAsMaskP d o = some d') : o < d.st.oracles.size := by
  unfold Ground.spendAsMaskP at h
  split at h
  · rename_i hok
    simp only [Ground.ok, Ground.spendAsMaskL, List.all_cons, Bool.and_eq_true] at hok
    have h1 := hok.1
    rcases Nat.lt_or_ge o d.st.oracles.size with h2 | h2
    · exact h2
    · rw [Array.getElem?_eq_none h2] at h1
      cases h1
  · cases h

theorem othersOf_size (last : Bool) (nx : IoppStage) : (othersOf last nx).size = 1 := by
  unfold othersOf
  split <;> rfl

/-- The switch and the batching behind it, through (U). rs: at most two rounds. -/
theorem switch_did (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (hlen : rs.length ≤ 2)
    (h1 : (switchJ p j cur nxt last cut).decide t1 rs gs = .ok t2)
    (h2 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    ∃ (rows : SingleRows) (gp : ℕ) (nx : IoppStage) (out : Switched) (row : GroupRow)
      (L : GroupLayout) (th : E) (D : Taken), t1.pass = .single rows gp ∧
      Did p.nums.firstTree (keyed p cut gs) rows (switchTargetStage nx.code nx.maskCode nx.k nx.h 1)
        gp (othersOf last nx) t1.st t1.book t1.roots t3.st t3.book out row L th D ∧
      t3.mask = out.others[0]? := by
  have h1' := h1
  simp only [switchJ] at h1'
  split at h1'
  · rename_i rows gp nx e1 e2
    obtain ⟨⟨⟨out, theta⟩, s'⟩, hx, h1'⟩ := bind_ok h1'
    obtain ⟨r1, r2, rest, hr⟩ := switchE_two hx
    have hr' : rs = r1 :: r2 :: rest := hr
    have hrest : rest = [] := by
      rw [hr'] at hlen
      simp only [List.length_cons] at hlen
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    subst hr'
    obtain ⟨out', row, L, th, D, _, _, hd, _, hm⟩ :=
      switchUnfolds p j cur nxt last cut t1 t2 t3 r1 r2 gs rows gp nx he ha e1 e2 h1 h2
    exact ⟨rows, gp, nx, out', row, L, th, D, e1, hd, hm⟩
  · cases h1'

/-- The number of the present stage's mask: the record's, or the next message's. -/
def maskNo (t : T12) : ℕ := t.mask.getD t.st.oracles.size

/-- One, where the fold sends its own mask. -/
def own (t : T12) : ℕ := if t.mask.isNone then 1 else 0

/-- What a stage but the last leaves of the statement. t: in front of the fold; t3: behind the
batching behind the switch. -/
theorem stage_st (p : P12) (he : p.early = true) (ha : p.answers = 1) (j : ℕ)
    (cur nxt : Fmt.M1.Stage) (last : Bool) (cutF cutS : List Fmt.DeclaredRound) (t t1 t2 t3 : T12)
    (rsF rsS : List Fmt.RoundView) (gsF gsS : Gs) (hlen : rsS.length ≤ 2)
    (f1 : (foldJ p j cur cutF).decide t rsF gsF = .ok t1)
    (f2 : (switchJ p j cur nxt last cutS).decide t1 rsS gsS = .ok t2)
    (f3 : (behindJ p (j + 1) nxt cutS).decide t2 [] [] = .ok t3) :
    t3.st.groups.size = t.st.groups.size + 1 ∧
    (∀ q, q < t.st.groups.size → t3.st.groups[q]? = t.st.groups[q]?) ∧
    (∃ G', t3.st.groups[t.st.groups.size]? = some G' ∧ G'.inRun = true ∧ G'.rows = #[]) ∧
    t3.st.oracles.size = t.st.oracles.size + own t + 2 ∧
    (∀ o, o < t.st.oracles.size → t.mask ≠ some o → t3.st.oracles[o]? = t.st.oracles[o]?) ∧
    maskNo t < t.st.oracles.size + own t ∧
    (∃ x, t3.st.oracles[maskNo t]? = some x ∧ x.spentAsMask = true) ∧
    t3.mask = some (t.st.oracles.size + own t + 1) := by
  obtain ⟨row, L, c, n, id, d1, d', rows, _, _, hcase, hsp, rfl⟩ := foldJ_form p j cur cutF t t1 rsF
      gsF f1
  obtain ⟨rows', gp, nx, out, row', L', th, D, hp, hd, hm⟩ :=
    switch_did p he ha j cur nxt last cutS _ t2 t3 rsS gsS hlen f2 f3
  obtain ⟨rfl, rfl⟩ : rows = rows' ∧ d'.st.groups.size = gp := by
    cases hp
    exact ⟨rfl, rfl⟩
  have hthere := spendP_there hsp
  have hd' := spendP_form hsp
  -- The statement behind the mask's entering
  have h1 : d1.st.groups = t.st.groups ∧ d1.st.oracles.size = t.st.oracles.size + own t ∧
      id = maskNo t ∧ (∀ o, o < t.st.oracles.size → d1.st.oracles[o]? = t.st.oracles[o]?) ∧
      (t.mask ≠ some id → t.st.oracles.size ≤ id) := by
    rcases hcase with ⟨hmk, rfl⟩ | ⟨hmk, ids, hr, hi⟩
    · refine ⟨rfl, ?_, ?_, fun _ _ => rfl, fun hne => absurd hmk hne⟩
      · simp [own, hmk]
      · simp [maskNo, hmk]
    · obtain ⟨lay, _, _, rfl, rfl⟩ := recvP_ok hr
      have hid : id = t.st.oracles.size := by
        simp at hi
        omega
      refine ⟨rfl, ?_, ?_, fun o ho => stSent_old _ _ o ho, fun _ => by omega⟩
      · simp [own, hmk, stSent]
      · simp [maskNo, hmk, hid]
  obtain ⟨g1, g2, g3, g4, g5⟩ := h1
  have hgr : d'.st.groups = t.st.groups := by rw [hd']; exact g1
  have hosz : d'.st.oracles.size = t.st.oracles.size + own t := by
    rw [hd']
    show (d1.st.oracles.modify id _).size = _
    rw [Array.size_modify, g2]
  -- The new group had no member
  have hG : D.G.members = #[] := by
    have hg := hd.group
    rw [ledgerShut_groups] at hg
    have hg' : (d'.st.groups.push { code := n.1, maskCode := n.2 })[d'.st.groups.size]? = some D.G
        := hg
    rw [Array.getElem?_push_size] at hg'
    rw [← Option.some.inj hg']
  obtain ⟨a1, a2⟩ := did_groups hd
  obtain ⟨G', b1, b2, b3⟩ := did_new hd
  obtain ⟨c1, c2⟩ := did_oracles hd hG
  have hS : (Ground.withGroup d'.st n.1 n.2).oracles = d'.st.oracles := rfl
  have hSg : (Ground.withGroup d'.st n.1 n.2).groups = d'.st.groups.push { code := n.1, maskCode :=
      n.2 } := rfl
  dsimp only at a1 a2 b1 c1 c2
  rw [hS] at c1 c2
  rw [hSg] at a1 a2
  have hsent : (OnBytes.Slice.sentOf (switchTargetStage nx.code nx.maskCode nx.k nx.h 1) (othersOf
      last nx)).size = 2 := by
    unfold Slice.sentOf
    rw [Array.size_append, othersOf_size]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, Array.size_push, hgr]
  · intro q hq
    have hq' : q < d'.st.groups.size := by rw [hgr]; exact hq
    rw [a2 q (by omega), Array.getElem?_push_lt hq', ← Array.getElem?_eq_getElem hq', hgr]
  · rw [← hgr]
    exact ⟨G', b1, b2, b3⟩
  · rw [c1, hosz, hsent]
  · intro o ho hne
    rw [c2 o (by rw [hosz]; omega), hd']
    show (d1.st.oracles.modify id _)[o]? = _
    have hio : id ≠ o := by
      intro e
      subst e
      have := g5 hne
      omega
    rw [Array.getElem?_modify, if_neg hio, g4 o ho]
  · rw [← g3, ← g2]
    exact hthere
  · rw [← g3, c2 id (by rw [hosz, ← g2]; exact hthere), hd']
    show ∃ x, (d1.st.oracles.modify id _)[id]? = some x ∧ _
    rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_eq_getElem hthere]
    exact ⟨_, rfl, rfl⟩
  · rw [hm, hd.riders, othersOf_size]
    show ((Array.range 1).map (· + (d'.st.oracles.size + 1)))[0]? = _
    rw [hosz]
    simp

/-! ## The base case, the induction, the top -/

theorem spendPlain_form (S S1 : Statement) (o : ℕ) (h : First.Base.spendPlain S o = some S1) :
    o < S.oracles.size ∧
      S1 = { S with oracles := S.oracles.modify o fun x => { x with spentAsMask := true } } := by
  unfold First.Base.spendPlain at h
  split at h
  · rename_i x hx
    split at h
    · cases h
      refine ⟨?_, rfl⟩
      rcases Nat.lt_or_ge o S.oracles.size with h2 | h2
      · exact h2
      · rw [Array.getElem?_eq_none h2] at hx
        cases hx
    · cases h
  · cases h

/-- What the base case leaves of the statement: the masking message, which the record names, is
spent; nothing else turns. -/
def BaseSt (t tE : T12) : Prop :=
  ∃ star, t.mask = some star ∧ star < t.st.oracles.size ∧
    tE.st = { t.st with oracles := t.st.oracles.modify star fun x => { x with spentAsMask := true }
        }

theorem baseJ5_st (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) :
    BaseSt t tE := by
  obtain ⟨star, a, h1, h2, rfl⟩ := baseJ5_form p j cur cut t tE rs gs h
  exact ⟨star, h1, h2, rfl⟩

theorem baseJ_st (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (baseJ p j cur cut).decide t rs gs = .ok tE) :
    BaseSt t tE := by
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
      obtain ⟨star, S1, ids, pos, o, k1, k2, _, k4, _⟩ :=
        baseEW_state _ _ _ _ _ _ _ _ (mapError_ok h3)
      obtain ⟨c1, c2⟩ := spendPlain_form _ _ _ k2
      have k4' : b.st = S1 := k4
      exact ⟨star, k1, c1, k4'.trans c2⟩
    · cases hs
  · cases h

/-- What the stages from a stage on leave of the statement. n: how many stages lie behind the
present one. -/
structure StagesSt (t tE : T12) (n : ℕ) : Prop where
  groupsN : tE.st.groups.size = t.st.groups.size + n
  groupsOld : ∀ q, q < t.st.groups.size → tE.st.groups[q]? = t.st.groups[q]?
  groupsNew : ∀ q, t.st.groups.size ≤ q → q < t.st.groups.size + n →
    ∃ G', tE.st.groups[q]? = some G' ∧ G'.inRun = true ∧ G'.rows = #[]
  oraclesN : tE.st.oracles.size = t.st.oracles.size + own t + 2 * n
  oraclesOld : ∀ o, o < t.st.oracles.size → t.mask ≠ some o → tE.st.oracles[o]? = t.st.oracles[o]?
  maskSpent : ∃ x, tE.st.oracles[maskNo t]? = some x ∧ x.spentAsMask = true
  masksSpent : ∀ i, i < n →
    ∃ x, tE.st.oracles[t.st.oracles.size + own t + 2 * i + 1]? = some x ∧ x.spentAsMask = true

/-- By recursion along the stages. hB: the base case of X leaves BaseSt. -/
theorem stages_st (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (he : p.early = true) (ha : p.answers = 1) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
      (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (stagesFrom X p j cur rest l : Blk').decide t rs gs = .ok tE → StagesSt t tE rest.length
  | [], j, cur, l, t, tE, rs, gs, h => by
    rw [stagesFrom_last] at h
    obtain ⟨star, h1, h2, h3⟩ := hB _ _ _ _ _ _ _ h
    have hown : own t = 0 := by simp [own, h1]
    have hno : maskNo t = star := by simp [maskNo, h1]
    refine ⟨by rw [h3]; rfl, fun q _ => by rw [h3], fun q a b => by simp at b; omega, ?_, ?_, ?_,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rw [h3, hown]
      simp
    · intro o _ hne
      rw [h3]
      show (t.st.oracles.modify star _)[o]? = _
      rw [Array.getElem?_modify, if_neg fun e => hne (by rw [h1, e])]
    · rw [hno, h3]
      show ∃ x, (t.st.oracles.modify star _)[star]? = some x ∧ _
      rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_eq_getElem h2]
      exact ⟨_, rfl, rfl⟩
  | nxt :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨t1, t2, t3, f1, f2, f3, _, f5⟩ := (stagesFrom_ok X p j cur nxt rest l t tE rs gs).1 h
    have hlen : ((rs.drop (foldAt X p j cur l : Blk').rounds.length).take
        (switchAt X p j cur nxt rest.isEmpty l : Blk').rounds.length).length ≤ 2 := by
      refine (List.length_take_le _ _).trans ?_
      show (((l.drop (1 + cur.k)).take 2).map (·.1)).length ≤ 2
      rw [List.length_map]
      exact List.length_take_le _ _
    obtain ⟨a1, a2, ⟨G', a3, a3', a3''⟩, a4, a5, a6, ⟨xm, a7, a7'⟩, a8⟩ :=
      stage_st p he ha j cur nxt rest.isEmpty _ _ t t1 t2 t3 _ _ _ _ hlen
        (hX.fold _ _ _ _ _ _ _ f1) (hX.switch _ _ _ _ _ _ _ _ _ f2) (hX.behind _ _ _ _ _ f3)
    have ih := stages_st X p hX hB he ha rest (j + 1) nxt _ t3 tE _ _ f5
    have hown3 : own t3 = 0 := by simp [own, a8]
    have hno3 : maskNo t3 = t.st.oracles.size + own t + 1 := by simp [maskNo, a8]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ih.groupsN, a1, List.length_cons]
      omega
    · intro q hq
      rw [ih.groupsOld q (by omega), a2 q hq]
    · intro q h1 h2
      rw [List.length_cons] at h2
      by_cases e : q = t.st.groups.size
      · subst e
        rw [ih.groupsOld _ (by omega)]
        exact ⟨G', a3, a3', a3''⟩
      · exact ih.groupsNew q (by omega) (by omega)
    · rw [ih.oraclesN, a4, hown3, List.length_cons]
      omega
    · intro o ho hne
      rw [ih.oraclesOld o (by omega) (by rw [a8]; intro e; have := Option.some.inj e; omega), a5 o
          ho hne]
    · rw [ih.oraclesOld _ (by omega) (by rw [a8]; intro e; have := Option.some.inj e; omega)]
      exact ⟨xm, a7, a7'⟩
    · intro i hi
      rw [List.length_cons] at hi
      cases i with
      | zero =>
        have := ih.maskSpent
        rw [hno3] at this
        exact this
      | succ i =>
        have := ih.masksSpent i (by omega)
        rw [a4, hown3] at this
        rw [show t.st.oracles.size + own t + 2 * (i + 1) + 1 =
          t.st.oracles.size + own t + 2 + 0 + 2 * i + 1 by omega]
        exact this

/-- A message's ledger, if it has one, is shut. -/
def Shut (x : OnBytes.Oracle) : Prop := ∀ led, x.ledger = some led → led.closed = true

/-- Behind the closing of the listed messages' ledgers: a listed message's ledger is shut; one that
was shut stays shut. -/
theorem closeLedgers_shut : ∀ (l : List ℕ) (S : Statement) (o : ℕ) (x' : OnBytes.Oracle),
    (closeLedgers S l).oracles[o]? = some x' →
    (o ∈ l ∨ ∃ x, S.oracles[o]? = some x ∧ Shut x) → Shut x'
  | [], S, o, x', h, hc => by
    rcases hc with hc | ⟨x, hx, hs⟩
    · cases hc
    · have h' : S.oracles[o]? = some x' := h
      rw [hx] at h'
      cases h'
      exact hs
  | a :: l, S, o, x', h, hc => by
    have h' : (closeLedgers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } l).oracles[o]?
        = some x' := h
    refine closeLedgers_shut l _ o x' h' ?_
    by_cases hol : o ∈ l
    · exact .inl hol
    · right
      show ∃ x, (S.oracles.modify a _)[o]? = some x ∧ Shut x
      rw [Array.getElem?_modify]
      by_cases e : a = o
      · subst e
        rw [if_pos rfl]
        have hsome : ∃ x, S.oracles[a]? = some x := by
          cases hx : S.oracles[a]? with
          | some x => exact ⟨x, rfl⟩
          | none =>
            have h2 := closeLedgers_other l { S with oracles := S.oracles.modify a fun x =>
              { x with ledger := x.ledger.map fun l => { l with closed := true } } } a hol
            rw [h'] at h2
            have h3 : (S.oracles.modify a fun x =>
              { x with ledger := x.ledger.map fun l => { l with closed := true } })[a]? = some x' :=
              h2.symm
            rw [Array.getElem?_modify, if_pos rfl, hx] at h3
            cases h3
        obtain ⟨x, hx⟩ := hsome
        rw [hx]
        refine ⟨_, rfl, fun led hl => ?_⟩
        obtain ⟨l0, _, rfl⟩ := Option.map_eq_some_iff.1 hl
        rfl
      · rw [if_neg e]
        rcases hc with hc | hc
        · rcases List.mem_cons.1 hc with rfl | hc
          · exact absurd rfl e
          · exact absurd hc hol
        · exact hc

/-- What a yes of the test leaves, second part: the statement. t0: the record that the test is
handed; tE: what its yes leaves; n: the switches (the stages less one). G: the group under test as
it stood. -/
structure OutK2 (t0 tE : T12) (n : ℕ) (G : Group) : Prop where
  /-- The group under test was there -/
  was : t0.st.groups[t0.g]? = some G
  /-- It is marked, holds no open row, and is else as it was (its codes, members, kept marks) -/
  begunG : tE.st.groups[t0.g]? = some { G with inRun := true, rows := #[] }
  /-- Every other group that stood, stands, to the letter -/
  others : ∀ q, q < t0.st.groups.size → q ≠ t0.g → tE.st.groups[q]? = t0.st.groups[q]?
  /-- One group has come for each switch; each is marked and holds no open row -/
  groupsN : tE.st.groups.size = t0.st.groups.size + n
  groupsNew : ∀ q, t0.st.groups.size ≤ q → q < t0.st.groups.size + n →
    ∃ G', tE.st.groups[q]? = some G' ∧ G'.inRun = true ∧ G'.rows = #[]
  /-- Two messages have come for each switch, and one more where the first fold sends its own mask
  -/
  oraclesN : tE.st.oracles.size = t0.st.oracles.size + own t0 + 2 * n
  /-- A message that is neither a member of the group nor the first mask stands, to the letter -/
  rest : ∀ o, o < t0.st.oracles.size → o ∉ G.members.toList → t0.mask ≠ some o →
    tE.st.oracles[o]? = t0.st.oracles[o]?
  /-- Each member's ledger, if it has one, is shut (a member that is not the first mask) -/
  ledgers : ∀ o x, o ∈ G.members.toList → o < t0.st.oracles.size → t0.mask ≠ some o →
    tE.st.oracles[o]? = some x → Shut x
  /-- The first mask, and the second message of each switch, are marked as spent -/
  maskSpent : ∃ x, tE.st.oracles[maskNo t0]? = some x ∧ x.spentAsMask = true
  masksSpent : ∀ i, i < n →
    ∃ x, tE.st.oracles[t0.st.oracles.size + own t0 + 2 * i + 1]? = some x ∧ x.spentAsMask = true

/-- A yes of the test's decision leaves OutK2. -/
theorem k12_out2_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) :
    ∃ G, OutK2 t0 tE (p.nums.stages.length - 1) G := by
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
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
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have k := stages_st X p hX hB he ha rest 0 first _ _ tE _ _ hst
  have hn : p.nums.stages.length - 1 = rest.length := by rw [hs]; simp
  rw [hn]
  have hg : tF.g < tF.st.groups.size := by
    rcases Nat.lt_or_ge tF.g tF.st.groups.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hG
      cases hG
  have gsz : (begun tF.st tF.g G).groups.size = tF.st.groups.size := by
    show ((closeLedgers tF.st _).groups.modify _ _).size = _
    rw [Array.size_modify, closeLedgers_groups]
  have osz : (begun tF.st tF.g G).oracles.size = tF.st.oracles.size := closeLedgers_size _ _
  have hown : own { tF with st := begun tF.st tF.g G, pass := .claim row L } = own tF := rfl
  have hno : maskNo { tF with st := begun tF.st tF.g G, pass := .claim row L } = maskNo tF := by
    unfold maskNo
    show tF.mask.getD (begun tF.st tF.g G).oracles.size = _
    rw [osz]
  have k1 := k.groupsN
  have k2 := k.groupsOld
  have k3 := k.groupsNew
  have k4 := k.oraclesN
  have k5 := k.oraclesOld
  have k6 := k.maskSpent
  have k7 := k.masksSpent
  dsimp only at k1 k2 k3 k4 k5 k7
  rw [gsz] at k1 k2 k3
  rw [osz, hown] at k4 k7
  rw [osz] at k5
  rw [hno] at k6
  refine ⟨G, hG, ?_, ?_, k1, k3, k4, ?_, ?_, k6, k7⟩
  · rw [k2 _ hg]
    show ((closeLedgers tF.st _).groups.modify tF.g _)[tF.g]? = _
    rw [Array.getElem?_modify, if_pos rfl, closeLedgers_groups, hG]
    rfl
  · intro q hq hne
    rw [k2 q hq]
    show ((closeLedgers tF.st _).groups.modify tF.g _)[q]? = _
    rw [Array.getElem?_modify, if_neg hne.symm, closeLedgers_groups]
  · intro o ho hmem hmk
    rw [k5 o ho hmk]
    exact closeLedgers_other _ _ _ hmem
  · intro o x hmem ho hmk hx
    rw [k5 o ho hmk] at hx
    exact closeLedgers_shut _ _ _ _ hx (.inl hmem)

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_out2 (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ G, OutK2 t0 tE (p.nums.stages.length - 1) G :=
  k12_out2_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha t0 tE rs gs h

/-- Of proximityTestKind proximityTestParts p (Join.lean's own parts). -/
theorem k12_out2_joined (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind K12.proximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ G, OutK2 t0 tE (p.nums.stages.length - 1) G :=
  k12_out2_of K12.proximityTestParts p (like_joined p) (fun j cur cut t t' rs gs h => baseJ_st p j cur cut t t'
                  rs gs h)
    he ha t0 tE rs gs h

end H2K.Out
