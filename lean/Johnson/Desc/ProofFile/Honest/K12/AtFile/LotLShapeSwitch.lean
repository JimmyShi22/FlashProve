-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeSwitch.lean

It states no goal. No property of the protocol is claimed.

WHAT A CODE SWITCH WITHOUT KEPT MEMBERS LAYS, READ OFF THE
LIBRARY's OWN UPDATE ON SHAPES (`switchEU`, Johnson/Desc/First/Shape/Switch.lean): where the update returns, at a sending
of two messages (the carrier, sampled; a mask, not sampled) that sit in one new tree, and at a group that is fresh: the
group, the two messages, the tree and the two places behind it, each as a whole record, and the lists' lengths.
General laws on shapes: no state, no file, no size.

  `modAt_ne`, `modAt_len`, `modAt_behind`   a change of one entry: the others; the length; behind a front
  `recvS_two`        the receiving of two messages in one new tree
  `sendPS_two`       the sending: the carrier is admitted, the mask is not
  `counted_apart`    the book behind the reading of the old rows: a tree that holds none of them is as it was
  `swRowsS_kinds`    the rows that such a switch lays: one plain row, then generator rows alone
  `switchEU_lays`    THE LAW

IMPORTS OF Johnson.Top.H0.*: none by name; Johnson.Desc.First.Shape.Switch imports Johnson.Top.H0.Tw.K2C.Closed and
Johnson.Top.H0.Tw.K2C.SendsOpen.

Hypotheses of `switchEU_lays`, by name. noKept: the target has no kept member. noMaskRows: the carrier has no mask row (so
no ledger is shut). sampled, unsampled: the carrier counts an answer, the mask none. layout, oneTree, …: the two sit in
one new tree, at parts 0 and 1. fresh: the group has no member, mark or row and its test has not begun. oldApart: none
of the carried rows' messages is placed in the new tree.

Limits. THE UPDATE ALONE: that a decision says yes where the update returns is not said. HOW MANY generator rows are laid
stands under ∃ (it is the number of drawn positions times one more than the old rows' masks: not said here). Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.First.Shape.Switch
import Johnson.Desc.Ground.Shape.Claims
import Johnson.Desc.K14.Shape.Pieces
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open OnBytes (OracleNotice OracleShape TreeShape TreeLay SwitchTarget RowKind noId)
open VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (CoreSh StSh BookSh GrpSh OrcSh TreeSh SrcSh modAt modAt_at modAt_get
  freshOrc recvS admitS joinS addRowsS countB treesSentS placesS)
open VerifiableInference.Desc.First.Shape (sendPS loopS todoL pairsL behindU switchEU readBookS oldOraclesS onSt
  joinsSt SingleSh FormsSh RowMk mapM_all swRowsS swFrameS swCarriedS swOldSamplesS gensS switchKeptS)
open VerifiableInference.Desc.First.K2 (P2)
open _root_.Desc.K14.Shape (joinS_up addRowsS_up joinUp rowsUp)

/-! ## A change of one entry -/

theorem modAt_ne {α : Type} (l : List α) (i j : ℕ) (f : α → α) (h : j ≠ i) :
    (modAt l i f)[j]? = l[j]? := by
  rw [modAt_at]
  cases l[j]? with
  | none => rfl
  | some x => simp [h]

theorem modAt_len {α : Type} (l : List α) (i : ℕ) (f : α → α) : (modAt l i f).length = l.length := by
  simp [modAt]

/-- A change behind a front leaves the front. -/
theorem modAt_behind {α : Type} (l r : List α) (i : ℕ) (f : α → α) :
    modAt (l ++ r) (l.length + i) f = l ++ modAt r i f := by
  apply List.ext_getElem?
  intro j
  rw [modAt_at]
  by_cases h : j < l.length
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
    cases l[j]? with
    | none => rfl
    | some x =>
      have e : j ≠ l.length + i := by omega
      simp [e]
  · have h' : l.length ≤ j := Nat.le_of_not_lt h
    rw [List.getElem?_append_right h', List.getElem?_append_right h', modAt_at]
    cases r[j - l.length]? with
    | none => rfl
    | some x =>
      by_cases e : j = l.length + i
      · simp [e]
      · have e' : j - l.length ≠ i := by omega
        simp [e, e']

/-! ## The receiving and the sending of two messages in one new tree -/

section
variable {ft : ℕ} {a c : CoreSh} {n₀ n₁ : OracleNotice} {ids : Array ℕ} {lay : TreeLay} {τ : TreeShape}

/-- **The receiving of two messages in one new tree.** -/
theorem recvS_two (h : recvS ft a #[n₀, n₁] = some (ids, c))
    (layout : Own.treesMade a.st.codes #[n₀, n₁] = some lay) (oneTree : lay.shapes = #[τ])
    (tree₀ : lay.tree.getD 0 0 = 0) (tree₁ : lay.tree.getD 1 0 = 0) (part₀ : lay.part.getD 0 0 = 0)
    (part₁ : lay.part.getD 1 0 = 1) :
    ids = #[a.st.oracles.length, a.st.oracles.length + 1] ∧ c.st.codes = a.st.codes ∧
      c.st.groups = a.st.groups ∧
      c.st.oracles = a.st.oracles ++ [freshOrc n₀, freshOrc n₁] ∧
      c.book.trees = a.book.trees ++ [⟨τ, ft + a.roots, .own a.roots,
        [a.st.oracles.length, a.st.oracles.length + 1],
        (n₀.shape.answers == 0) || (n₁.shape.answers == 0), 0⟩] ∧
      c.book.place = a.book.place ++ [(a.book.trees.length, 0), (a.book.trees.length, 1)] ∧
      c.roots = a.roots + 1 ∧ a.st.oracles.length = a.book.place.length := by
  unfold recvS at h
  split at h
  · rename_i hg
    rw [layout] at h
    obtain ⟨e₁, e₂⟩ := Prod.mk.inj (Option.some.inj h)
    have hlen : a.st.oracles.length = a.book.place.length := by
      unfold VerifiableInference.Desc.Ground.Sh.recvG at hg
      rw [Bool.and_eq_true] at hg
      exact beq_iff_eq.1 hg.2
    subst e₂
    refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_, hlen⟩
    · rw [← e₁]
      show (Array.range 2).map (· + a.st.oracles.length) = _
      rw [show Array.range 2 = #[0, 1] from rfl]
      simp [Nat.add_comm]
    · have r2 : List.range (#[n₀, n₁] : Array OracleNotice).size = [0, 1] := rfl
      have ts : treesSentS ft (#[τ] : Array TreeShape).toList a.roots a.book.trees =
          a.book.trees ++ [⟨τ, ft + a.roots, .own a.roots, [], false, 0⟩] := rfl
      dsimp only
      rw [r2, oneTree, ts]
      simp only [List.foldl_cons, List.foldl_nil, tree₀, tree₁]
      rw [modAt_behind, modAt_behind]
      simp [modAt]
    · show a.book.place ++ (List.range 2).map (fun i =>
        (a.book.trees.length + lay.tree.getD i 0, lay.part.getD i 0)) = _
      rw [show List.range 2 = [0, 1] from rfl]
      show a.book.place ++ [(a.book.trees.length + lay.tree.getD 0 0, lay.part.getD 0 0),
        (a.book.trees.length + lay.tree.getD 1 0, lay.part.getD 1 0)] = _
      rw [tree₀, tree₁, part₀, part₁]
      rfl
    · show a.roots + lay.shapes.size = _
      rw [oneTree]
      rfl
  · cases h

/-- **The sending: the carrier is admitted, the mask is not.** -/
theorem sendPS_two (h : sendPS ft #[n₀, n₁] a = some (ids, c))
    (layout : Own.treesMade a.st.codes #[n₀, n₁] = some lay) (oneTree : lay.shapes = #[τ])
    (tree₀ : lay.tree.getD 0 0 = 0) (tree₁ : lay.tree.getD 1 0 = 0) (part₀ : lay.part.getD 0 0 = 0)
    (part₁ : lay.part.getD 1 0 = 1) (sampled : n₀.shape.answers ≠ 0)
    (unsampled : n₁.shape.answers = 0) :
    ∃ places, Own.padMade a.st.codes n₀.shape = some places ∧
      ids = #[a.st.oracles.length, a.st.oracles.length + 1] ∧ c.st.codes = a.st.codes ∧
      c.st.groups = a.st.groups ∧
      c.st.oracles = a.st.oracles ++ [⟨n₀.shape, true, n₀.shape.answers,
        places.map fun p => (p.part, p.index), [],
        OnBytes.Slice.freshLedger a.st.codes n₀.shape, false⟩, freshOrc n₁] ∧
      c.book.trees = a.book.trees ++ [⟨τ, ft + a.roots, .own a.roots,
        [a.st.oracles.length, a.st.oracles.length + 1], true, 0⟩] ∧
      c.book.place = a.book.place ++ [(a.book.trees.length, 0), (a.book.trees.length, 1)] ∧
      c.roots = a.roots + 1 ∧ a.st.oracles.length = a.book.place.length := by
  unfold sendPS at h
  obtain ⟨⟨ids', c₁⟩, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c₂, hl, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨e₀, e₁⟩ := Prod.mk.inj e
  have e₀' : ids' = ids := e₀
  subst e₀' e₁
  obtain ⟨hi, hc, hg, ho, ht, hp, hro, hlen⟩ := recvS_two hr layout oneTree tree₀ tree₁ part₀ part₁
  have g₀ : c₁.st.oracles[a.st.oracles.length]? = some (freshOrc n₀) := by
    rw [ho]
    simp
  have g₁ : c₁.st.oracles[a.st.oracles.length + 1]? = some (freshOrc n₁) := by
    rw [ho]
    simp
  have htodo : todoL c₁ ids' = [a.st.oracles.length] := by
    have hs : (n₀.shape.answers != 0) = true := by simpa using sampled
    unfold todoL
    rw [hi]
    simp [List.filter, g₀, g₁, freshOrc, hs, unsampled]
  have hpairs : pairsL c₁ (todoL c₁ ids') = [(a.st.oracles.length, n₀.shape)] := by
    rw [htodo]
    unfold pairsL
    simp [g₀, freshOrc]
  dsimp only at hl
  rw [hpairs] at hl
  obtain ⟨c₃, hl', e₃⟩ := Option.bind_eq_some_iff.1
    (show (admitS c₁ a.st.oracles.length n₀.shape.answers).bind (loopS []) = some c₂ from hl)
  obtain rfl : c₃ = c₂ := Option.some.inj e₃
  unfold admitS at hl'
  split at hl'
  · rw [g₀] at hl'
    obtain ⟨places, hpl, e⟩ := Option.map_eq_some_iff.1
      (show (Own.padMade c₁.st.codes (freshOrc n₀).shape).map _ = some c₃ from hl')
    subst e
    refine ⟨places, by rw [← hc]; exact hpl, hi, hc, hg, ?_, ?_, hp, hro, hlen⟩
    · dsimp only
      rw [ho, show a.st.oracles.length = a.st.oracles.length + 0 from rfl, modAt_behind, hc]
      simp [modAt, freshOrc]
    · show c₁.book.trees = _
      rw [ht]
      simp [unsampled]
  · cases hl'

end

/-! ## The book behind the reading of the old rows -/

theorem foldl_countB (l : List ℕ) : ∀ b : BookSh,
    (l.foldl countB b).place = b.place ∧ (l.foldl countB b).trees.length = b.trees.length ∧
      ∀ t, t ∉ l → (l.foldl countB b).trees[t]? = b.trees[t]? := by
  induction l with
  | nil => exact fun b => ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons x l ih =>
    intro b
    obtain ⟨h₁, h₂, h₃⟩ := ih (countB b x)
    refine ⟨h₁, h₂.trans (by unfold countB; dsimp only; exact modAt_len _ _ _),
      fun t ht => ?_⟩
    rw [List.mem_cons, not_or] at ht
    exact (h₃ t ht.2).trans (by unfold countB; dsimp only; exact modAt_ne _ _ _ _ ht.1)

/-- **A tree that holds none of the old rows' messages is as it was.** -/
theorem counted_apart {old : SingleSh} {b B : BookSh} (h : readBookS old b = some B) (t : ℕ)
    (apart : ∀ o ∈ (oldOraclesS old).toList, ∀ q, b.place[o]? = some q → q.1 ≠ t) :
    B.place = b.place ∧ B.trees.length = b.trees.length ∧ B.trees[t]? = b.trees[t]? := by
  unfold readBookS at h
  obtain ⟨ps, hps, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨h₁, h₂, h₃⟩ := foldl_countB (Fmt.listOf (ps.map (·.1))) b
  refine ⟨h₁, h₂, h₃ t fun ht => ?_⟩
  obtain ⟨q, hq, e⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 ht)
  obtain ⟨o, ho, hf⟩ := (mapM_all _ _ _ hps).2 q hq
  exact apart o ho q hf e

/-! ## The kinds of the rows that a switch without kept members lays -/

/-- Where no new number stands for a kept member, the switch's frame has no kept member. -/
theorem swFrameS_no_kept {a : StSh} {old : SingleSh} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
    {W : OnBytes.SwitchFrame} (h : swFrameS a old T g anew = some W) (h0 : anew.size = 0) :
    W.kept = [] := by
  unfold swFrameS at h
  obtain ⟨code, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨zk, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨newCode, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i hs
    have hs' : (switchKeptS old).size = 0 := by
      rw [← beq_iff_eq.1 hs]
      exact h0
    rw [← Option.some.inj h]
    dsimp only
    rw [hs']
    rfl
  · cases h

theorem foldlM_none_kind {α : Type} (f : RowMk → α → Option RowMk) (hf : ∀ r x, f r x = none) :
    ∀ (l : List α) (r b : RowMk), l.foldlM f r = some b → b = r
  | [], r, b, h => (Option.some.inj h).symm
  | x :: l, r, b, h => by
    rw [List.foldlM_cons, hf] at h
    cases h

theorem foldl_kind {α : Type} (f : RowMk → α → RowMk) (hf : ∀ r x, (f r x).kind = r.kind) :
    ∀ (l : List α) (r : RowMk), (l.foldl f r).kind = r.kind
  | [], _ => rfl
  | x :: l, r => (foldl_kind f hf l (f r x)).trans (hf r x)

/-- **The kinds: one plain row, then generator rows alone.** -/
theorem swRowsS_kinds {a : StSh} {F : FormsSh} {old : SingleSh} {T : SwitchTarget} {g draws : ℕ}
    {anew : Array ℕ} {rows : List RowMk} (h : swRowsS a F old T g anew draws = some rows)
    (h0 : anew.size = 0) :
    ∃ n, rows.map (·.kind) = .plain :: List.replicate n .generator := by
  unfold swRowsS at h
  obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨carried, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨samples, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  have hk := swFrameS_no_kept hW h0
  have hsam : samples = [] := by
    unfold swOldSamplesS at hs
    rw [hk] at hs
    exact (Option.some.inj hs).symm
  have hcar : carried.kind = .plain := by
    unfold swCarriedS at hc
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hc
    have e₁ := foldl_kind (fun (r : RowMk) (j : ℕ) =>
      VerifiableInference.Desc.First.Shape.addRestES r W.g W.restPart
        (OnBytes.switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j 0)) (old.d.getD j 0))
      (fun _ _ => rfl) (List.range old.masks) b
    have hb' := foldlM_none_kind _ (fun r x => by rw [hk]; rfl) _ _ _ hb
    exact e₁.trans (by rw [hb']; rfl)
  have hgen : ∀ r ∈ gensS W old.masks, r.kind = .generator := by
    intro r hr
    unfold gensS at hr
    rw [hk] at hr
    rcases List.mem_cons.1 hr with rfl | hr
    · rfl
    · rcases List.mem_append.1 hr with hr | hr
      · cases hr
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
        rfl
  refine ⟨((List.replicate draws (gensS W old.masks)).flatten.map (·.kind)).length, ?_⟩
  rw [hsam]
  show carried.kind :: ((List.replicate draws (gensS W old.masks)).flatten.map (·.kind)) = _
  rw [hcar]
  congr 1
  refine List.eq_replicate_iff.2 ⟨rfl, fun k hk' => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hk'
  obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
  rw [(List.mem_replicate.1 hl).2] at hrl
  exact hgen r hrl

/-! ## The law -/

/-- **WHAT A CODE SWITCH WITHOUT KEPT MEMBERS LAYS.** -/
theorem switchEU_lays {p : P2} {grp : ℕ} {old : SingleSh} {T : SwitchTarget} {n₁ : OracleNotice}
    {a a' : CoreSh} {F F' : FormsSh} {ids : Array ℕ} {lay : TreeLay} {τ : TreeShape} {code maskCode : ℕ}
    (h : switchEU p grp old T #[n₁] a F = some (ids, a', F')) (noKept : T.kept = #[])
    (noMaskRows : T.shape.maskRows = 0)
    (layout : Own.treesMade a.st.codes #[⟨T.shape, T.leafClass⟩, n₁] = some lay)
    (oneTree : lay.shapes = #[τ]) (tree₀ : lay.tree.getD 0 0 = 0) (tree₁ : lay.tree.getD 1 0 = 0)
    (part₀ : lay.part.getD 0 0 = 0) (part₁ : lay.part.getD 1 0 = 1)
    (sampled : T.shape.answers ≠ 0) (unsampled : n₁.shape.answers = 0)
    (fresh : a.st.groups[grp]? = some ⟨code, maskCode, [], [], [], false⟩)
    (oldApart : ∀ o ∈ (oldOraclesS old).toList, ∀ q,
      (a.book.place ++ [(a.book.trees.length, 0), (a.book.trees.length, 1)])[o]? = some q →
        q.1 ≠ a.book.trees.length) :
    ∃ places n, Own.padMade a.st.codes T.shape = some places ∧
      ids = #[a.st.oracles.length, a.st.oracles.length + 1] ∧ a'.st.codes = a.st.codes ∧
      a'.st.groups[grp]? = some ⟨code, maskCode, [a.st.oracles.length], [false],
        .plain :: List.replicate n .generator, false⟩ ∧
      a'.st.groups.length = a.st.groups.length ∧
      a'.st.oracles[a.st.oracles.length]? = some ⟨T.shape, true, T.shape.answers,
        places.map fun p => (p.part, p.index), [grp],
        OnBytes.Slice.freshLedger a.st.codes T.shape, false⟩ ∧
      a'.st.oracles[a.st.oracles.length + 1]? = some (freshOrc n₁) ∧
      a'.st.oracles.length = a.st.oracles.length + 2 ∧
      a'.book.trees[a.book.trees.length]? = some ⟨τ, p.firstTree + a.roots, .own a.roots,
        [a.st.oracles.length, a.st.oracles.length + 1], true, 0⟩ ∧
      a'.book.trees.length = a.book.trees.length + 1 ∧
      a'.book.place = a.book.place ++ [(a.book.trees.length, 0), (a.book.trees.length, 1)] ∧
      a'.roots = a.roots + 1 ∧ a.st.oracles.length = a.book.place.length := by
  have hsent : _root_.Tw.K2.switchNotices T #[n₁] = #[⟨T.shape, T.leafClass⟩, n₁] := by
    simp [_root_.Tw.K2.switchNotices, noKept]
  unfold switchEU at h
  rw [hsent] at h
  obtain ⟨⟨ids', c⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨c', F''⟩, hb, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨e₀, e⟩ := Prod.mk.inj e
  obtain ⟨e₁, -⟩ := Prod.mk.inj e
  have e₀' : ids' = ids := e₀
  have e₁' : c' = a' := e₁
  subst e₀' e₁'
  obtain ⟨places, hpl, hi, hc, hg, ho, ht, hp, hro, hlen⟩ :=
    sendPS_two hs layout oneTree tree₀ tree₁ part₀ part₁ sampled unsampled
  dsimp only at hb
  unfold behindU at hb
  obtain ⟨B, hB, hb⟩ := Option.bind_eq_some_iff.1 hb
  rw [if_neg (by rw [noMaskRows]; exact Nat.lt_irrefl 0)] at hb
  obtain ⟨s1, e1, hb⟩ := Option.bind_eq_some_iff.1 hb
  obtain rfl := Option.some.inj e1
  obtain ⟨s2, h2, hb⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨s3, h3, hb⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨rows, hrows, hb⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨s4, h4, e⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨rfl, -⟩ := Prod.mk.inj e
  have hid : ids'.getD 0 noId = a.st.oracles.length := by
    rw [hi]
    rfl
  rw [hid] at h2
  -- no kept member joins
  have e3 : s3 = s2 := by
    rw [noKept] at h3
    have : (((ids'.extract 1 (1 + (#[] : Array OnBytes.KeptTarget).size)).zip
        (#[] : Array OnBytes.KeptTarget)).toList) = [] := by simp
    rw [this] at h3
    exact (Option.some.inj h3).symm
  subst e3
  -- the joining and the rows, in closed form
  unfold onSt at h2 h4
  obtain ⟨y2, hy2, rfl⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨y4, hy4, rfl⟩ := Option.map_eq_some_iff.1 h4
  have u2 := joinS_up hy2
  have u4 := addRowsS_up hy4
  obtain ⟨b₁, b₂, b₃⟩ := counted_apart hB a.book.trees.length (by rw [hp]; exact oldApart)
  have hgrp : c.st.groups[grp]? = some ⟨code, maskCode, [], [], [], false⟩ := by
    rw [hg]
    exact fresh
  obtain ⟨n, hkinds⟩ := swRowsS_kinds hrows (by rw [noKept]; simp)
  rw [hkinds] at u4
  refine ⟨places, n, hpl, hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hro, hlen⟩
  · rw [u4, u2]
    exact hc
  · rw [u4, u2]
    simp only [rowsUp, joinUp]
    rw [modAt_get, modAt_get, hgrp]
    simp [VerifiableInference.Desc.Ground.Sh.insAt]
  · rw [u4, u2]
    simp only [rowsUp, joinUp]
    rw [modAt_len, modAt_len, hg]
  · rw [u4, u2]
    simp only [rowsUp, joinUp]
    rw [modAt_get, ho]
    simp
  · rw [u4, u2]
    simp only [rowsUp, joinUp]
    rw [modAt_ne _ _ _ _ (Nat.succ_ne_self _), ho]
    simp
  · rw [u4, u2]
    simp only [rowsUp, joinUp]
    rw [modAt_len, ho]
    simp
  · show B.trees[a.book.trees.length]? = _
    rw [b₃, ht]
    simp
  · show B.trees.length = _
    rw [b₂, ht]
    simp
  · show B.place = _
    rw [b₁, hp]

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.modAt_behind
#print axioms ProofFile.Honest.K12.LotL.recvS_two
#print axioms ProofFile.Honest.K12.LotL.sendPS_two
#print axioms ProofFile.Honest.K12.LotL.counted_apart
#print axioms ProofFile.Honest.K12.LotL.swRowsS_kinds
#print axioms ProofFile.Honest.K12.LotL.switchEU_lays
#print axioms ProofFile.Honest.K12.LotL.modAt_ne
#print axioms ProofFile.Honest.K12.LotL.modAt_len
#print axioms ProofFile.Honest.K12.LotL.foldl_countB
#print axioms ProofFile.Honest.K12.LotL.swFrameS_no_kept
#print axioms ProofFile.Honest.K12.LotL.foldlM_none_kind
#print axioms ProofFile.Honest.K12.LotL.foldl_kind
