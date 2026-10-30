-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Page.lean: the plain functions on the statement keep it in order.

The effects on the statement that the steps of the description call are plain functions, each a list
of named clauses and a pure effect of the library (Johnson/Desc/First/Base/Ground.lean). This file
shows of each that, where it returns a state, the statement stays in order (InOrder,
Johnson/Desc/Means/Order.lean); that a row which the adding takes meets RowIn; and the law of the
batching at what the beginning of a test returns.

Main theorems: rowIn_of_rowL, addRowP_keeps, addRowsP_keeps, joinP_keeps, newGroupP_keeps,
recvP_keeps, adoptP_keeps, admitP_keeps, takeMaskP_keeps, closeLedgerP_keeps, spendAsMaskP_keeps,
RowOn.renamed, elsewhereP_keeps, beginRunP_keeps, beginRunP_means.

What is not claimed. admitP_keeps takes as a condition that the sample rows are on their oracle
message, and elsewhereP_keeps that the other statement is in order. That a block changes the
statement by these functions alone.
Nothing on soundness.

-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Means.Order
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree
import Johnson.Desc.Own.LayoutAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

variable {Lc : Type}

/-- A clause on a value that is there is the clause of the value. -/
theorem has_some {α : Type} (a : α) (f : α → Bool) : has (some a) f = f a := rfl

/-- **A row that passes the clauses of the adding meets RowIn.** -/
theorem rowIn_of_rowL {S : Statement} {g : Nat} {row : Row} (h : ok (rowL S g row) = true) :
    ∃ G, S.groups[g]? = some G ∧ RowIn S G row := by
  simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  simp only [← VerifiableInference.Desc.Own.placeFits_agrees,
    ← VerifiableInference.Desc.Own.formFits_agrees] at h
  obtain ⟨h1, _, _, h4, h5, h6, h7, _⟩ := h
  cases hG : S.groups[g]? with
  | none =>
    rw [hG] at h1
    cases h1
  | some G =>
    rw [hG, has_some] at h4 h5 h6 h7
    simp only [Array.all_eq_true_iff_forall_mem, Bool.and_eq_true, decide_eq_true_eq] at h4 h5 h6 h7
    exact ⟨G, rfl, fun t ht => (h4 t (Array.mem_toList_iff.1 ht)).2,
      fun u hu => h5 u (Array.mem_toList_iff.1 hu),
      fun w hw => ⟨(h6 w (Array.mem_toList_iff.1 hw)).1.1.2, (h6 w (Array.mem_toList_iff.1 hw)).1.2,
        (h6 w (Array.mem_toList_iff.1 hw)).2⟩,
      fun f hf => h7 f (Array.mem_toList_iff.1 hf)⟩

/-- The adding of a row. -/
theorem addRowP_keeps {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hI : InOrder d.st) :
    InOrder d'.st ∧ ∃ G, d.st.groups[g]? = some G ∧ RowIn d.st G row ∧
      d'.st = Slice.withRow d.st g row := by
  unfold addRowP at h
  by_cases c : ok (rowL d.st g row) = true
  · rw [if_pos c] at h
    obtain rfl := Option.some.inj h
    obtain ⟨G, hG, hr⟩ := rowIn_of_rowL c
    exact ⟨hI.withRow g G row hG hr, G, hG, hr, rfl⟩
  · rw [if_neg c] at h
    cases h

theorem addRowsFrom_keeps (g : Nat) : ∀ (l : List Row) (d d' : DState Lc),
    addRowsFrom g l d = some d' → InOrder d.st → InOrder d'.st
  | [], d, d', h, hI => by
    obtain rfl := Option.some.inj h
    exact hI
  | row :: l, d, d', h, hI => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_keeps g l d1 d' h2 (addRowP_keeps h1 hI).1

/-- The adding of rows. -/
theorem addRowsP_keeps {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hI : InOrder d.st) : InOrder d'.st := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_keeps g rows d d' h hI
  · cases h

/-- A message joins a group. -/
theorem joinP_keeps {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold joinP at h
  by_cases c : ok (joinL d.st g o kept) = true
  · rw [if_pos c] at h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    obtain ⟨_, c2, _, _, c5, c6, c7, _⟩ := c
    cases hx : d.st.oracles[o]? with
    | none =>
      rw [hx] at c2
      cases c2
    | some x =>
      rw [hG, hx, has_some, has_some] at c5 c6
      rw [hG, has_some] at c7
      simp only [Bool.or_eq_true, beq_iff_eq] at c5 c6
      have hnew : o ∉ G.members.toList := by
        intro hm
        have : G.members.contains o = true := by simpa using hm
        rw [this] at c7
        cases c7
      exact hI.withMessageInGroup g o kept G x hG hx hnew c5 c6
  · rw [if_neg c] at h
    cases h

/-- A new group. -/
theorem newGroupP_keeps {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact hI.withGroup a b
  · cases h

/-- The oracle messages of a prover's message. -/
theorem recvP_keeps {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hI : InOrder d.st) : InOrder d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hI.stSent sent
  · cases h

/-- Messages whose trees another chain has sent. -/
theorem adoptP_keeps {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hI : InOrder d.st) : InOrder d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hI.stSent sent
  · cases h

/-- A sample's answers are in: if the sample rows are on the message. -/
theorem admitP_keeps {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st)
    (hr : ∀ r ∈ rows.toList, RowOn d.st o r) : InOrder d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact hI.admitted o x.shape places rows hr
  · cases h

/-- An effect on one oracle message that leaves its shape and its sample rows. -/
theorem InOrder.onOracle {S : Statement} (hI : InOrder S) (o : Nat) (f : Oracle → Oracle)
    (h1 : ∀ x, (f x).shape = x.shape) (h2 : ∀ x, (f x).sampleRows = x.sampleRows) :
    InOrder { S with oracles := S.oracles.modify o f } := by
  have hE : Extends S { S with oracles := S.oracles.modify o f } :=
    Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ h1
  exact hI.sameGroups hE rfl (hI.samples_of hE fun o' => map_modify _ _ _ _ _ h2)

/-- The next free mask entry. -/
theorem takeMaskP_keeps {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hI.onOracle o _ (fun _ => rfl) (fun _ => rfl)
  · cases h

/-- A ledger is shut. -/
theorem closeLedgerP_keeps {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    have hE := extends_closeLedgers d.st [o]
    exact hI.sameGroups hE (closeLedgers_groups [o] d.st)
      (hI.samples_of hE (closeLedgers_sampleRows [o] d.st))
  · cases h

/-- A message becomes a mask. -/
theorem spendAsMaskP_keeps {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hI.onOracle o _ (fun _ => rfl) (fun _ => rfl)
  · cases h

/-! ## A message that is sampled in another statement -/

theorem getElem?_modify_some {A : Array Oracle} {o o' : Nat} {f : Oracle → Oracle} {x' : Oracle}
    (h : (A.modify o f)[o']? = some x') :
    (o = o' ∧ ∃ x, A[o']? = some x ∧ x' = f x) ∨ (o ≠ o' ∧ A[o']? = some x') := by
  rw [Array.getElem?_modify] at h
  by_cases c : o = o'
  · rw [if_pos c] at h
    obtain ⟨x, h1, h2⟩ := Option.map_eq_some_iff.1 h
    exact Or.inl ⟨c, x, h1, h2.symm⟩
  · rw [if_neg c] at h
    exact Or.inr ⟨c, h⟩

/-- A row on an oracle message of one statement, renamed, is on an oracle message of another that
has the same tables. -/
theorem RowOn.renamed {S T : Statement} {mine theirs : Nat} {r : Row}
    (hh : ∀ part, T.has theirs part = true → S.has mine part = true)
    (hb : ∀ part, T.has theirs part = true → S.tableBits mine part = T.tableBits theirs part)
    (h : RowOn T theirs r) : RowOn S mine (r.renamed mine) := by
  have key : ∀ {o : Nat} {part : Part} {index : Nat} (vars : Nat),
      Blk.placeOk T { code := 0, members := #[theirs] } o part vars index = true →
      o = theirs ∧ T.has theirs part = true ∧ vars = T.tableBits theirs part ∧
        index < 2 ^ T.tableBits theirs part := by
    intro o part index vars hp
    obtain ⟨hm, h1, h2, h3⟩ := (placeOk_iff _ _ _ _ _ _).1 hp
    have e : o = theirs := by simpa using hm
    subst e
    exact ⟨rfl, h1, h2, h3⟩
  have mk : ∀ {part : Part} {index : Nat}, T.has theirs part = true →
      index < 2 ^ T.tableBits theirs part →
      Blk.placeOk S { code := 0, members := #[mine] } mine part (S.tableBits mine part) index =
        true := by
    intro part index h1 h3
    exact (placeOk_iff _ _ _ _ _ _).2 ⟨by simp, hh part h1, rfl, by rw [hb part h1]; exact h3⟩
  refine ⟨fun t ht => ?_, fun u hu => ?_, fun w hw => ?_, fun f hf => ?_⟩
  · have ht' : t ∈ (r.terms.map fun t => { t with oracle := mine }).toList := ht
    simp only [Array.toList_map, List.mem_map] at ht'
    obtain ⟨t0, h0, rfl⟩ := ht'
    obtain ⟨_, h1, h2, h3⟩ := key _ (h.terms t0 h0)
    have e : t0.v.vars = S.tableBits mine t0.part := by rw [hb _ h1]; exact h2
    show Blk.placeOk S _ mine t0.part t0.v.vars 0 = true
    rw [e]
    exact mk h1 h3
  · have hu' : u ∈ (r.units.map fun u => { u with oracle := mine }).toList := hu
    simp only [Array.toList_map, List.mem_map] at hu'
    obtain ⟨u0, h0, rfl⟩ := hu'
    obtain ⟨_, h1, _, h3⟩ := key _ (h.units u0 h0)
    exact mk h1 h3
  · have hw' : w ∈ (r.runs.map fun w => { w with oracle := mine }).toList := hw
    simp only [Array.toList_map, List.mem_map] at hw'
    obtain ⟨w0, h0, rfl⟩ := hw'
    obtain ⟨a1, a2, a3⟩ := h.runs w0 h0
    obtain ⟨_, h1, _, h3⟩ := key _ a3
    exact ⟨a1, a2, mk h1 h3⟩
  · have hf' : f ∈ (r.forms.map fun f => { f with oracle := mine }).toList := hf
    simp only [Array.toList_map, List.mem_map] at hf'
    obtain ⟨f0, h0, rfl⟩ := hf'
    obtain ⟨a1, a2⟩ := h.forms f0 h0
    obtain ⟨e0, h1, _, h3⟩ := key _ a1
    refine ⟨mk h1 h3, ?_⟩
    show f0.c.fits (S.tableBits mine .main) = true
    rw [hb _ h1, ← e0]
    exact a2

/-- A message is sampled in another statement that is in order. -/
theorem elsewhereP_keeps {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hI : InOrder d.st) (hO : InOrder other) :
    InOrder d'.st := by
  unfold elsewhereP at h
  by_cases c : ok (elsewhereL d.st mine other theirs) = true
  · rw [if_pos c] at h
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, elsewhereL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    obtain ⟨c1, _, _, _, c5, c6, c7⟩ := c
    cases hx : d.st.oracles[mine]? with
    | none =>
      rw [hx] at c1
      cases c1
    | some x =>
      rw [hx, hy, has_some, has_some] at c5 c6 c7
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at c5 c6 c7
      obtain ⟨⟨⟨r1, _⟩, r3⟩, _⟩ := c5
      have hrows : ∀ part, x.shape.rows part = y.shape.rows part := by
        intro part
        cases part
        · exact r1
        · exact r3
      have hh : ∀ part, other.has theirs part = true → d.st.has mine part = true := by
        intro part hp
        unfold Statement.has at hp ⊢
        rw [hy] at hp
        rw [hx]
        dsimp only at hp ⊢
        rw [hrows]
        exact hp
      have hb : ∀ part, other.has theirs part = true →
          d.st.tableBits mine part = other.tableBits theirs part := by
        intro part hp
        unfold Statement.has at hp
        rw [hy] at hp
        have hpos : 0 < y.shape.rows part := by simpa using hp
        unfold Statement.tableBits Statement.rowBits Statement.placeBits
        rw [hx, hy]
        dsimp only
        rw [hrows]
        congr 1
        have hne : (y.shape.rows part == 0) = false := by
          simp
          omega
        rw [hne]
        cases part with
        | main =>
          have hm : ¬ x.shape.mainRows = 0 := by
            have e := hrows .main
            have e' : x.shape.mainRows = y.shape.rows .main := e
            omega
          have e : d.st.codes.base[x.shape.code]? = other.codes.base[y.shape.code]? := by
            first
              | exact c6.resolve_left hm
              | (have h6 := c6.resolve_left hm
                 cases hc : d.st.codes.base[x.shape.code]? with
                 | none =>
                   rw [hc] at h6
                   simp [has] at h6
                 | some c =>
                   rw [hc, has_some] at h6
                   exact (beq_iff_eq.1 h6).symm)
          simp only [Bool.false_eq_true, if_false, Array.getD_eq_getD_getElem?, e]
        | mask =>
          have hm : ¬ x.shape.maskRows = 0 := by
            have e := hrows .mask
            have e' : x.shape.maskRows = y.shape.rows .mask := e
            omega
          have e : d.st.codes.mask[x.shape.maskCode]? = other.codes.mask[y.shape.maskCode]? := by
            first
              | exact c7.resolve_left hm
              | (have h7 := c7.resolve_left hm
                 cases hc : d.st.codes.mask[x.shape.maskCode]? with
                 | none =>
                   rw [hc] at h7
                   simp [has] at h7
                 | some c =>
                   rw [hc, has_some] at h7
                   exact (beq_iff_eq.1 h7).symm)
          simp only [Bool.false_eq_true, if_false, Array.getD_eq_getD_getElem?, e]
      have hE : Extends d.st { d.st with oracles := d.st.oracles.modify mine fun x =>
          { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                   pad := y.pad } } :=
        Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl
      refine hI.sameGroups hE rfl fun o' x' hx' r hr => ?_
      rcases getElem?_modify_some hx' with ⟨rfl, x0, _, rfl⟩ | ⟨_, h0⟩
      · have hr' : r ∈ (y.sampleRows.map (·.renamed mine)).toList := hr
        simp only [Array.toList_map, List.mem_map] at hr'
        obtain ⟨r0, h0, rfl⟩ := hr'
        exact (RowOn.renamed hh hb (hO.samples theirs y hy r0 h0)).extends hE
      · exact (hI.samples o' x' h0 r hr).extends hE
  · rw [if_neg c] at h
    cases h

/-- What the beginning of a test returns. -/
theorem beginRunP_inv {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) :
    ∃ G, d.st.groups[g]? = some G ∧ input = ⟨layoutOf d.st G, Slice.runRows d.st G⟩ ∧
      d'.st = Slice.begun d.st g G := by
  unfold beginRunP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨G, hG, e1, e2⟩ := h
    have hl : d.st.layout g = some (VerifiableInference.Desc.Own.layoutOf d.st G) := by
      rw [← VerifiableInference.Desc.Own.layoutMade_eq, VerifiableInference.Desc.Own.layoutMade, hG]
      rfl
    rw [layout_eq d.st g G hG] at hl
    rw [← Option.some.inj hl] at e1
    exact ⟨G, hG, e1.symm, by rw [← e2]⟩
  · cases h

/-- The beginning of a test. -/
theorem beginRunP_keeps {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hI : InOrder d.st) : InOrder d'.st := by
  obtain ⟨G, hG, _, e⟩ := beginRunP_inv h
  rw [e]
  exact hI.begun g G hG

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The batching behind the beginning of a test**, at a statement in order: Bat.combine, at the
statement and the input that the beginning returns, returns a row; it has no coefficient where the
tables hold no word; and for all words it is short, on the group's tables, of the sum of x^i times
what row number i was short of in the statement before. -/
theorem beginRunP_means {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hI : InOrder d.st) (x : E) :
    ∃ out, Bat.combine d'.st g input x = some out ∧ MaskReady input.layout out ∧
      Clean ρ d'.st input.layout out ∧ ∀ m : Words K,
        groupShort ρ d'.st input.layout out (tablesOf d'.st input.layout m) =
          hornerSum (ρ.val x) (input.rows.toList.map fun r => short ρ d.st r m) := by
  obtain ⟨G, hG, rfl, e⟩ := beginRunP_inv h
  rw [e]
  exact (begin_inOrder ρ hI g G x hG).2

end OnBytes.Means
