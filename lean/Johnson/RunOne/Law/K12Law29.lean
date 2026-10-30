-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Law29.lean: The key file's tables, row 2.9 (the
proximity test on the folded row's group G_u; border 9 of the shared chain): THE «law» OF ITS WAY
BACK (the premise of that name of `relAt_back_to`, KeyQuietSub.lean): the row's five closed items
hold in front, at the witness in which message 3 (U) is laid. Statements and proofs, at the tables'
own letters (Johnson/RunOne/KeyRows23At.lean: F · Fr₂ · G₂ · at_ · S · K₁ · R · enc · rad).
The row (Johnson/Desc/Key/KeyBorders23.lean): ins := [claim 2 "record", claim 2 "columns",
claim 2 "FoldU", srow 3, pin 3] · ctx := [pin 5, srow 5] · lays := [3]. THE GROUP HAS TWO MEMBERS: U
(message 3) AND THE SHARED SPLIT's MASKS (message 5): THE ROW LAYS THE FIRST; THE SECOND RIDES.
  `items_29`: what the five items say, unfolded: all of G_u's open rows (three runs) and message 3's
    sample rows hold at the witness, and message 3 is PINned.
  `law_29_of_tuple`: from the border's promise, a tuple of tables (one a member of the group) that
    are members of their committed words' lists and meet their out-of-domain (OOD) samples, the
    riding member's pin, and «all rows taken in hold of the tuple's words»: the five items at the
    laid witness. By the engine (K12LawLay.lean).
  `law_29`: the premise «law» of `relAt_back_to` at the row, to the letter. `row_29`: the table's
    own row has these lists (by evaluation).
What it is not. WHERE THE TUPLE COMES FROM IS NOT HERE: the test's law (`core_behind_QW`,
Johnson/Desc/K12/Coin/CoreBehindQ.lean) hands typed messages with `AllSay` and `CandAt`; the bridge
(`cand_laid_of_candAt₂`, Johnson/Top/Fire/Code/CandBridge.lean) makes them members; that the laid
table reads as the typed message's own is typed by nobody yet. The counts on the verifier's state,
OffTables, the tables' sizes and «the rows name the group's members alone» are premises. It pays no
field of the tables. No soundness is claimed. Nothing on hiding.

-/
import Johnson.RunOne.Law.K12LawLay
import Johnson.RunOne.KeyRows23At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Law29
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12LawLay

section
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where) (S : LinShape) (K₁ : KPlan)
  (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad : Nat)

/-- **What the row's five closed items say.** -/
theorem items_29 (a : P₂ × St₂) (y : Strs) (w' : Wit Cells Unit M) (G0 : Group)
    (x : OnBytes.Oracle) (hG : a.2.st.groups[a.2.loc.gU]? = some G0)
    (hc : S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0)
    (hx : a.2.st.oracles[0]? = some x) (hsm : x.sampled = true) (hsz : x.sampleRows.size ≠ 0)
    (hrows : ∀ r ∈ G0.rows.toList, RowHolds R.same a.2.st (valOf (plan₂ S) R w') r)
    (hsr : ∀ r ∈ x.sampleRows.toList, RowHolds R.same a.2.st (valOf (plan₂ S) R w') r)
    (hpin : PIN F G₂ (at_ 3).1 (at_ 3).2 a y w') :
    ∀ i ∈ [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3],
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) a y w' := by
  have run : ∀ lo n, lo + n ≤ G0.rows.size → n ≠ 0 →
      rowsHold R.same a.2.st (valOf (plan₂ S) R w') a.2.loc.gU lo n := fun lo n hl hn =>
    ⟨G0, hG, hl, hn, fun r hr => hrows r (List.mem_of_mem_drop (List.mem_of_mem_take hr))⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · show claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "record" a y w'
    have e : claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "record" a y w' =
        rowsHold R.same a.2.st (valOf (plan₂ S) R w') a.2.loc.gU 0 S.fold.index.answers := by
      unfold claim₂
      simp
      rfl
    rw [e]
    exact run _ _ (by omega) h1
  · show claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "columns" a y w'
    have e : claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "columns" a y w' =
        rowsHold R.same a.2.st (valOf (plan₂ S) R w') a.2.loc.gU S.fold.index.answers
          S.fold.columns := by
      unfold claim₂
      simp
      rfl
    rw [e]
    exact run _ _ (by omega) h2
  · show claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "FoldU" a y w'
    have e : claim₂ K₁ (plan₂ S) R (readers₂ S) enc rad 2 "FoldU" a y w' =
        rowsHold R.same a.2.st (valOf (plan₂ S) R w') a.2.loc.gU
          (S.fold.index.answers + S.fold.columns) 1 := by
      unfold claim₂
      simp
      rfl
    rw [e]
    exact run _ _ hc (by decide)
  · show srowAt R (plan₂ S) a.2.st 3 w'
    exact ⟨0, x, rfl, hx, hsm, hsz, hsr⟩
  · exact hpin

end

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)
variable {XI Cells M Smp Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (G₂ : Reading (P₂ × St₂) Cells M Smp Rec) (at_ : Where) (S : LinShape) (K₁ : KPlan)
  (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

theorem five_pinned : 5 ∈ pinned (open₂ 9) := by decide

/-- **The law of row 2.9's way back, from a tuple of tables.** tbl 3: laid; tbl 5: rides. -/
theorem law_29_of_tuple (x : (P₂ × St₂) × Fr₂.E.Str) (w : Wit Cells Unit M) (tbl : Nat → M)
    (hon : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 9 x) (hi : LayIdem G₂)
    (hap : SeatsApart at_ [3] [3]) (hap' : SeatsApart at_ [3] [5])
    (hm : ∀ k, k = 3 ∨ k = 5 → ∃ o z, F.oracleAt (at_ k).1 = some o ∧
      G₂.smp x.1 (at_ k).1 (at_ k).2 = some z ∧
      Member F G₂ o (at_ k).1 (at_ k).2 (strsOf Fr₂ x.2) z (tbl k))
    (hp5 : PIN F G₂ (at_ 5).1 (at_ 5).2 x.1 (strsOf Fr₂ x.2) w)
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (St' : Statement) (G0 : Group)
    (x0 : OnBytes.Oracle) (rs : List OnBytes.Row) (W : Means.Words GE)
    (hall : Means.AllSay ρ St' rs W) (hoff : ∀ r ∈ rs, OffTables ρ x.1.2.st r)
    (hsz : ∀ r ∈ rs, ∀ o ∈ r.oracles, ∀ pt,
      Means.tableSize St' o pt = Means.tableSize x.1.2.st o pt)
    (hW : ∀ r ∈ rs, ∀ o ∈ r.oracles, ∃ k, (k = 3 ∨ k = 5) ∧ (plan₂ S).num o = some k ∧
      W o = entOf ρ R (tbl k))
    (hG : x.1.2.st.groups[x.1.2.loc.gU]? = some G0) (hsub : ∀ r ∈ G0.rows.toList, r ∈ rs)
    (hc : S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsm : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0) (hsub' : ∀ r ∈ x0.sampleRows.toList, r ∈ rs) :
    ∀ i ∈ [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3],
      i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2)
        (layAt at_ [3] tbl w) := by
  obtain ⟨_, _, hfree, hno⟩ := hon.resolve_left (fun h => h trivial)
  have arr3 : ArrOk G₂ at_ [3] := fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have arr5 : ArrOk G₂ at_ [5] := fun k hk => hfree.arr k (by simp at hk; subst hk; decide)
  have rd3 : ReadsPinned G₂ at_ R [3] := fun v k hk =>
    hfree.reads v k (by simp at hk; subst hk; decide)
  have rd5 : ReadsPinned G₂ at_ R [5] := fun v k hk =>
    hfree.reads v k (by simp at hk; subst hk; decide)
  have hread := reads_all F G₂ at_ R [3] [5] tbl w arr3 arr5 rd3 rd5 hi hap
    (fun k hk => by simp at hk; subst hk; decide) hap' x.1 (strsOf Fr₂ x.2)
    (fun k hk => by simp at hk; subst hk; exact hno 5 five_pinned)
    (fun k hk => by simp at hk; subst hk; exact hp5)
    (fun k hk => by simp at hk; subst hk; exact hm 5 (Or.inr rfl))
  have hrows := rows_of_tuple ρ (plan₂ S) R hsame St' x.1.2.st (layAt at_ [3] tbl w) rs W hall hoff
    hsz fun r hr o ho => by
      obtain ⟨k, hk, hn, e⟩ := hW r hr o ho
      rw [e, wordsOf_num ρ (plan₂ S) R _ hn, hread k (by
        rcases hk with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp))]
  exact items_29 F G₂ at_ S K₁ R enc rad x.1 (strsOf Fr₂ x.2) _ G0 x0 hG hc h1 h2 hx hsm hss
    (fun r hr => hrows r (hsub r hr)) (fun r hr => hrows r (hsub' r hr))
    (pin_laid F G₂ at_ [3] tbl w arr3 hi hap x.1 (strsOf Fr₂ x.2) 3 (by simp) (hm 3 (Or.inl rfl)))

/-- **The premise «law» of `relAt_back_to` at row 2.9, to the letter**: at any row r with the
table's row's `ins` whose `outs ++ ctx` holds pin 5: a′ := b · y′ · w behind; a := x.1 · the strings
of x.2 · the laid witness in front. The riding member's pin comes back by `rides_pin2_at`
(Johnson/Desc/Key/KeyQuiet.lean): its OOD sample and its committed word stay across the test. -/
theorem law_29 (r : KRow)
    (hins : r.ins =
      [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3])
    (hctx : KItem.pin 5 ∈ r.outs ++ r.ctx) (x : (P₂ × St₂) × Fr₂.E.Str) (b : P₂ × St₂)
    (y' : Strs) (w : Wit Cells Unit M) (tbl : Nat → M)
    (hon : on₂ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ 9 x) (hi : LayIdem G₂)
    (hap : SeatsApart at_ [3] [3]) (hap' : SeatsApart at_ [3] [5])
    (hm : ∀ k, k = 3 ∨ k = 5 → ∃ o z, F.oracleAt (at_ k).1 = some o ∧
      G₂.smp x.1 (at_ k).1 (at_ k).2 = some z ∧
      Member F G₂ o (at_ k).1 (at_ k).2 (strsOf Fr₂ x.2) z (tbl k))
    (hsmp : G₂.smp b (at_ 5).1 (at_ 5).2 = G₂.smp x.1 (at_ 5).1 (at_ 5).2)
    (hword : wordOf F y' (at_ 5).1 (at_ 5).2 = wordOf F (strsOf Fr₂ x.2) (at_ 5).1 (at_ 5).2)
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (St' : Statement) (G0 : Group)
    (x0 : OnBytes.Oracle) (rs : List OnBytes.Row) (W : Means.Words GE)
    (hall : Means.AllSay ρ St' rs W) (hoff : ∀ r ∈ rs, OffTables ρ x.1.2.st r)
    (hsz : ∀ r ∈ rs, ∀ o ∈ r.oracles, ∀ pt,
      Means.tableSize St' o pt = Means.tableSize x.1.2.st o pt)
    (hW : ∀ r ∈ rs, ∀ o ∈ r.oracles, ∃ k, (k = 3 ∨ k = 5) ∧ (plan₂ S).num o = some k ∧
      W o = entOf ρ R (tbl k))
    (hG : x.1.2.st.groups[x.1.2.loc.gU]? = some G0) (hsub : ∀ r ∈ G0.rows.toList, r ∈ rs)
    (hc : S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsm : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0) (hsub' : ∀ r ∈ x0.sampleRows.toList, r ∈ rs) :
    (∀ i ∈ r.outs ++ r.ctx, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) b y' w) →
      ∀ i ∈ r.ins, i.holds F G₂ at_ (meaning₂ S K₁ R enc rad) x.1 (strsOf Fr₂ x.2)
        (layAt at_ [3] tbl w) := by
  intro h
  rw [hins]
  exact law_29_of_tuple ρ F Fr₂ G₂ at_ S K₁ R enc rad a coll last₁ off₂ x w tbl hon hi hap hap' hm
    (rides_pin2_at F G₂ (at_ 5).1 (at_ 5).2 x.1 b (strsOf Fr₂ x.2) y' w hsmp hword (h _ hctx))
    hsame St' G0 x0 rs W hall hoff hsz hW hG hsub hc h1 h2 hx hsm hss hsub'

/-- The table's own row has these two lists. -/
theorem row_29 : (rows₂[9]?).map (fun r => (r.ins, r.outs, r.ctx, r.lays)) =
    some ([KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3], [],
      [KItem.pin 5, .srow 5], [3]) := by decide

end

end Johnson.RunOne.Law.K12Law29

#print axioms Johnson.RunOne.Law.K12Law29.items_29
#print axioms Johnson.RunOne.Law.K12Law29.law_29_of_tuple
#print axioms Johnson.RunOne.Law.K12Law29.law_29
#print axioms Johnson.RunOne.Law.K12Law29.row_29
