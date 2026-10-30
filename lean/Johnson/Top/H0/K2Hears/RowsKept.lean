-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/RowsKept.lean: the code switch: THE ROWS THAT THE SWITCH MAKES ARE
THE NEW ROWS OF THE GROUP IN THE RECORD THAT THE TEXT HANDS ON, at all three places where the kind
stands (a link, the head, the finish).

HeardRows.lean's yes_rows ends at "addRowsG S3 group rows = .ok w.st" and, at a link, at
"firstBehind w.st … = .ok (s'.st, …)". Here both are opened.
  from_rows      the plain ground's addRowsFrom: the statement behind is the library's withRows
  added_rows     addRowsG's yes: the group G was there, and behind it the group is G with the rows
                 added at the end of its open rows
  join_rows, joins_rows  a join leaves every group's open rows as they were
  first_keeps    firstBehind's yes: the same tables (BehindSame.lean's SameTables) and, group by
                 group, the same open rows
  YesRowsKept, yes_rows_kept  A YES OF decide: there are the front x, the statement S3, the array Y,
                 the rows and the group G as it stood in S3, with switchRows S3 … Y = some rows and
                 (s'.st.groups[x.f.group]?).map (·.rows) = some (G.rows ++ rows.toArray)
By withRows_group (OnBytes/Slice/BlkCalls.lean). NOT HERE: that G.rows is empty (the
group is new at a link and at the finish: newGroupG; at the head it is the record's). What G.rows
are: Whole.lean's behind_rows: the rows that the group had in front. What else firstBehind turns
(the frame f). No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.BehindSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut closeLedgerG joinG addRowsG firstBehind switchE switchBehind dOf)
open VerifiableInference.Desc.Ground (joinP addRowP addRowsP addRowsFrom rowsL)

theorem from_rows {L : Type} (g : Nat) : ∀ (rows : List OnBytes.Row) (d d' : Desc.Plain.DState L),
    addRowsFrom g rows d = some d' → d'.st = OnBytes.Slice.withRows d.st g rows
  | [], d, d', h => by
    cases h
    rfl
  | r :: l, d, d', h => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    unfold addRowP at h1
    split at h1
    · cases h1
      exact from_rows g l _ d' h2
    · cases h1

/-- The rows are added to the group. -/
theorem added_rows {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') :
    ∃ G, S.groups[g]? = some G ∧ S'.groups[g]? = some { G with rows := G.rows ++ rows.toArray } :=
        by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold addRowsP at hd
    split at hd
    · rename_i hok
      have hs : ((dOf S).st.groups[g]?).isSome = true := by
        simp [VerifiableInference.Desc.Ground.ok, rowsL] at hok
        simp [hok.1]
      obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hs
      refine ⟨G, hG, ?_⟩
      rw [from_rows g rows _ d hd]
      exact OnBytes.Slice.withRows_group g rows _ G hG
    · cases hd
  · cases h

theorem join_rows {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S')
    (i : Nat) : (S'.groups[i]?).map (·.rows) = (S.groups[i]?).map (·.rows) := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    unfold joinP at hd
    split at hd
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 hd
      show ((OnBytes.Slice.withMessageInGroup S g o kept G).groups[i]?).map (·.rows) = _
      unfold OnBytes.Slice.withMessageInGroup
      simp only [Array.getElem?_modify]
      split
      · rw [Option.map_map]
        rfl
      · rfl
    · cases hd
  · cases h

theorem joins_rows {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (S S' : Statement), l.foldlM (fun S p => joinG S g (f p) (k p)) S = .ok S' →
    ∀ i : Nat, (S'.groups[i]?).map (·.rows) = (S.groups[i]?).map (·.rows)
  | [], S, S', h, i => by
    cases h
    rfl
  | p :: l, S, S', h, i => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    exact (joins_rows g f k l S1 S' h2 i).trans (join_rows h1 i)

/-- **Behind a later link's switch the tables and the groups' open rows are as they were.** -/
theorem first_keeps {S S' : Statement} {x : _root_.Tw.K2.Front} {s : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x s plain = .ok (S', f, mine)) :
    SameTables S S' ∧ ∀ i : Nat, (S'.groups[i]?).map (·.rows) = (S.groups[i]?).map (·.rows) := by
  unfold firstBehind at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i S'' hS
          have e : S'' = S' := by
            injection h with h1
            exact (Prod.mk.inj h1).1
          rw [e] at hS
          exact ⟨same_joins (α := OnBytes.Params.ReqMessage × Nat) x.f.group (fun y => y.2)
              (fun y => decide (0 < y.1.life)) _ S S' hS,
            joins_rows (α := OnBytes.Params.ReqMessage × Nat) x.f.group (fun y => y.2)
              (fun y => decide (0 < y.1.life)) _ S S' hS⟩

/-- **A yes of decide: the rows made are the group's new rows in the record handed on.** -/
def YesRowsKept : Prop := ∀ snd p s r₁ r₂ gs s', decideWith snd p s [r₁, r₂] gs = .ok s' →
  ∃ (x : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent) (S3 : Statement) (Y : Array E)
    (rows : List OnBytes.Row) (G : Group),
    frontAt p s = some x ∧
    oldRead snd p s r₁ r₂ gs = some (x.f.rows, Positions.ofDraws p.logN r₂.drawn.poss, Y) ∧
    switchRows S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size))
      (Positions.ofDraws p.logN r₂.drawn.poss) Y = some rows ∧
    S3.groups[x.f.group]? = some G ∧
    (s'.st.groups[x.f.group]?).map (·.rows) = some (G.rows ++ rows.toArray)

theorem yes_rows_kept : YesRowsKept := fun snd p s r₁ r₂ gs s' h => by
  obtain ⟨x, w, y, S3, Y, rows, hx, ho, -, hm, hl, hb⟩ := yes_rows snd p s r₁ r₂ gs s' h
  obtain ⟨G, hG, hG'⟩ := added_rows hl
  refine ⟨x, y, S3, Y, rows, G, hx, ho, hm, hG, ?_⟩
  rcases hb with ⟨-, f, mine, hf⟩ | ⟨-, e⟩
  · rw [(first_keeps hf).2, hG']
    rfl
  · rw [e, hG']
    rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.added_rows
#print axioms VerifiableInference.Desc.First.K2.first_keeps
#print axioms VerifiableInference.Desc.First.K2.yes_rows_kept
