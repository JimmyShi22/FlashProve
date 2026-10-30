-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsFirst.lean: WHERE THE LAW-SIDE MAKER OF THE SENDINGS' ROWS RETURNS
(`Johnson.G.sendRowsOf`, Johnson/G/LinkSig.lean), THE ROWS OF THE PROOF FILE's FIRST CHAIN ARE ONE
FOR EACH OF ITS SENDINGS, IN ORDER, EACH WITH AS MANY SAMPLED MESSAGES AS THE SENDING HAS MESSAGES
WITH AN ANSWER. And three steps for the named test `radIsB` (Johnson/P5T/MembersByMake.lean).
Theorems on public data. A law file; no running text imports it.

  `cnt s`           how many oracle messages of a sending have an answer.
  `mapM_zip_rel`, `rel_flat`   steps on lists made entry by entry.
  `pack_aligned`    where `packListOf` (Johnson/G/PackList.lean) returns: its list goes with the
                    sendings, one entry a sending, each entry's list as long as cnt of its sending;
                    as far as the calls' chains reach.
  `isFirst`, `filter_tag`, `sendsFrom_tags`   of sendsFrom's seven lists the fifth alone bears
                    ("proof", 0).
  `rows_first`      sendRowsOf … = .ok rows · sendsOf … = .ok [k0, k1, k2, e, p0, p1, p2] · the
                    seven names ⊢ (firstRows rows).map (·.sampled.length) = p0.sends.map cnt.
  `radIsB_of_some`  at rad := radOf rows the test says only that the rows HAVE a radius at every
                    entry with a sample: each clause is x == some (x.getD 0).
  `rad_some`        from the rows' lengths to "has a radius".
  `filter_range_len`, `flat_beyond`, `flat_at`   steps.
  `mine_le`         the plan's entries with a sample of sending k (mineAt (planSeats Z dl) k) are at
                    most cnt of that sending. No premise.

Limits. From returns alone: that sendRowsOf or packListOf returns is shown nowhere here. Lengths
alone: nothing on what a radius is. Nothing on soundness or on hiding.

-/
import Johnson.P5T.MembersByMake
import Johnson.Desc.First.Link.Law.MadeSends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (Listed Sending ChainSends SendRow sendRowsOf packListOf sendsOf)
open P5T (PSeat planSeats mineAt rad? radOf radIsB firstRows)

/-- How many oracle messages of a sending have an answer. -/
def cnt (s : Sending) : Nat := (s.sent.filter fun m => decide (0 < m.shape.answers)).length

/-- What is made entry by entry of two zipped lists stands in a relation with the second list, as
far as the first reaches. -/
theorem mapM_zip_rel {α β γ : Type} (f : α × β → Except String γ) (R : β → γ → Prop)
    (hf : ∀ a b c, f (a, b) = .ok c → R b c) :
    ∀ (xs : List α) (ys : List β) (out : List γ), (xs.zip ys).mapM f = .ok out →
      List.Forall₂ R (ys.take xs.length) out
  | [], ys, out, h => by
    rw [List.zip_nil_left] at h
    cases h
    exact List.Forall₂.nil
  | x :: xs, [], out, h => by
    rw [List.zip_nil_right] at h
    cases h
    exact List.Forall₂.nil
  | x :: xs, y :: ys, out, h => by
    rw [List.zip_cons_cons, List.mapM_cons] at h
    obtain ⟨c, hc, h⟩ := exc_bind h
    obtain ⟨cs, hcs, h⟩ := exc_bind h
    cases h
    rw [List.length_cons, List.take_succ_cons]
    exact List.Forall₂.cons (hf x y c hc) (mapM_zip_rel f R hf xs ys cs hcs)

/-- Lists of lists in relation, laid flat. -/
theorem rel_flat {R : Sending → Codes × List (OracleShape × Nat) → Prop} :
    ∀ {ds : List ChainSends} {per : List (List (Codes × List (OracleShape × Nat)))},
      List.Forall₂ (fun d L => List.Forall₂ R d.sends L) ds per →
      List.Forall₂ (fun (x : ChainSends × Sending) e => R x.2 e)
        (ds.flatMap fun c => c.sends.map fun s => (c, s)) per.flatten
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons (a := d) h t => by
    rw [List.flatMap_cons, List.flatten_cons]
    have h1 : List.Forall₂ (fun (x : ChainSends × Sending) e => R x.2 e)
        (d.sends.map fun s => (d, s)) _ := List.forall₂_map_left_iff.2 h
    exact List.rel_append h1 (rel_flat t)

/-- **The list of radii goes with the sendings**, as far as the calls' chains reach. -/
theorem pack_aligned {pol lay KL : ByteArray} {pack : List (Codes × List (OracleShape × Nat))}
    {sends : List ChainSends} (hp : packListOf pol lay KL = .ok pack)
    (hs : sendsOf pol lay KL = .ok sends) :
    ∃ m, List.Forall₂ (fun (x : ChainSends × Sending) e => e.2.length = cnt x.2)
      ((sends.take m).flatMap fun c => c.sends.map fun s => (c, s)) pack := by
  unfold packListOf at hp
  obtain ⟨⟨st, chains⟩, _, hp⟩ := exc_bind hp
  dsimp -zeta only at hp
  obtain ⟨sends', hs', hp⟩ := exc_bind hp
  obtain rfl : sends' = sends := Except.ok.inj (hs'.symm.trans hs)
  obtain ⟨per, hper, hp⟩ := exc_bind hp
  cases hp
  refine ⟨chains.length, rel_flat (R := fun x e => e.2.length = cnt x) ?_⟩
  refine mapM_zip_rel _ _ (fun c d L hL => ?_) _ _ _ hper
  dsimp -zeta only at hL
  extract_lets smp at hL
  split at hL
  · rename_i hlen
    obtain ⟨_, _, hL⟩ := exc_bind hL
    have h1 := mapM_zip_rel _ (fun (x : Sending) (e : Codes × List (OracleShape × Nat)) =>
      e.2.length = cnt x) (fun o x e he => ?_) _ _ _ hL
    · rw [eq_of_beq hlen, List.take_length] at h1
      exact h1
    · dsimp -zeta only at he
      extract_lets at_ sampled o' at he
      split at he
      · rename_i hl2
        obtain ⟨_, _, he⟩ := exc_bind he
        obtain ⟨l, hl, he⟩ := exc_bind he
        have h2 := (mapM_zip_rel _ (fun _ _ => True) (fun _ _ _ _ => trivial) _ _ _ hl).length_eq
        have hfin : e.2 = l := by
          dsimp only at he
          split at he
          · obtain ⟨_, _, he⟩ := exc_bind he
            split at he
            · obtain ⟨_, _, he⟩ := exc_bind he
              cases he
              rfl
            · obtain ⟨_, e', _⟩ := exc_bind he
              cases e'
          · obtain ⟨_, e', _⟩ := exc_bind he
            cases e'
        rw [hfin, ← h2, List.length_take, eq_of_beq hl2, Nat.min_self]
        simp only [sampled, List.length_map]
        rfl
      · obtain ⟨_, e', _⟩ := exc_bind he
        cases e'
  · obtain ⟨_, e', _⟩ := exc_bind hL
    cases e'

/-- Is it the proof file's first chain's list? -/
def isFirst (c : ChainSends) : Bool := c.file == "proof" && c.chain == 0

theorem filter_tag (c : ChainSends) :
    ((c.sends.map fun s => (c, s)).filter fun a => isFirst a.1) =
      if isFirst c then c.sends.map fun s => (c, s) else [] := by
  rw [List.filter_map]
  cases h : isFirst c
  · simp [Function.comp_def, h]
  · simp [Function.comp_def, h]

/-- **The first chain's rows: one for each sending, in order, each with as many sampled messages
as the sending has messages with an answer.** -/
theorem rows_first {pol lay KL : ByteArray} {rows : List SendRow}
    {k0 k1 k2 e p0 p1 p2 : ChainSends} (hr : sendRowsOf pol lay KL = .ok rows)
    (hs : sendsOf pol lay KL = .ok [k0, k1, k2, e, p0, p1, p2])
    (t0 : isFirst k0 = false) (t1 : isFirst k1 = false) (t2 : isFirst k2 = false)
    (t3 : isFirst e = false) (t4 : isFirst p0 = true) (t5 : isFirst p1 = false)
    (t6 : isFirst p2 = false) :
    (firstRows rows).map (·.sampled.length) = p0.sends.map cnt := by
  unfold sendRowsOf at hr
  obtain ⟨sends', hs', hr⟩ := exc_bind hr
  obtain rfl : sends' = _ := Except.ok.inj (hs'.symm.trans hs)
  obtain ⟨pack, hp, hr⟩ := exc_bind hr
  dsimp -zeta only at hr
  extract_lets flat at hr
  split at hr
  · rename_i hlen
    obtain ⟨_, _, hr⟩ := exc_bind hr
    cases hr
    obtain ⟨m, hF⟩ := pack_aligned hp hs
    -- the whole list is aligned
    have hsplit : flat = (([k0, k1, k2, e, p0, p1, p2].take m).flatMap fun c =>
        c.sends.map fun s => (c, s)) ++ (([k0, k1, k2, e, p0, p1, p2].drop m).flatMap fun c =>
        c.sends.map fun s => (c, s)) := by
      rw [← List.flatMap_append, List.take_append_drop]
    have hl := hF.length_eq
    have hz : (([k0, k1, k2, e, p0, p1, p2].drop m).flatMap fun c =>
        c.sends.map fun s => (c, s)) = [] := by
      apply List.eq_nil_of_length_eq_zero
      have h1 := congrArg List.length hsplit
      rw [List.length_append, hl, eq_of_beq hlen] at h1
      omega
    rw [hz, List.append_nil] at hsplit
    rw [← hsplit] at hF
    obtain ⟨hle, hzip⟩ := List.forall₂_iff_zip.1 hF
    -- the rows of the first chain
    have e1 : firstRows ((flat.zip pack).map fun x => match x with
        | ((c, s), p) => (⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
            (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow)) =
        ((flat.zip pack).filter fun z => isFirst z.1.1).map fun x => match x with
        | ((c, s), p) => (⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
            (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow) := by
      unfold firstRows
      rw [List.filter_map]
      rfl
    rw [e1, List.map_map]
    have e2 : ((flat.zip pack).filter fun z => isFirst z.1.1).map
        ((fun r : SendRow => r.sampled.length) ∘ fun x => match x with
        | ((c, s), p) => (⟨c.file, c.chain, s.entry, s.label, c.codes, p.2,
            (s.sent.filter fun m => m.shape.answers == 0).map (·.shape)⟩ : SendRow)) =
        ((flat.zip pack).filter fun z => isFirst z.1.1).map fun z => cnt z.1.2 := by
      refine List.map_congr_left fun z hz => ?_
      obtain ⟨⟨c, s⟩, p⟩ := z
      exact hzip (List.mem_filter.1 hz).1
    rw [e2]
    have e3 : ((flat.zip pack).filter fun z => isFirst z.1.1).map (fun z => cnt z.1.2) =
        (((flat.zip pack).map (·.1)).filter fun a => isFirst a.1).map fun a => cnt a.2 := by
      rw [List.filter_map, List.map_map]
      rfl
    rw [e3, List.map_fst_zip (Nat.le_of_eq hle)]
    have e4 : (flat.filter fun a => isFirst a.1) = p0.sends.map fun s => (p0, s) := by
      simp only [flat, List.flatMap_cons, List.flatMap_nil, List.filter_append, filter_tag, t0, t1,
        t2, t3, t4, t5, t6, List.filter_nil, List.append_nil, List.nil_append, if_true,
        Bool.false_eq_true, if_false]
    rw [e4, List.map_map]
    rfl
  · obtain ⟨_, e', _⟩ := exc_bind hr
    cases e'

/-- At rad := the rows' own, the test says only that the rows have a radius. -/
theorem radIsB_of_some (rows : List SendRow) (n : Nat) (ps : List PSeat)
    (h : ∀ k, k < n → ∀ i, i < (mineAt ps k).length → (rad? rows k i).isSome = true) :
    radIsB rows n (radOf rows) ps = true := by
  unfold radIsB
  simp only [List.all_eq_true, List.mem_range]
  intro k hk i hi
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h k hk i hi)
  unfold radOf
  rw [hv]
  simp

/-- From the rows' lengths to "has a radius". -/
theorem rad_some {rows : List SendRow} {l : List Nat}
    (h : (firstRows rows).map (·.sampled.length) = l) {k i c : Nat} (hk : l[k]? = some c)
    (hi : i < c) : (rad? rows k i).isSome = true := by
  rw [← h, List.getElem?_map] at hk
  obtain ⟨r, hr, hc⟩ := Option.map_eq_some_iff.1 hk
  unfold rad?
  rw [hr]
  have hi' : i < r.sampled.length := by rw [hc]; exact hi
  simp [List.getElem?_eq_getElem hi']

/-! ## The plan's entries of one sending -/

theorem filter_range_len {α : Type} (d : α) (p : α → Bool) : ∀ l : List α,
    ((List.range l.length).filter fun i => p (l.getD i d)).length = (l.filter p).length
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons,
      List.filter_map, List.getD_cons_zero]
    have ih := filter_range_len d p l
    have e : ((List.range l.length).filter ((fun i => p ((a :: l).getD i d)) ∘ Nat.succ)) =
        (List.range l.length).filter fun i => p (l.getD i d) := rfl
    rw [e]
    cases p a
    · simpa using ih
    · simpa using ih

theorem flat_beyond {α β : Type} (H : α × Nat → List β) (k : Nat)
    (h0 : ∀ s j, j ≠ k → H (s, j) = []) :
    ∀ (L : List α) (n : Nat), k < n → (L.zipIdx n).flatMap H = []
  | [], _, _ => rfl
  | a :: L, n, hn => by
    rw [List.zipIdx_cons, List.flatMap_cons, h0 a n (by omega), List.nil_append]
    exact flat_beyond H k h0 L (n + 1) (by omega)

theorem flat_at {α β : Type} (H : α × Nat → List β) (k : Nat) (c : α → Nat)
    (h0 : ∀ s j, j ≠ k → H (s, j) = []) (hk : ∀ s, (H (s, k)).length ≤ c s) :
    ∀ (L : List α) (n : Nat), n ≤ k →
      ((L.zipIdx n).flatMap H).length ≤ ((L[k - n]?).map c).getD 0
  | [], _, _ => Nat.zero_le _
  | a :: L, n, hn => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append]
    rcases Nat.eq_or_lt_of_le hn with e | hlt
    · subst e
      rw [flat_beyond H n h0 L (n + 1) (by omega), Nat.sub_self]
      exact hk a
    · rw [h0 a n (by omega)]
      have ih := flat_at H k c h0 hk L (n + 1) hlt
      have e : k - n = (k - (n + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      simpa using ih

/-- **The plan's entries with a sample of sending k are at most as many as that sending's messages
with an answer.** -/
theorem mine_le (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (k : Nat) :
    (mineAt (planSeats Z dl) k).length ≤ ((Z.made.proof.1.sends[k]?).map cnt).getD 0 := by
  unfold mineAt planSeats
  dsimp only
  rw [List.filter_flatMap]
  have h := flat_at (fun x : Sending × Nat =>
      (match layTrees Z.made.proof.1.codes x.1.sent.toArray with
      | none => ([] : List PSeat)
      | some lay =>
        (List.range x.1.sent.length).map fun i =>
          ({ label := x.1.label, send := x.2
             seg := P5T.segOf ((reqGroups Z.first.shape).toList.length + 1) 16 x.1.label, idx := i
             j := P5T.rootsBefore dl (x.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0
             shape := (x.1.sent.getD i default).shape
             role := (match P5T.segOf ((reqGroups Z.first.shape).toList.length + 1) 16
                 x.1.label with
               | some (l, m) => P5T.rolesOf Z.first.shape (reqGroups Z.first.shape).toList l m
               | none => []).getD i P5T.Role.other } : PSeat)).filter
        fun p : PSeat => p.send == k && p.smpd) k cnt ?_ ?_ Z.made.proof.1.sends 0 (Nat.zero_le _)
  · rw [Nat.sub_zero] at h
    exact h
  · intro s j hj
    dsimp only
    split
    · rfl
    · rw [List.filter_map, List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro i _
      simp [Function.comp_def, hj]
  · intro s
    dsimp only
    split
    · exact Nat.zero_le _
    · rw [List.filter_map, List.length_map]
      refine Nat.le_of_eq ?_
      unfold cnt
      rw [← filter_range_len default (fun m : OracleNotice => decide (0 < m.shape.answers)) s.sent]
      congr 1
      refine List.filter_congr fun i _ => ?_
      simp [Function.comp_def, PSeat.smpd]

/-! ## The seven lists' names -/

/-- Of the seven lists the fifth alone is the proof file's first chain's. -/
theorem sendsFrom_tags {c : Configured} {k0 k1 k2 e p0 p1 p2 : ChainSends}
    (h : VerifiableInference.Number.sendsFrom c = .ok [k0, k1, k2, e, p0, p1, p2]) :
    isFirst k0 = false ∧ isFirst k1 = false ∧ isFirst k2 = false ∧ isFirst e = false ∧
      isFirst p0 = true ∧ isFirst p1 = false ∧ isFirst p2 = false := by
  unfold VerifiableInference.Number.sendsFrom at h
  extract_lets z a one K B x at h
  have hone : ∀ (f : String) (ch : Nat) (cs : Codes) (L : List Listed) (P : Planned)
      (k : ChainSends), one f ch cs L P = .ok k → k.file = f ∧ k.chain = ch := by
    intro f ch cs L P k hk
    simp only [one] at hk
    split at hk
    · obtain ⟨_, _, hk⟩ := exc_bind hk
      obtain ⟨out, _, hk⟩ := exc_bind hk
      cases hk
      exact ⟨rfl, rfl⟩
    · obtain ⟨_, e', _⟩ := exc_bind hk
      cases e'
  split at h
  · obtain ⟨w1, _, h⟩ := exc_bind h
    obtain ⟨s1, _, h⟩ := exc_bind h
    obtain ⟨w2, _, h⟩ := exc_bind h
    obtain ⟨s2, _, h⟩ := exc_bind h
    rw [List.mapM_cons] at h
    obtain ⟨a0, h0, h⟩ := exc_bind h
    obtain ⟨r0, hr0, h⟩ := exc_bind h
    cases h
    rw [List.mapM_cons] at hr0
    obtain ⟨a1, h1, hr0⟩ := exc_bind hr0
    obtain ⟨r1, hr1, hr0⟩ := exc_bind hr0
    cases hr0
    rw [List.mapM_cons] at hr1
    obtain ⟨a2, h2, hr1⟩ := exc_bind hr1
    obtain ⟨r2, hr2, hr1⟩ := exc_bind hr1
    cases hr1
    rw [List.mapM_cons] at hr2
    obtain ⟨a3, h3, hr2⟩ := exc_bind hr2
    obtain ⟨r3, hr3, hr2⟩ := exc_bind hr2
    cases hr2
    rw [List.mapM_cons] at hr3
    obtain ⟨a4, h4, hr3⟩ := exc_bind hr3
    obtain ⟨r4, hr4, hr3⟩ := exc_bind hr3
    cases hr3
    rw [List.mapM_cons] at hr4
    obtain ⟨a5, h5, hr4⟩ := exc_bind hr4
    obtain ⟨r5, hr5, hr4⟩ := exc_bind hr4
    cases hr4
    rw [List.mapM_cons] at hr5
    obtain ⟨a6, h6, hr5⟩ := exc_bind hr5
    obtain ⟨r6, _, hr5⟩ := exc_bind hr5
    cases hr5
    obtain ⟨f0, c0⟩ := hone _ _ _ _ _ _ h0
    obtain ⟨f1, c1⟩ := hone _ _ _ _ _ _ h1
    obtain ⟨f2, c2⟩ := hone _ _ _ _ _ _ h2
    obtain ⟨f3, c3⟩ := hone _ _ _ _ _ _ h3
    obtain ⟨f4, c4⟩ := hone _ _ _ _ _ _ h4
    obtain ⟨f5, c5⟩ := hone _ _ _ _ _ _ h5
    obtain ⟨f6, c6⟩ := hone _ _ _ _ _ _ h6
    unfold isFirst
    rw [f0, f1, f2, f3, f4, f5, f6, c0, c1, c2, c3, c4, c5, c6]
    decide
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mine_le
#print axioms VerifiableInference.Desc.LinkJoin.sendsFrom_tags
#print axioms VerifiableInference.Desc.LinkJoin.pack_aligned
#print axioms VerifiableInference.Desc.LinkJoin.rows_first
#print axioms VerifiableInference.Desc.LinkJoin.radIsB_of_some
#print axioms VerifiableInference.Desc.LinkJoin.rad_some
