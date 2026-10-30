-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadWalks.lean: the vertices that the program's reader has met in the openings of a
chain: whole paths can be read off them, and under one root no vertex has two values, also across
two openings and across the chains of one file.

Statements and proofs. The reader of an opening walks from the opened leaves to a root and hands
out every vertex that it has met, as (depth, place, value) (`Fmt.OpenOut.seen`). Run/WalkPaths.lean
says what that list is. The chain's reader enters the vertices of each opening into a record that
is kept root by root (`Fmt.addSeen`), and refuses if a vertex gets a second value under its root;
the record goes on from chain to chain within one verdict.

Main names:
  `Walked h cfg y`: the opening y is what the reader of an opening has handed out, at the hash h.
  `OneValue l`: no vertex has two values in the list l.
  `walked_one`, `walked_paths`, `walked_full`: in one opening no vertex has two values; at every
    listed position the look-up of a whole path (`Run.pathFrom`) returns, with as many entries as
    the tree is deep. No more is said of the paths here: what their entries are is in
    OnBytes/Maker/ReadNodes.lean, and that a leaf climbs along one to the root in the library's
    `Run.WalkTie.opening_paths` (Run/WalkPaths.lean).
  `Entered sn l sn'`: the openings l were entered into the record sn one after the other, and sn'
    came of it.
  `readX_entered`, `readChain_entered`: of a chain that was read: each opening is `Walked`, and all
    of them, in the file's order, were entered into the record with which the reading began.
  `recAt sn root`: what a record holds under a root. `Kept sn`: under each root no vertex has two
    values.
  `entered_kept`: entering keeps `Kept`, loses nothing, and holds each entered opening's vertices
    under that opening's root.
  `same_root_agree`: so two openings that were entered into one record, at whichever chains, and
    have one root, give one value to each vertex below the root.
  `three_walks`: both at the three chains of one file, read one after the other.
Limits: the root is the one to which the reader's walk led; that two openings of one tree have one
root is a hypothesis of `same_root_agree` (OnBytes/Maker/OneRoot.lean and SrcFitsOf.lean
prove it from a reading). That a
vertex's value is the hash of its children's is not stated in this file. Nothing on soundness (index
binding included), what a root fixes beyond the reader's record, opening-form binding, no two
openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.ReadFacts
import Run.WalkPaths

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie _root_.Run.WalkTie Octopus

/-- An opening as a reader holds it. -/
abbrev OpenedY : Type := Fmt.Shape × List ℕ × Fmt.OpenOut

/-- No vertex has two values. -/
def OneValue (l : List (ℕ × ℕ × ByteArray)) : Prop :=
  ∀ u ∈ l, ∀ v ∈ l, u.1 = v.1 → u.2.1 = v.2.1 → u.2.2 = v.2.2

/-- The opening is what the reader of an opening has handed out. -/
def Walked (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray) (y : OpenedY) :
    Prop :=
  ∃ (f : Fmt.Fld) (salt : ℕ) (start b : ByteArray) (i : ℕ),
    Fmt.readOpeningW (m := Id) h cfg f salt y.1 start y.2.1 b i = some y.2.2

/-! ## One opening -/

/-- A member of a list has a partner in a list of the same length. -/
theorem mem_zip_left {α β : Type} : ∀ (l : List α) (m : List β), l.length = m.length →
    ∀ x ∈ l, ∃ v, (x, v) ∈ l.zip m
  | [], _, _, _, hx => by cases hx
  | _ :: _, [], e, _, _ => by cases e
  | a :: l, b :: m, e, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨b, List.mem_cons_self⟩
    · obtain ⟨v, hv⟩ := mem_zip_left l m (Nat.succ.inj e) x hx
      exact ⟨v, List.mem_cons_of_mem _ hv⟩

/-- A function that returns at each member returns at the list. -/
theorem mapM_some {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y) →
    ∃ ys, l.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | a :: l, hl => by
    obtain ⟨y, hy⟩ := hl a List.mem_cons_self
    obtain ⟨ys, hys⟩ := mapM_some f l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    exact ⟨y :: ys, by rw [List.mapM_cons, hy, hys]; rfl⟩

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)

/-- In one opening no vertex has two values, and every listed position has a whole path of the
tree's depth. -/
theorem walked_facts {y : OpenedY} (W : Walked h cfg y) :
    OneValue y.2.2.seen ∧
      ∀ x ∈ y.2.1, ∃ p, pathFrom y.1.a y.2.2.seen x = some p ∧ p.length = y.1.a := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨hl, r1, r2, r3, r4, r5⟩ := reader_seen h cfg f salt y.1 start y.2.1 b i y.2.2 e
  obtain ⟨-, hp, -⟩ := listOK_spec y.1.a y.2.1 hl
  have hu1 := listOK_one y.1.a y.2.1 hl
  have hlen : (leafV h y.1 start y.2.1 (y.2.2.cols.zip y.2.2.salts)).length = y.2.1.length :=
    length_leafV h y.1 start y.2.1 _ (by rw [List.length_zip, r1, r2, Nat.min_self])
  have hn : need y.1.a y.2.1 ≤ y.2.2.given.length := le_of_eq r3.symm
  have hmem : ∀ x,
      x ∈ y.2.2.seen ↔
      InLv (fun l r => h 166 0 0 cfg (l ++ r)) y.1.a y.2.1
        (leafV h y.1 start y.2.1 (y.2.2.cols.zip y.2.2.salts)) y.2.2.given x.1 (x.2.1, x.2.2) :=
    fun x => by rw [r5]; exact mem_seen_iff _ _ _ _ _ x
  have hone : OneValue y.2.2.seen := fun u hu v hv e1 e2 =>
    InLv_unique _ y.1.a y.2.1 _ y.2.2.given hp hlen hn hu1 u.1 (u.2.1, u.2.2) (v.2.1, v.2.2)
      ((hmem u).1 hu) (by rw [e1]; exact (hmem v).1 hv) e2
  refine ⟨hone, fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := mem_zip_left y.2.1 _ hlen.symm x hx
  obtain ⟨p, h1, h2, -⟩ := paths_ind (fun l r => h 166 0 0 cfg (l ++ r)) y.2.2.seen hone
    y.1.a y.2.1 _ y.2.2.given hp hlen hn (fun d' e' hi => (hmem (d', e'.1, e'.2)).2 hi) (x, v) hv
  exact ⟨p.map bytesToDig, h1, by rw [List.length_map]; exact PathOK_length _ _ _ _ _ _ p h2⟩

theorem walked_one {y : OpenedY} (W : Walked h cfg y) : OneValue y.2.2.seen :=
  (walked_facts h cfg W).1

theorem walked_paths {y : OpenedY} (W : Walked h cfg y) :
    ∀ x ∈ y.2.1, ∃ p, pathFrom y.1.a y.2.2.seen x = some p ∧ p.length = y.1.a :=
  (walked_facts h cfg W).2

/-- **The whole paths of all listed positions are there.** -/
theorem walked_full {y : OpenedY} (W : Walked h cfg y) :
    ∃ ps, y.2.1.mapM (pathFrom y.1.a y.2.2.seen) = some ps :=
  mapM_some _ _ fun x hx => (walked_paths h cfg W x hx).imp fun _ hp => hp.1

end

/-! ## The record, from opening to opening -/

/-- The openings were entered into the record one after the other. -/
inductive Entered : Fmt.Seen → List OpenedY → Fmt.Seen → Prop
  | nil (sn : Fmt.Seen) : Entered sn [] sn
  | cons {sn sn1 sn' : Fmt.Seen} {y : OpenedY} {l : List OpenedY}
      (e : Fmt.addSeen y.2.2.root (Fmt.entered y.2.2.seen) sn = some sn1)
      (t : Entered sn1 l sn') : Entered sn (y :: l) sn'

theorem Entered.append {sn sn1 sn' : Fmt.Seen} {l l' : List OpenedY} (a : Entered sn l sn1)
    (b : Entered sn1 l' sn') : Entered sn (l ++ l') sn' := by
  induction a with
  | nil _ => exact b
  | cons e _ ih => exact .cons e (ih b)

section
variable (h : HId)

/-- The stored tables' openings behind one draw of positions. -/
theorem stored_entered (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : ℕ) (l : List OpenedY) (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
    (∀ y ∈ l, Walked h cfg y) ∧ Entered sn l sn'
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, rfl, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨fun y hy => (by cases hy), .nil _⟩
  | t :: ts, sn, i, l, sn', k, e => by
      unfold Fmt.readStored at e
      simp only [idb] at e
      cases ho : Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
          (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
      | none => rw [ho] at e; cases e
      | some o =>
        rw [ho] at e
        dsimp only at e
        split at e
        · split at e
          · cases e
          · rename_i sn1 hadd
            cases hrec : Fmt.readStored (m := Id) h cfg statement P poss b ts sn1 o.next with
            | none => rw [hrec] at e; cases e
            | some z =>
              rw [hrec] at e
              obtain ⟨l1, sn2, k1⟩ := z
              simp only [idp] at e
              obtain ⟨rfl, rfl, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
              obtain ⟨w, en⟩ := stored_entered cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec
              refine ⟨fun y hy => ?_, .cons hadd en⟩
              rcases List.mem_cons.1 hy with rfl | hy
              · exact ⟨P.field, t.salt, cfg, b, i, ho⟩
              · exact w y hy
        · cases e

/-- The trees' openings behind one draw of positions. -/
theorem opens_entered (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Fmt.Shape × Fmt.Src)) (sn : Fmt.Seen) (i : ℕ) (l : List OpenedY)
      (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
    (∀ y ∈ l, Walked h cfg y) ∧ Entered sn l sn'
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, rfl, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨fun y hy => (by cases hy), .nil _⟩
  | (sh, src) :: os, sn, i, l, sn', k, e => by
      unfold Fmt.readOpens at e
      dsimp only at e
      split at e
      · cases e
      · rename_i root start hrs
        simp only [idb] at e
        cases ho : Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
            (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => rw [ho] at e; cases e
        | some o =>
          rw [ho] at e
          dsimp only at e
          split at e
          · rename_i hroot
            split at e
            · cases e
            · rename_i sn1 hadd
              cases hrec : Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1 o.next with
              | none => rw [hrec] at e; cases e
              | some z =>
                rw [hrec] at e
                obtain ⟨l1, sn2, k1⟩ := z
                simp only [idp] at e
                obtain ⟨rfl, rfl, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
                obtain ⟨w, en⟩ := opens_entered cfg P run roots poss b os sn1 o.next l1 sn2 k1 hrec
                rw [← bytes_beq _ _ hroot] at hadd
                refine ⟨fun y hy => ?_, .cons hadd en⟩
                rcases List.mem_cons.1 hy with rfl | hy
                · exact ⟨P.field, P.salt, start, b, i, ho⟩
                · exact w y hy
          · cases e

/-- One round of the strict reader. -/
theorem roundX_entered (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro : Fmt.RoundOut, s'.out = s.out.push ro ∧ (∀ y ∈ ro.opens, Walked h cfg y) ∧
      Entered s.seen ro.opens s'.seen := by
  unfold Fmt.roundX at e
  split at e
  · cases e
  · rename_i msg hmsg
    split at e
    · cases e
    · rename_i vals hvals
      split at e
      · cases e
      · rename_i nonce i1 hnon
        simp only [idb] at e
        cases hq : Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          split at e
          · cases e
          · rename_i u i2 hlist
            cases hs : Fmt.readStored (m := Id) h cfg statement P
                (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b ts s.seen i2 with
            | none => rw [hs] at e; cases e
            | some y =>
              rw [hs] at e
              obtain ⟨colsS, sn1, i2'⟩ := y
              dsimp only at e
              cases ho : Fmt.readOpens (m := Id) h cfg P run
                  (s.roots ++ (Fmt.rootsOf vals).toArray)
                  (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn1
                  i2' with
              | none => rw [ho] at e; cases e
              | some z =>
                rw [ho] at e
                obtain ⟨cols, sn2, i3⟩ := z
                simp only [idp] at e
                obtain rfl := Option.some.inj e
                obtain ⟨w1, e1⟩ :=
                  stored_entered h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs
                obtain ⟨w2, e2⟩ := opens_entered h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho
                refine ⟨⟨msg, vals, nonce, _, _, colsS ++ cols⟩, rfl, fun y hy => ?_, e1.append e2⟩
                rcases List.mem_append.1 hy with hy | hy
                · exact w1 y hy
                · exact w2 y hy

/-- All rounds of a chain. -/
theorem foldX_entered (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
    Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
    ∃ ros : List Fmt.RoundOut, s'.out.toList = s.out.toList ++ ros ∧
      (∀ ro ∈ ros, ∀ y ∈ ro.opens, Walked h cfg y) ∧
      Entered s.seen (ros.flatMap (·.opens)) s'.seen
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, fun ro hro => (by cases hro), .nil _⟩
  | r :: rs, s, s', e => by
      simp only [Fmt.foldRoundsX, idb] at e
      cases hc : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2, h3⟩ := roundX_entered h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨ros, g1, g2, g3⟩ := foldX_entered cfg statement P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, fun ro' hro' => ?_, ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rcases List.mem_cons.1 hro' with rfl | hro'
          · exact h2
          · exact g2 ro' hro'
        · rw [List.flatMap_cons]
          exact h3.append g3

/-- **A chain that the strict reader has read.** -/
theorem readX_entered (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    (∀ ro ∈ o.rounds.toList, ∀ y ∈ ro.opens, Walked h S.base.cfg y) ∧
      Entered seen (o.rounds.toList.flatMap (·.opens)) o.seen := by
  obtain ⟨-, x, i0, hd, s, -, -, hf, rfl, -⟩ := readX_stages h S seen b i o j e
  obtain ⟨ros, g1, g2, g3⟩ := foldX_entered h _ _ _ _ b _ _ s hf
  have hr : s.out.toList = ros := g1
  show (∀ ro ∈ s.out.toList, _) ∧ Entered seen (s.out.toList.flatMap (·.opens)) s.seen
  rw [hr]
  exact ⟨g2, g3⟩

end

/-- **The same of the reader that the program runs.** -/
theorem readChain_entered (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    (∀ ro ∈ o.rounds.toList, ∀ y ∈ ro.opens, Walked Fmt.formatHash S.base.cfg y) ∧
      Entered seen (o.rounds.toList.flatMap (·.opens)) o.seen :=
  readX_entered Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e)

/-! ## What a record holds -/

/-- What a record holds under a root. -/
def recAt : Fmt.Seen → ByteArray → List (ℕ × ℕ × ByteArray)
  | [], _ => []
  | (r, old) :: l, root => if r == root then old else recAt l root

/-- Under each root no vertex has two values. -/
def Kept (sn : Fmt.Seen) : Prop := ∀ root, OneValue (recAt sn root)

theorem beq_false_of_ne {a b : ByteArray} (hne : a ≠ b) : (a == b) = false := by
  cases hb : a == b with
  | false => rfl
  | true => exact absurd (bytes_beq a b hb) hne

/-- What `Fmt.agree` tests. -/
theorem agree_spec {old new : List (ℕ × ℕ × ByteArray)} (h : Fmt.agree old new = true) :
    ∀ o ∈ old, ∀ v ∈ new, o.1 = v.1 → o.2.1 = v.2.1 → o.2.2 = v.2.2 := by
  intro o ho v hv e1 e2
  unfold Fmt.agree at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h v hv) o ho
  rw [e1, e2] at h1
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at h1
  exact bytes_beq _ _ h1

/-- What entering does to a record. -/
theorem addSeen_rec (root : ByteArray) (new : List (ℕ × ℕ × ByteArray)) :
    ∀ (sn sn' : Fmt.Seen), Fmt.addSeen root new sn = some sn' →
    Fmt.agree (recAt sn root) new = true ∧ recAt sn' root = recAt sn root ++ new ∧
      ∀ r, r ≠ root → recAt sn' r = recAt sn r
  | [], sn', e => by
    obtain rfl := Option.some.inj e
    refine ⟨by simp [Fmt.agree, recAt], ?_, fun r hr => ?_⟩
    · show (if root == root then new else []) = [] ++ new
      rw [bytes_beq_self, if_pos rfl]
      rfl
    · show (if root == r then new else []) = []
      rw [beq_false_of_ne (Ne.symm hr)]
      rfl
  | (r0, old) :: l, sn', e => by
    unfold Fmt.addSeen at e
    by_cases h0 : (r0 == root) = true
    · rw [if_pos h0] at e
      have e0 : r0 = root := bytes_beq _ _ h0
      split at e
      · rename_i hag
        obtain rfl := Option.some.inj e
        refine ⟨?_, ?_, fun r hr => ?_⟩
        · show Fmt.agree (if r0 == root then old else recAt l root) new = true
          rw [if_pos h0]
          exact hag
        · show (if r0 == root then old ++ new else recAt l root) =
            (if r0 == root then old else recAt l root) ++ new
          rw [if_pos h0, if_pos h0]
        · show (if r0 == r then old ++ new else recAt l r) = if r0 == r then old else recAt l r
          rw [beq_false_of_ne (by rw [e0]; exact Ne.symm hr)]
          rfl
      · cases e
    · rw [if_neg h0] at e
      cases hl : Fmt.addSeen root new l with
      | none => rw [hl] at e; cases e
      | some l' =>
        rw [hl] at e
        obtain rfl := Option.some.inj e
        obtain ⟨a1, a2, a3⟩ := addSeen_rec root new l l' hl
        refine ⟨?_, ?_, fun r hr => ?_⟩
        · show Fmt.agree (if r0 == root then old else recAt l root) new = true
          rw [if_neg h0]
          exact a1
        · show (if r0 == root then old else recAt l' root) =
            (if r0 == root then old else recAt l root) ++ new
          rw [if_neg h0, if_neg h0]
          exact a2
        · show (if r0 == r then old else recAt l' r) = if r0 == r then old else recAt l r
          rw [a3 r hr]

theorem OneValue.append {old new : List (ℕ × ℕ × ByteArray)} (a : OneValue old) (b : OneValue new)
    (h : Fmt.agree old new = true) : OneValue (old ++ new) := by
  intro u hu v hv e1 e2
  rcases List.mem_append.1 hu with hu | hu <;> rcases List.mem_append.1 hv with hv | hv
  · exact a u hu v hv e1 e2
  · exact agree_spec h u hu v hv e1 e2
  · exact (agree_spec h v hv u hu e1.symm e2.symm).symm
  · exact b u hu v hv e1 e2

theorem OneValue.entered {l : List (ℕ × ℕ × ByteArray)} (a : OneValue l) :
    OneValue (Fmt.entered l) := fun u hu v hv =>
  a u (List.mem_of_mem_filter hu) v (List.mem_of_mem_filter hv)

/-- **Entering keeps the record in order, loses nothing, and holds each entered opening's vertices
under that opening's root.** -/
theorem entered_kept {sn sn' : Fmt.Seen} {l : List OpenedY} (E : Entered sn l sn') :
    Kept sn → (∀ y ∈ l, OneValue y.2.2.seen) →
    Kept sn' ∧ (∀ root, ∀ u ∈ recAt sn root, u ∈ recAt sn' root) ∧
      ∀ y ∈ l, ∀ u ∈ Fmt.entered y.2.2.seen, u ∈ recAt sn' y.2.2.root := by
  induction E with
  | nil sn => exact fun k _ => ⟨k, fun _ _ hu => hu, fun y hy => by cases hy⟩
  | @cons sn sn1 sn' y l e _ ih =>
    intro k ho
    obtain ⟨a1, a2, a3⟩ := addSeen_rec _ _ sn sn1 e
    have k1 : Kept sn1 := by
      intro root
      by_cases hr : root = y.2.2.root
      · rw [hr, a2]
        exact (k _).append (ho y List.mem_cons_self).entered a1
      · rw [a3 root hr]
        exact k root
    have m1 : ∀ root, ∀ u ∈ recAt sn root, u ∈ recAt sn1 root := by
      intro root u hu
      by_cases hr : root = y.2.2.root
      · rw [hr, a2]
        exact List.mem_append_left _ (hr ▸ hu)
      · rw [a3 root hr]
        exact hu
    obtain ⟨b1, b2, b3⟩ := ih k1 fun y' hy' => ho y' (List.mem_cons_of_mem _ hy')
    refine ⟨b1, fun root u hu => b2 root u (m1 root u hu), fun y' hy' u hu => ?_⟩
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact b2 _ u (by rw [a2]; exact List.mem_append_right _ hu)
    · exact b3 y' hy' u hu

theorem kept_nil : Kept [] := fun _ u hu => by cases hu

/-- **Two openings that were entered into one record and have one root give one value to each vertex
below the root.** -/
theorem same_root_agree {sn sn' : Fmt.Seen} {l : List OpenedY} (E : Entered sn l sn')
    (k : Kept sn) (ho : ∀ y ∈ l, OneValue y.2.2.seen) (y y' : OpenedY) (hy : y ∈ l) (hy' : y' ∈ l)
    (hr : y.2.2.root = y'.2.2.root) :
    ∀ u ∈ y.2.2.seen, ∀ v ∈ y'.2.2.seen, u.1 ≠ 0 → u.1 = v.1 → u.2.1 = v.2.1 → u.2.2 = v.2.2 := by
  obtain ⟨b1, -, b3⟩ := entered_kept E k ho
  intro u hu v hv h0 e1 e2
  have mu : u ∈ Fmt.entered y.2.2.seen := List.mem_filter.2 ⟨hu, by simpa using h0⟩
  have mv : v ∈ Fmt.entered y'.2.2.seen := List.mem_filter.2 ⟨hv, by simpa using (e1 ▸ h0)⟩
  exact b1 y.2.2.root u (b3 y hy u mu) v (hr ▸ b3 y' hy' v mv) e1 e2

/-! ## The three chains of one file -/

/-- All openings of a chain as read, in the file's order. -/
def opensIn (o : Fmt.ChainOut) : List OpenedY := o.rounds.toList.flatMap (·.opens)

/-- **Three chains that the program's reader has read one after the other**, the first from the
empty record, each later one from the record that the chain before it left: every opening has its
whole paths, and two openings with one root, in whichever chains, give one value to each vertex
below the root. -/
theorem three_walks (S₁ S₂ S₃ : Fmt.SpecX) (b : ByteArray) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (o₁ o₂ o₃ : Fmt.ChainOut) (e₁ : readChain S₁ [] b i₁ = some (o₁, j₁))
    (e₂ : readChain S₂ o₁.seen b i₂ = some (o₂, j₂))
    (e₃ : readChain S₃ o₂.seen b i₃ = some (o₃, j₃)) :
    (∀ y ∈ opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃),
      OneValue y.2.2.seen ∧ ∃ ps, y.2.1.mapM (pathFrom y.1.a y.2.2.seen) = some ps) ∧
    ∀ y ∈ opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃),
      ∀ y' ∈ opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃), y.2.2.root = y'.2.2.root →
      ∀ u ∈ y.2.2.seen, ∀ v ∈ y'.2.2.seen, u.1 ≠ 0 → u.1 = v.1 → u.2.1 = v.2.1 →
        u.2.2 = v.2.2 := by
  obtain ⟨w₁, n₁⟩ := readChain_entered S₁ [] b i₁ o₁ j₁ e₁
  obtain ⟨w₂, n₂⟩ := readChain_entered S₂ o₁.seen b i₂ o₂ j₂ e₂
  obtain ⟨w₃, n₃⟩ := readChain_entered S₃ o₂.seen b i₃ o₃ j₃ e₃
  have W : ∀ y ∈ opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃), ∃ cfg, Walked Fmt.formatHash cfg y := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨ro, hro, hy⟩ := List.mem_flatMap.1 hy
      exact ⟨_, w₁ ro hro y hy⟩
    · rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨ro, hro, hy⟩ := List.mem_flatMap.1 hy
        exact ⟨_, w₂ ro hro y hy⟩
      · obtain ⟨ro, hro, hy⟩ := List.mem_flatMap.1 hy
        exact ⟨_, w₃ ro hro y hy⟩
  have E : Entered [] (opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃)) o₃.seen := n₁.append (n₂.append n₃)
  have O : ∀ y ∈ opensIn o₁ ++ (opensIn o₂ ++ opensIn o₃), OneValue y.2.2.seen := fun y hy => by
    obtain ⟨cfg, w⟩ := W y hy
    exact walked_one Fmt.formatHash cfg w
  refine ⟨fun y hy => ⟨O y hy, ?_⟩,
    fun y hy y' hy' hr => same_root_agree E kept_nil O y y' hy hy' hr⟩
  obtain ⟨cfg, w⟩ := W y hy
  exact walked_full Fmt.formatHash cfg w

end OnBytes.Maker
