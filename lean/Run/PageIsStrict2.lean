-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsStrict2.lean: what the lenient reader reads and the three tests accept, the strict reader
reads too (under the hypotheses told below).

There are two readers of a proof file. The strict reader (Fmt/Rules8.lean, `wholeChain`) is this
library's rendering of the verifier of the format page (docs/format/FORMAT.md, which comes with the
programs, that is,
with the C++ implementation that accompanies this Lean code; here in an edition of the page that is
not the one that ships) up to its decision: it recomputes the hash chain, tests the proof of work,
checks every Merkle opening against its root, and keeps a record (`Fmt.Seen`, Fmt/Rules8.lean) so
that no vertex gets two values under one root (FORMAT.md, R7.14). The lenient reader
(Run/ParseLax.lean, `laxWhole`) only cuts the file into its parts; behind it the compiled verifier
itself tests the proof of work and checks every Merkle opening against its root (`pi_chain`,
`pi_after`, Run/PageIs.lean); it keeps no such record. To cut the file, the lenient reader
recomputes the hash chain, and it refuses some files (what it still asks the hash, what it refuses
and what it does not test: part 1 of the head of Run/ParseLax.lean).
This file proves the statement `Spec.pi_strict2` of Run/PageIs.lean, for a description within the
limits of the generic construction (`Run.PQ.ok`) and a hash function whose answers have the format's
lengths: if the lenient reader reads a file, every proof-of-work test passes (`passL`), every
opening leads to the root that was sent (`rootsAll`), and the roots that the file sends are pairwise
different as byte strings (`rootsDiffer`), then the strict reader reads the file and hands out the
same view (`Fmt.viewOf`, Fmt/M1View.lean).

Why the condition on the roots. The record of R7.14 is kept under a root's 32 bytes. If a file sends
one and the same root for two opened trees, the strict reader compares the vertices of their
openings, and the compiled verifier does not; for an arbitrary hash function the two can then differ
(a reasoning; not stated in Run/ or Fmt/). Where the roots differ, every opening meets a fresh
record, and the record never refuses. The other direction, "what the strict reader reads, the
lenient reader reads, with `passL` and `rootsAll` passed" (`Spec.pi_strict1`, proved in
Run/PageIsReaders.lean), needs no such condition, since a record can only add refusals.

Sources. The statement is that of Run/PageIs.lean. The strict reader stands on R7.14 as this file
reads it, with the record keyed by the root's 32 bytes; this file has not been held against the
format page as it ships,
and may differ from it.
The proof also rests
on the clause of the conditions on a description that bounds the length of a leaf's salt (FORMAT.md,
R7.3). Were that clause no part of Fmt.Spec.ok, the statement would be false without a further
hypothesis: the strict reader alone would test that length, inside the reading of an opening.

1. What the file contains. Theorems with their proofs, and one definition (`ownIx`). No typed
protocol term occurs. The hash function is a variable h in the identity monad.
   `query_strict`: a step of the chain without the proof-of-work test, together with that test
     passed, is the strict step.
   `opening_strict`: what was cut as an opening at an admissible list of positions, with salts of an
     admitted length, the strict reader reads.
   `opens_strict`, `step_strict`, `fold_strict`: each starts from any record whose keys, together
     with the roots of the openings still to come, are pairwise different.
   `strict2`: the whole statement, with "no round has an opening, or the salt's length is admitted"
     and "the roots of the opened trees differ" as hypotheses.

2. What is checked when the file compiles. No tests (#guard) in this file.

3. Theorems. The one that other files use is `pi_strict2`.

4. What is not claimed.
   Nothing about the hash function, and no statement on soundness.
   Nothing about a file that sends one root for two opened trees: there the two readers' verdicts
   are not compared here. `pi_strict2` says nothing about any file that sends one root twice.
   That Fmt/Rules8.lean renders R7.14 in general is not claimed here.
   The record is kept for one chain. A verdict that reads several chains or files (a session in the
   sense of FORMAT.md, R7.14) is not rendered.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageIsReaders
import Run.PageIsTabProofs
import Fmt.Rules8Ok

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src St)

/-! ## The record does not refuse a root that it has not met -/

theorem addSeen_fresh (key : ByteArray) (new : List (ℕ × ℕ × ByteArray)) :
    ∀ sn : _root_.Fmt.Seen,
      key ∉ sn.map Prod.fst → _root_.Fmt.addSeen key new sn = some (sn ++ [(key, new)])
  | [], _ => rfl
  | (r, old) :: l, h => by
      have h1 : r ≠ key := fun e => h (by rw [List.map_cons, e]; exact List.mem_cons_self)
      have h2 : key ∉ l.map Prod.fst := fun e =>
        h (by rw [List.map_cons]; exact List.mem_cons_of_mem _ e)
      unfold _root_.Fmt.addSeen
      rw [if_neg (fun e => h1 (bytes_beq _ _ e)), addSeen_fresh key new l h2]
      rfl

/-! ## The lenient reader against the strict one -/

section
variable (h : HId)

theorem query_strict (c : Chain) (msg : ByteArray) (kind : _root_.Fmt.Kind) (work nonce K : ℕ)
    (c' : Chain) (vb : Array ByteArray)
    (e : laxQueryW (m := Id) h c msg kind work nonce K = some (c', vb))
    (hp : _root_.Fmt.passesA work
        (_root_.Fmt.fetchW (m := Id) h c.label c.rho (c.round + 1)
          msg kind work nonce (_root_.Fmt.firstBlock work + K)) = true) :
    Chain.queryW (m := Id) h c msg kind work nonce K = some (c', vb) := by
  unfold laxQueryW at e
  unfold Chain.queryW
  split at e
  · rename_i hk
    rw [if_pos hk]
    simp only [idb, idp] at e ⊢
    rw [if_pos hp]
    exact e
  · cases e

/-- What was parsed as an opening at an admissible list of positions (`hl`), with salts of an
admitted length (`hsb`), the strict reader reads, with the same columns, salts, given digests and
next place. -/
theorem opening_strict (cfg : ByteArray) (f : _root_.Fmt.Fld) (sb : ℕ) (sh : _root_.Fmt.Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (cs : List (List UInt64 × ByteArray))
    (given : List ByteArray) (next : ℕ)
    (ep : _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, given), next))
    (hl : _root_.Fmt.listOK sh.a xs = true) (hsb : _root_.Fmt.saltLenOK sb = true) :
    ∃ o : OpenOut,
      _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o ∧
      o.cols = cs.map Prod.fst ∧
      o.salts = cs.map Prod.snd ∧
      o.given = given ∧ o.next = next := by
  obtain ⟨l1, l2⟩ := rdOpening_len f sb sh xs b i cs given next ep
  have hu := WalkTie.listOK_one sh.a xs hl
  have l2' : given.length = Octopus.need sh.a xs := l2.trans (WalkTie.places_length sh.a xs hu)
  have hw := WalkTie.walk_id (fun l r => (h 166 0 0 cfg (l ++ r) : ByteArray)) sh.a xs
    (WalkTie.leafV h sh start xs cs) given [] []
    (WalkTie.length_leafV h sh start xs cs l1) (le_of_eq l2'.symm) hu
  unfold _root_.Fmt.readOpeningW
  rw [hl, hsb]
  simp only [Bool.and_self, if_true]
  rw [ep]
  simp only [idb, idp]
  rw [WalkTie.leaves_id h sh start xs cs l1]
  have hw2 : (_root_.Fmt.walkW (m := Id) (fun _ _ l r => _root_.Fmt.vertexW h cfg l r)
          _root_.Fmt.takeGiven sh.a (xs.zip (WalkTie.leafV h sh start xs cs)) (given, []) []).map
        (fun x => (x.1, x.2.1.1)) = some _ := hw
  cases hwv : _root_.Fmt.walkW (m := Id) (fun _ _ l r => _root_.Fmt.vertexW h cfg l r)
      _root_.Fmt.takeGiven sh.a (xs.zip (WalkTie.leafV h sh start xs cs)) (given, []) [] with
  | none => rw [hwv] at hw2; cases hw2
  | some p =>
    exact ⟨⟨cs.map (·.1), cs.map (·.2), given, p.1, p.2.2 ++ p.2.1.2, next⟩,
      rfl, rfl, rfl, rfl, rfl⟩

/-- The openings after one draw. -/
theorem opens_strict (cfg : ByteArray) (P : Plan) (run : ByteArray) (roots : Array ByteArray)
    (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (_root_.Fmt.Shape × Src))
        (sn : _root_.Fmt.Seen) (i : ℕ) (cols : List (_root_.Fmt.Shape × List ℕ × OpenOut)) (k : ℕ),
      (os.isEmpty = true ∨ _root_.Fmt.saltLenOK P.salt = true) → (∀ x ∈ os, ∃ n, x.2 = .own n) →
      (sn.map Prod.fst ++ cols.map fun y => y.2.2.root).Nodup →
      laxOpens P roots poss b os i = some (cols, k) →
      (∀ x ∈ cols, rootOf h cfg run x.1 x.2.1 x.2.2 = x.2.2.root) →
      ∃ (l : List (_root_.Fmt.Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen),
        _root_.Fmt.readOpens (m := Id) h cfg P (some run) roots poss b os sn i = some (l, sn', k) ∧
        (l.map fun x => (x.1, x.2.1, stripO x.2.2)) = cols ∧
        sn'.map Prod.fst = sn.map Prod.fst ++ cols.map fun y => y.2.2.root
  | [], sn, i, cols, k, _, _, _, e, _ => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
      exact ⟨[], sn, rfl, rfl, (List.append_nil _).symm⟩
  | (sh, src) :: os, sn, i, cols, k, hsb0, hown, hnd, e, hroot => by
      have hsb : _root_.Fmt.saltLenOK P.salt = true := hsb0.resolve_left (by simp)
      obtain ⟨n, hn⟩ := hown (sh, src) List.mem_cons_self
      have hn' : src = .own n := hn
      subst hn'
      unfold laxOpens at e
      dsimp only at e
      split at e
      · rename_i r cs gv j hr hl hp
        obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.1 e
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxe
        obtain ⟨o, ho, hc, hs, hg, hnx⟩ :=
          opening_strict h cfg P.field P.salt sh run _ b i cs gv j hp hl hsb
        have hor : o.root = r := by
          rw [(WalkTie.reader_id h cfg P.field P.salt sh run _ b i o ho).2.2.2, hc, hs, hg]
          exact hroot _ List.mem_cons_self
        have hfresh : r ∉ sn.map Prod.fst := by
          intro hm
          rw [List.map_cons] at hnd
          exact (List.nodup_append.1 hnd).2.2 _ hm _ List.mem_cons_self rfl
        have hnd' : ((sn ++ [(r, _root_.Fmt.entered o.seen)]).map Prod.fst ++
            x.1.map fun y => y.2.2.root).Nodup := by
          rw [List.map_append, List.append_assoc]
          exact hnd
        obtain ⟨l, sn', h1, h2, h3⟩ :=
          opens_strict cfg P run roots poss b os (sn ++ [(r, _root_.Fmt.entered o.seen)]) j x.1 x.2
            (Or.inr hsb) (fun y hy => hown y (List.mem_cons_of_mem _ hy)) hnd' hx
            (fun y hy => hroot y (List.mem_cons_of_mem _ hy))
        refine ⟨(sh, _root_.Fmt.listOf (poss.map (· % 2 ^ sh.a)), o) :: l, sn', ?_, ?_, ?_⟩
        · unfold _root_.Fmt.readOpens
          dsimp only
          rw [hr]
          simp only [idb]
          rw [ho]
          dsimp only
          rw [hor, if_pos (bytes_beq_self r), addSeen_fresh _ _ sn hfresh]
          dsimp only
          rw [hnx, h1]
          rfl
        · rw [List.map_cons, h2]
          unfold stripO
          rw [hc, hs, hg, hor, hnx]
        · rw [h3, List.map_append, List.append_assoc]
          rfl
      · cases e

/-- One round. -/
theorem step_strict (cfg : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray) (pos : ℕ)
    (c : Chain) (roots : Array ByteArray) (snL : _root_.Fmt.Seen) (outL : Array RoundOut) (t' : St)
    (r : _root_.Fmt.Round) (hsb : r.opens.isEmpty = true ∨ _root_.Fmt.saltLenOK P.salt = true)
    (hown : ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (e : cutStep (m := Id) h (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _))
        P (some run) b ⟨pos, c, roots, snL, outL⟩ r = some t') :
    ∃ ro : RoundOut,
      t'.out = outL.push ro ∧
      t'.chain = nextOf h c r ro ∧
      t'.seen = snL ∧
      ∀ (sn : _root_.Fmt.Seen) (out : Array RoundOut),
        _root_.Fmt.passesA r.entry.work (rowBs h c r ro) = true →
        (∀ x ∈ ro.opens, rootOf h cfg run x.1 x.2.1 x.2.2 = x.2.2.root) →
        (sn.map Prod.fst ++ ro.opens.map fun y => y.2.2.root).Nodup →
        ∃ (ro' : RoundOut) (sn' : _root_.Fmt.Seen),
          _root_.Fmt.step (m := Id) h cfg P (some run) b ⟨pos, c, roots, sn, out⟩ r =
            some ⟨t'.pos, t'.chain, t'.roots, sn', out.push ro'⟩ ∧
          stripR ro' = ro ∧
          sn'.map Prod.fst = sn.map Prod.fst ++ ro.opens.map fun y => y.2.2.root := by
  unfold cutStep at e
  dsimp only at e
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
        cases hq : laxQueryW (m := Id) h c msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          obtain ⟨-, hc, -⟩ := laxQuery_some h _ _ _ _ _ _ cv.1 cv.2 hq
          split at e
          · cases e
          · rename_i u i2 hlist
            simp only [idp] at e
            split at e
            · cases e
            · rename_i cols i3 hops
              cases e
              refine ⟨⟨msg, vals, nonce, _, _, cols⟩, rfl, hc, rfl, ?_⟩
              intro sn out hpass hroot hnd
              obtain ⟨l, sn', h1, h2, h3⟩ :=
                opens_strict h cfg P run _ _ b r.opens sn i2 cols i3 hsb hown hnd hops hroot
              refine ⟨⟨msg, vals, nonce,
                  _root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2),
                  _root_.Fmt.listOf
                    (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss,
                  l⟩,
                sn', ?_, ?_, h3⟩
              · unfold _root_.Fmt.step
                dsimp only
                rw [hmsg]
                dsimp only
                rw [hvals]
                dsimp only
                rw [hnon]
                simp only [idb]
                rw [query_strict h c msg r.kind r.entry.work nonce _ cv.1 cv.2 hq hpass]
                dsimp only
                rw [hlist]
                dsimp only
                rw [h1]
                rfl
              · unfold stripR
                dsimp only
                rw [h2]

/-- All rounds. -/
theorem fold_strict (cfg : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray) :
    ∀ (rs : List _root_.Fmt.Round) (pos : ℕ) (c : Chain) (roots : Array ByteArray)
        (snL : _root_.Fmt.Seen) (outL : Array RoundOut) (t' : St),
      (∀ r ∈ rs, r.opens.isEmpty = true ∨ _root_.Fmt.saltLenOK P.salt = true) →
      (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) →
      cutFold (m := Id) h (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P
          (some run) b rs ⟨pos, c, roots, snL, outL⟩ = some t' →
      ∃ ros : List RoundOut,
        t'.out.toList = outL.toList ++ ros ∧
        ∀ (sn : _root_.Fmt.Seen) (out : Array RoundOut), passL h rs ros c = true →
          rootsAll h cfg run ros = true →
          (sn.map Prod.fst ++ (ros.flatMap (·.opens)).map fun y => y.2.2.root).Nodup →
          ∃ (ros' : List RoundOut) (s' : St),
            _root_.Fmt.foldRounds (m := Id) h cfg P (some run) b rs ⟨pos, c, roots, sn, out⟩ =
              some s' ∧
            s'.pos = t'.pos ∧
            s'.out.toList = out.toList ++ ros' ∧
            ros'.map stripR = ros
  | [], pos, c, roots, snL, outL, t', _, _, e => by
      obtain rfl := Option.some.inj e
      exact ⟨[],
        (List.append_nil _).symm,
        fun sn out _ _ _ => ⟨[], _, rfl, rfl, (List.append_nil _).symm, rfl⟩⟩
  | r :: rs, pos, c, roots, snL, outL, t', hsb, hown, e => by
      simp only [cutFold, idb] at e
      cases hc : cutStep (m := Id) h
          (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P (some run) b
          ⟨pos, c, roots, snL, outL⟩ r with
      | none => rw [hc] at e; cases e
      | some t1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, a1, a2, a3, a4⟩ :=
          step_strict h cfg P run b pos c roots snL outL t1 r (hsb r List.mem_cons_self)
            (hown r List.mem_cons_self) hc
        obtain ⟨ros, g1, g2⟩ := fold_strict cfg P run b rs t1.pos t1.chain t1.roots t1.seen t1.out
          t' (fun r' hr' => hsb r' (List.mem_cons_of_mem _ hr'))
          (fun r' hr' => hown r' (List.mem_cons_of_mem _ hr')) e
        refine ⟨ro :: ros, ?_, ?_⟩
        · rw [g1, a1, Array.toList_push, List.append_assoc]
          rfl
        · intro sn out hp hr hnd
          have hp' : (_root_.Fmt.passesA r.entry.work (rowBs h c r ro) &&
                passL h rs ros (nextOf h c r ro)) = true := hp
          have hr' : (ro.opens.all (fun x => rootOf h cfg run x.1 x.2.1 x.2.2 == x.2.2.root) &&
                rootsAll h cfg run ros) = true := hr
          rw [Bool.and_eq_true] at hp' hr'
          rw [List.flatMap_cons, List.map_append, ← List.append_assoc] at hnd
          obtain ⟨ro', sn', b1, b2, b3⟩ :=
            a4 sn out hp'.1 (fun x hx => bytes_beq _ _ (List.all_eq_true.1 hr'.1 x hx))
              (List.nodup_append.1 hnd).1
          obtain ⟨ros', s', c1, c2, c3, c4⟩ :=
            g2 sn' (out.push ro') (by rw [a2]; exact hp'.2) hr'.2 (by rw [b3]; exact hnd)
          refine ⟨ro' :: ros', s', ?_, c2, ?_, ?_⟩
          · simp only [_root_.Fmt.foldRounds, idb]
            rw [b1]
            exact c1
          · rw [c3, Array.toList_push, List.append_assoc]
            rfl
          · rw [List.map_cons, b2, c4]

end

/-! ## The roots of the trees that are opened differ, if the roots that the file sends differ (under
the further hypotheses of `opened_nodup`) -/

/-- No two openings of a chain within the limits of the generic construction (here `TabOk S`,
Run/PageIsTabProofs.lean) are of one tree. -/
theorem trees_nodup (S : _root_.Fmt.Spec) (t : TabOk S) :
    ((allOpens S).map fun x => x.1.tree).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  rw [List.count, List.countP_map, List.countP_eq_length_filter]
  by_cases hex : ∃ x ∈ allOpens S, x.1.tree = a
  · obtain ⟨x, hx, rfl⟩ := hex
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
    obtain ⟨n, g⟩ := tab_good S t r hr x hxr
    refine le_trans (le_of_eq ?_) (t.once n g.lt)
    congr 1
    refine List.filter_congr fun y hy => ?_
    obtain ⟨r', hr', hyr⟩ := List.mem_flatMap.1 hy
    obtain ⟨k, g'⟩ := tab_good S t r' hr' y hyr
    show (y.1.tree == x.1.tree) = (ownNo y == some n)
    rw [g.tree, g'.tree, (tab_ownNo y k).2 g'.src]
    by_cases e : k = n
    · subst e
      simp
    · have e1 : ¬ S.firstTree + k = S.firstTree + n := by omega
      have e2 : ¬ (some k : Option ℕ) = some n := fun h => e (Option.some.inj h)
      rw [beq_eq_false_iff_ne.2 e1, beq_eq_false_iff_ne.2 e2]
  · have : (allOpens S).filter ((fun b => b == a) ∘ fun x => x.1.tree) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y hy hya
      exact hex ⟨y, hy, beq_iff_eq.1 hya⟩
    rw [this]
    exact Nat.zero_le _

/-- The place of an own tree's root among the roots sent. -/
def ownIx (x : _root_.Fmt.Shape × Src) : ℕ := match x.2 with
  | .own n => n
  | .given _ _ => 0

/-- Under `TabOk S`, no two openings are of one place. -/
theorem ix_nodup (S : _root_.Fmt.Spec) (t : TabOk S) : ((allOpens S).map ownIx).Nodup := by
  have hn := trees_nodup S t
  have e : (allOpens S).map (fun x => x.1.tree) =
      ((allOpens S).map ownIx).map fun n => S.firstTree + n := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
    obtain ⟨n, g⟩ := tab_good S t r hr x hxr
    show x.1.tree = S.firstTree + ownIx x
    unfold ownIx
    rw [g.tree, g.src]
  rw [e] at hn
  exact List.Nodup.of_map _ hn

/-- Entries of a list without repeats at different places differ. -/
theorem nodup_pick {α β γ : Type} (f : α → ℕ) (g : β → γ) (all : List γ) (hall : all.Nodup) :
    ∀ (la : List α) (lb : List β),
      List.Forall₂ (fun a b => all[f a]? = some (g b)) la lb → (la.map f).Nodup → (lb.map g).Nodup
  | [], [], _, _ => List.nodup_nil
  | a :: la, b :: lb, hF, hN => by
      obtain ⟨h1, h2⟩ := List.forall₂_cons.1 hF
      rw [List.map_cons, List.nodup_cons] at hN ⊢
      refine ⟨fun hm => ?_, nodup_pick f g all hall la lb h2 hN.2⟩
      obtain ⟨b', hb', e⟩ := List.mem_map.1 hm
      have hex : ∀ (la' : List α) (lb' : List β),
          List.Forall₂ (fun a b => all[f a]? = some (g b)) la' lb' → b' ∈ lb' →
          ∃ a' ∈ la', all[f a']? = some (g b') := by
        intro la' lb' hF'
        induction hF' with
        | nil => intro h; cases h
        | cons hab _ ih =>
            intro h
            rcases List.mem_cons.1 h with rfl | h
            · exact ⟨_, List.mem_cons_self, hab⟩
            · obtain ⟨a', ha', q⟩ := ih h
              exact ⟨a', List.mem_cons_of_mem _ ha', q⟩
      obtain ⟨a', ha', q⟩ := hex la lb h2 hb'
      rw [e] at q
      obtain ⟨l1, e1⟩ := List.getElem?_eq_some_iff.1 h1
      obtain ⟨l2, e2⟩ := List.getElem?_eq_some_iff.1 q
      have : f a = f a' := (hall.getElem_inj_iff).1 (e1.trans e2.symm)
      exact hN.1 (this ▸ List.mem_map_of_mem ha')

/-- The openings after one draw (`hO`: `OpenFacts`, Run/PageIs.lean), own trees alone: each holds
the root at its tree's place among the roots sent so far, and so among these and any later ones. -/
theorem open_roots (P : Plan) (A : Array ByteArray) (poss : List ℕ) (rest : List ByteArray)
    (lx : List (_root_.Fmt.Shape × Src)) (ly : List (_root_.Fmt.Shape × List ℕ × OpenOut))
    (hO : List.Forall₂ (OpenFacts P A poss) lx ly) :
    (∀ x ∈ lx, ∃ n, x.2 = .own n) →
    List.Forall₂
      (fun (x : _root_.Fmt.Shape × Src) (y : _root_.Fmt.Shape × List ℕ × OpenOut) =>
        (A.toList ++ rest)[ownIx x]? = some y.2.2.root)
      lx ly := by
  induction hO with
  | nil => exact fun _ => List.Forall₂.nil
  | @cons x y lx ly hxy _ ih =>
      intro hw
      refine List.Forall₂.cons ?_ (ih fun z hz => hw z (List.mem_cons_of_mem _ hz))
      obtain ⟨n, hn⟩ := hw x List.mem_cons_self
      have hr := hxy.root
      rw [hn] at hr
      have hr' : A[n]? = some y.2.2.root := hr
      have e0 : ownIx x = n := by unfold ownIx; rw [hn]
      rw [← Array.getElem?_toList] at hr'
      obtain ⟨l1, -⟩ := List.getElem?_eq_some_iff.1 hr'
      rw [e0, List.getElem?_append_left l1]
      exact hr'

/-- In the lenient reader's output (a trace, `TraceL`, with own trees alone) every opening holds the
root that was sent at its tree's place. -/
theorem trace_roots (h : HId) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) →
      List.Forall₂
        (fun (x : _root_.Fmt.Shape × Src) (y : _root_.Fmt.Shape × List ℕ × OpenOut) =>
          (roots.toList ++ ros.flatMap fun r => _root_.Fmt.rootsOf r.vals)[ownIx x]? =
            some y.2.2.root)
        (rs.flatMap (·.opens)) (ros.flatMap (·.opens))
  | [], [], _, _, _, _ => List.Forall₂.nil
  | r :: rs, ro :: ros, c, roots, hT, hown => by
      obtain ⟨-, -, -, -, hO, hT'⟩ := hT
      have ih := trace_roots h P rs ros _ _ hT' fun r' hr' => hown r' (List.mem_cons_of_mem _ hr')
      rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
      have e : (roots ++ (_root_.Fmt.rootsOf ro.vals).toArray).toList ++
            ros.flatMap (fun r => _root_.Fmt.rootsOf r.vals) =
          roots.toList ++
            (_root_.Fmt.rootsOf ro.vals ++ ros.flatMap fun r => _root_.Fmt.rootsOf r.vals) := by
        rw [Array.toList_append, List.append_assoc]
      have h1 := open_roots P _ _ (ros.flatMap fun r => _root_.Fmt.rootsOf r.vals)
        r.opens ro.opens hO (hown r List.mem_cons_self)
      rw [e] at ih h1
      exact List.rel_append h1 ih

/-- Under `hok`, `F` and `hd` (the roots that the file sends differ): the roots of the trees that
are opened differ. -/
theorem opened_nodup (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut) (hok : ok S = true)
    (F : LaxFacts h S o) (hd : ((rootsB o).map ByteArray.data).Nodup) :
    ((o.rounds.toList.flatMap (·.opens)).map fun y => y.2.2.root).Nodup := by
  have hT := trace_roots h S.plan S.rounds o.rounds.toList _ _ F.trace (own_of_ok S hok)
  have e : (#[] : Array ByteArray).toList ++
        (o.rounds.toList.flatMap fun r => _root_.Fmt.rootsOf r.vals) = rootsB o := rfl
  rw [e] at hT
  exact nodup_pick ownIx (fun y : _root_.Fmt.Shape × List ℕ × OpenOut => y.2.2.root) (rootsB o)
    (List.Nodup.of_map _ hd) _ _ hT (ix_nodup S (tab_limits S hok))

/-- Under `hok`, `hsalt`, `hrun` (which names the run's value) and `hk` (the roots of the opened
trees differ): what the lenient reader reads, with every proof-of-work test passed and every opening
walking to its root, the strict reader reads: the same view. -/
theorem strict2 (h : HId) (S : _root_.Fmt.Spec) (b : ByteArray) (o : ChainOut) (run : ByteArray)
    (hok : ok S = true)
    (hsalt : ((S.rounds.all fun r => r.opens.isEmpty) || _root_.Fmt.saltLenOK S.plan.salt) = true)
    (e : laxWhole (m := Id) h S b = some o) (hrun : o.run = some run)
    (hp : passL h S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true)
    (hr : rootsAll h S.cfg run o.rounds.toList = true)
    (hk : ((o.rounds.toList.flatMap (·.opens)).map fun y => y.2.2.root).Nodup) :
    ∃ o',
      _root_.Fmt.wholeChain (m := Id) h S b = some o' ∧
      _root_.Fmt.viewOf S.firstTree o' = _root_.Fmt.viewOf S.firstTree o := by
  have hrand := rand_of_ok S hok
  have hown := own_of_ok S hok
  have hsb : ∀ r ∈ S.rounds, r.opens.isEmpty = true ∨ _root_.Fmt.saltLenOK S.plan.salt = true := by
    intro r hr
    rcases Bool.or_eq_true_iff.1 hsalt with h1 | h2
    · exact Or.inl (List.all_eq_true.1 h1 r hr)
    · exact Or.inr h2
  unfold laxWhole cutWhole at e
  simp only [idb] at e
  cases hc : cutChain (m := Id) h
      (fun b _ roots poss os i => (pure (laxOpens S.plan roots poss b os i) : Id _)) S b 0 with
  | none => rw [hc] at e; cases e
  | some oj =>
    rw [hc] at e
    obtain ⟨o1, j⟩ := oj
    dsimp only at e
    simp only [idp] at e
    split at e
    · rename_i hj
      obtain rfl := Option.some.inj e
      unfold cutChain at hc
      split at hc
      · cases hc
      · rename_i hSok
        rw [hrand] at hc
        dsimp only at hc
        cases hsl : _root_.Fmt.slice b 0 32 with
        | none => rw [hsl] at hc; cases hc
        | some rnd =>
          rw [hsl] at hc
          simp only [Option.map_some, idb, _root_.Fmt.paramsDigestW] at hc
          cases hst : _root_.Fmt.startChainW
              (m := Id) h S.label (h 169 0 1 _root_.Fmt.zero32 S.params) S.statement (some rnd) with
          | none => rw [hst] at hc; cases hc
          | some hd =>
            rw [hst] at hc
            dsimp only at hc
            cases hf : cutFold (m := Id) h
                (fun _ roots poss os i => (pure (laxOpens S.plan roots poss b os i) : Id _))
                S.plan hd.run b S.rounds ⟨0 + 32, ⟨S.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
            | none => rw [hf] at hc; cases hc
            | some s =>
              rw [hf] at hc
              simp only [idp] at hc
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
              have hrun' : hd.run = some run := hrun
              rw [hrun'] at hf
              obtain ⟨ros, g1, g2⟩ :=
                fold_strict h S.cfg S.plan run b S.rounds _ _ _ _ _ s hsb hown hf
              have g1' : s.out.toList = ros := by simpa using g1
              obtain ⟨ros', s', c1, c2, c3, c4⟩ := g2 [] #[] (by rw [← g1']; exact hp) (by rw [← g1']; exact hr) (by
                rw [List.map_nil, List.nil_append, ← g1']
                exact hk)
              have c3' : s'.out.toList = ros' := by simpa using c3
              refine ⟨⟨h 169 0 1 _root_.Fmt.zero32 S.params, some run, hd.rho0,
                  s'.chain.rho, s'.seen, s'.out⟩,
                ?_, ?_⟩
              · unfold _root_.Fmt.wholeChain
                simp only [idb]
                unfold _root_.Fmt.readChain
                rw [if_neg hSok, hrand]
                dsimp only
                rw [hsl]
                simp only [Option.map_some, idb, _root_.Fmt.paramsDigestW]
                rw [hst]
                dsimp only
                rw [hrun', c1]
                simp only [idp]
                rw [c2, if_pos hj]
              · rw [hrun']
                exact (view_strip S.firstTree _ _ _ _ _ _ _ ros' _ _ (by rw [g1', c4]) c3').symm
    · cases e

/-- The conditions on a description (`Fmt.Spec.ok`) imply the hypothesis `hsalt` of `strict2` on the
salt's length. -/
theorem salt_of_ok (S : _root_.Fmt.Spec) (h : S.ok = true) :
    ((S.rounds.all fun r => r.opens.isEmpty) || _root_.Fmt.saltLenOK S.plan.salt) = true := by
  rw [_root_.Fmt.ok_salt h, Bool.or_true]

/-- The same as `strict2`, the salt's length from the conditions on the description. -/
theorem strict2_ok (h : HId) (S : _root_.Fmt.Spec) (b : ByteArray) (o : ChainOut) (run : ByteArray)
    (hok : ok S = true) (e : laxWhole (m := Id) h S b = some o) (hrun : o.run = some run)
    (hp : passL h S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true)
    (hr : rootsAll h S.cfg run o.rounds.toList = true)
    (hk : ((o.rounds.toList.flatMap (·.opens)).map fun y => y.2.2.root).Nodup) :
    ∃ o',
      _root_.Fmt.wholeChain (m := Id) h S b = some o' ∧
      _root_.Fmt.viewOf S.firstTree o' = _root_.Fmt.viewOf S.firstTree o :=
  strict2 h S b o run hok (salt_of_ok S (by
    simp only [ok, Bool.and_eq_true, and_assoc] at hok
    exact hok.1)) e hrun hp hr hk

/-- The proof of `Spec.pi_strict2` (Run/PageIs.lean). -/
theorem pi_strict2 : Spec.pi_strict2 := fun h hz S b o run hok e hrun hp hr hd =>
  strict2_ok h S b o run hok e hrun hp hr (opened_nodup h S o hok (pi_facts h hz S b o hok e) (by
    unfold rootsDiffer at hd
    rw [e] at hd
    exact of_decide_eq_true hd))

end Run.PQ
