-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsReaders.lean: the lenient reader against the strict reader: what the lenient reader's
output is, and that it reads whatever the strict reader reads. Both are parsers of a proof file;
both statements have the hypotheses told below.

Run/PageIs.lean compares two verifiers of a proof file: this library's rendering in Lean
(Fmt/Rules8.lean) of the verifier of the format page (docs/format/FORMAT.md, which comes with the
programs, that is, with the C++
implementation that accompanies this Lean code; here in an edition of the page that is not the one
that ships), and the compiled verifier behind a lenient reader that only cuts the file into its
parts. To cut the file, the lenient reader recomputes the hash chain, and it refuses some files
(what it still asks the hash, what it refuses and what it does not test: part 1 of the head of
Run/ParseLax.lean). This file proves two of the statements of Run/PageIs.lean that concern the
readers alone, `Spec.pi_facts` and `Spec.pi_strict1`. No typed protocol term occurs: only the
format's readers (Fmt/Rules5.lean, Fmt/Rules7.lean, Fmt/Rules8.lean) and the lenient reader
(Run/ParseLax.lean), in the identity monad, at a variable hash function h.
The statements ask that the answers of h have the format's lengths; these proofs do not use that.

1. What the file contains. Theorems with their proofs, and two definitions with which they are
stated (`stripO`, `stripR`).
   `pi_facts`: what the lenient reader's output is. Within the limits (`Run.PQ.ok`) of the generic
     construction, `laxWhole h S b = some o` implies `LaxFacts h S o`. That construction is the
     function from a description to a protocol (Run/PlanQTypes.lean). `LaxFacts h S o` says that the
     parameters' digest, the run's value made from 32 random bytes, and the chain's first value are
     as the format has them. It says further, round by round (`TraceL`), that the data of the query
     are admitted; that the items are the message as read; that what was drawn is the format's draw
     on the row made again from the message and the nonce; and that each opening stands at the
     draw's list of positions, which is an admissible list, under the root that was sent, in the
     right shape.
   `pi_strict1`: what the strict reader reads, the lenient one reads. Within the same limits,
     `wholeChain h S b = some o'` implies that there are o and run with `laxWhole h S b = some o`,
     the same view, every round's proof-of-work test passed (`passL`), and every opening leading to
     the root that was sent (`rootsAll`). There is no condition on the roots here: the strict
     reader's record of the vertices met (FORMAT.md, R7.14) can only add refusals, and the lemmas
     below hold for any such records.
   `own_of_ok`, `rand_of_ok`: within the limits every opening is of one of the chain's own trees,
     and the random bytes stand in the file.

2. What is checked when the file compiles. No tests (#guard) in this file.

3. Theorems. All of the above.

4. What is not claimed.
   The converse (`Spec.pi_strict2`: what the lenient reader reads, with all proof-of-work tests
   passed and all openings leading to their roots, the strict reader reads) is not here. It is
   proved in Run/PageIsStrict2.lean, under the hypotheses of its statement (Run/PageIs.lean), among
   them that the roots that the file sends differ; it depends on the key of the strict reader's
   record.
   Nothing about the hash function, and no statement on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIs
import Run.LaxDomProofs
import Run.OpenDomProofs
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src St)

/-! ## The lenient reader's openings -/

theorem rdOpening_len (f : _root_.Fmt.Fld) (sb : ℕ) (sh : _root_.Fmt.Shape) (xs : List ℕ)
    (b : ByteArray) (i : ℕ) (cs : List (List UInt64 × ByteArray)) (given : List ByteArray)
    (next : ℕ) (ep : _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, given), next)) :
    cs.length = xs.length ∧ given.length = (_root_.Fmt.walkPlaces sh.a xs).length := by
  unfold _root_.Fmt.rdOpening _root_.Fmt.rdPair at ep
  split at ep
  · rename_i cs' j e1
    split at ep
    · rename_i g' k e2
      simp only [Option.some.injEq, Prod.mk.injEq] at ep
      obtain ⟨⟨rfl, rfl⟩, -⟩ := ep
      exact ⟨WalkTie.rdMany_length _ _ _ _ _ _ e1, WalkTie.rdMany_length _ _ _ _ _ _ e2⟩
    · cases ep
  · cases ep

/-- What was parsed as an opening (`ep`) at a list of positions that passes `Fmt.listOK` (`hl`) has
the right shape: as a record of the type `OpenB` it passes `OpenB.ok`. -/
theorem open_ok (f : _root_.Fmt.Fld) (sb : ℕ) (sh : _root_.Fmt.Shape) (xs : List ℕ) (b : ByteArray)
    (i : ℕ) (cs : List (List UInt64 × ByteArray)) (given : List ByteArray) (next : ℕ)
    (ep : _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, given), next))
    (hl : _root_.Fmt.listOK sh.a xs = true) :
    (⟨sh.a, xs, cs.map Prod.fst, cs.map Prod.snd, given⟩ : OpenB).ok sb sh.W = true := by
  obtain ⟨l1, l2⟩ := rdOpening_len f sb sh xs b i cs given next ep
  obtain ⟨p1, p2⟩ := rdOpening_parts f sb sh xs b i cs given next ep
  obtain ⟨-, -, hb⟩ := WalkTie.listOK_spec sh.a xs hl
  unfold OpenB.ok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨TieTree.listOK_incr _ _ hl, hb⟩, by rw [List.length_map]; exact l1⟩,
            by rw [List.length_map]; exact l1⟩,
          ?_⟩,
        ?_⟩,
      by rw [l2]; exact WalkTie.places_length sh.a xs (WalkTie.listOK_one sh.a xs hl)⟩,
    p2⟩
  · intro c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
    exact (p1 y hy).1
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    exact (p1 y hy).2

theorem laxOpens_facts (P : Plan) (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (_root_.Fmt.Shape × Src))
        (i : ℕ) (cols : List (_root_.Fmt.Shape × List ℕ × OpenOut)) (j : ℕ),
      laxOpens P roots poss b os i = some (cols, j) → List.Forall₂ (OpenFacts P roots poss) os cols
  | [], i, cols, j, h => by
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact List.Forall₂.nil
  | (sh, src) :: os, i, cols, j, h => by
      unfold laxOpens at h
      dsimp only at h
      split at h
      · rename_i r cs gv k hr hl hp
        obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨rfl, -⟩ := Prod.mk.inj hxe
        exact List.Forall₂.cons ⟨rfl, rfl, hl, hr, open_ok P.field P.salt sh _ b i cs gv k hp hl⟩
          (laxOpens_facts P roots poss b os k x.1 x.2 hx)
      · cases h

/-! ## One round, all rounds -/

section
variable (h : HId)

theorem laxQuery_some (c : Chain) (msg : ByteArray) (kind : _root_.Fmt.Kind) (work nonce K : ℕ)
    (c' : Chain) (vb : Array ByteArray)
    (e : laxQueryW (m := Id) h c msg kind work nonce K = some (c', vb)) :
    _root_.Fmt.askOK c.label c.rho (c.round + 1) msg kind work nonce = true ∧
    c' = ⟨c.label,
        _root_.Fmt.nextA work
          (_root_.Fmt.fetchW (m := Id) h c.label c.rho (c.round + 1)
            msg kind work nonce (_root_.Fmt.firstBlock work + K)),
        c.round + 1⟩ ∧
    vb = _root_.Fmt.msgA work
        (_root_.Fmt.fetchW (m := Id) h c.label c.rho (c.round + 1)
          msg kind work nonce (_root_.Fmt.firstBlock work + K)) := by
  unfold laxQueryW at e
  split at e
  · rename_i hk
    simp only [idb, idp] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
    exact ⟨hk, rfl, rfl⟩
  · cases e

/-- One round of the lenient reader. If the step succeeds (`e`), it adds one round ro to the output,
and ro meets the clauses that `TraceL` (Run/PageIs.lean) has for one round. -/
theorem cutStep_facts (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s s' : St) (r : _root_.Fmt.Round)
    (e : cutStep (m := Id) h
        (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P run b s r =
      some s') :
    ∃ ro : RoundOut,
      s'.out = s.out.push ro ∧
      s'.chain = nextOf h s.chain r ro ∧
      s'.roots = s.roots ++ (_root_.Fmt.rootsOf ro.vals).toArray ∧
      _root_.Fmt.askOK s.chain.label s.chain.rho (s.chain.round + 1)
          ro.msg r.kind r.entry.work ro.nonce = true ∧
      _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) ro.msg = some ro.vals ∧
      ro.drawn =
        _root_.Fmt.drawRound P.field r.entry r.kind
          (_root_.Fmt.rowOf (_root_.Fmt.msgA r.entry.work (rowBs h s.chain r ro))) ∧
      ro.list = _root_.Fmt.listOf ro.drawn.poss ∧
      List.Forall₂ (OpenFacts P (s.roots ++ (_root_.Fmt.rootsOf ro.vals).toArray) ro.drawn.poss)
        r.opens ro.opens := by
  unfold cutStep at e
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
        cases hq : laxQueryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          obtain ⟨hk, hc, hvb⟩ := laxQuery_some h _ _ _ _ _ _ cv.1 cv.2 hq
          split at e
          · cases e
          · rename_i u i2 hlist
            simp only [idp] at e
            split at e
            · cases e
            · rename_i cols i3 hops
              cases e
              refine ⟨⟨msg, vals, nonce, _, _, cols⟩, rfl, hc, rfl, hk, hvals, ?_, rfl,
                laxOpens_facts P _ _ b r.opens i2 cols i3 hops⟩
              show _root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2) = _
              rw [hvb]
              rfl

/-- All rounds. If the lenient reader's fold over the rounds rs succeeds from the state s, the
rounds ros that it adds to the output meet `TraceL h P rs ros s.chain s.roots`. -/
theorem cutFold_facts (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List _root_.Fmt.Round) (s s' : St),
      cutFold (m := Id) h
          (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P run b rs s =
        some s' →
      ∃ ros : List RoundOut, s'.out.toList = s.out.toList ++ ros ∧ TraceL h P rs ros s.chain s.roots
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, trivial⟩
  | r :: rs, s, s', e => by
      simp only [cutFold, idb] at e
      cases hc : cutStep (m := Id) h
          (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P run b s r with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2, h3, h4, h5, h6, h7, h8⟩ := cutStep_facts h P run b s s1 r hc
        obtain ⟨ros, g1, g2⟩ := cutFold_facts P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, h4, h5, h6, h7, h8, ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rw [← h2, ← h3]
          exact g2

end

theorem startChain_some (h : HId) (lab : ℕ) (pd st rnd : ByteArray) (hd : _root_.Fmt.ChainHead)
    (e : _root_.Fmt.startChainW (m := Id) h lab pd st (some rnd) = some hd) :
    rnd.size = 32 ∧
    hd.run = some (h 172 0 lab _root_.Fmt.zero32 (pd ++ rnd)) ∧
    hd.rho0 = _root_.Fmt.firstValueW (m := Id) h lab pd st ByteArray.empty
        (some (h 172 0 lab _root_.Fmt.zero32 (pd ++ rnd))) := by
  unfold _root_.Fmt.startChainW at e
  split at e
  · dsimp only at e
    split at e
    · rename_i h32
      simp only [_root_.Fmt.runValueW, idb] at e
      split at e
      · simp only [idp] at e
        obtain rfl := Option.some.inj e
        exact ⟨h32, rfl, rfl⟩
      · cases e
    · cases e
  · cases e

/-- What the lenient reader's output is: the proof of `Spec.pi_facts` (Run/PageIs.lean). -/
theorem pi_facts : Spec.pi_facts := by
  intro h hz S b o hok e
  have hrand : S.rand = .inFile := by
    simp only [ok, Bool.and_eq_true, and_assoc] at hok
    obtain ⟨-, -, -, -, hr⟩ := hok
    split at hr
    · assumption
    · cases hr
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
    · obtain rfl := Option.some.inj e
      unfold cutChain at hc
      split at hc
      · cases hc
      · rw [hrand] at hc
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
            obtain ⟨h32, hrun, hrho⟩ := startChain_some h _ _ _ _ hd hst
            cases hf : cutFold (m := Id) h
                (fun _ roots poss os i => (pure (laxOpens S.plan roots poss b os i) : Id _))
                S.plan hd.run b S.rounds ⟨0 + 32, ⟨S.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
            | none => rw [hf] at hc; cases hc
            | some s =>
              rw [hf] at hc
              simp only [idp] at hc
              obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hc)
              obtain ⟨ros, g1, g2⟩ := cutFold_facts h S.plan hd.run b S.rounds _ s hf
              refine ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩
              · intro run hr
                have hr' : hd.run = some run := hr
                rw [hrun] at hr'
                obtain rfl := Option.some.inj hr'
                exact hrho
              · have g1' : s.out.toList = ros := by simpa using g1
                show TraceL h S.plan S.rounds s.out.toList ⟨S.label, hd.rho0, 0⟩ #[]
                rw [g1']
                exact g2
    · cases e


/-! ## The strict reader against the lenient one -/

theorem bytes_beq (a b : ByteArray) (h : (a == b) = true) : a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      have h' : (x == y) = true := by
        simpa [BEq.beq, ByteArray.instBEq.beq] using h
      rw [beq_iff_eq.1 h']

theorem bytes_beq_self (a : ByteArray) : (a == a) = true := by
  cases a with
  | mk x =>
    show (x == x) = true
    exact beq_self_eq_true x

/-- an opening, a round, as the lenient reader hands them out: without the vertices met -/
def stripO (o : OpenOut) : OpenOut := ⟨o.cols, o.salts, o.given, o.root, [], o.next⟩
def stripR (r : RoundOut) : RoundOut :=
  ⟨r.msg, r.vals, r.nonce, r.drawn, r.list, r.opens.map fun x => (x.1, x.2.1, stripO x.2.2)⟩

section
variable (h : HId)

theorem readOpening_some (cfg : ByteArray) (f : _root_.Fmt.Fld) (sb : ℕ) (sh : _root_.Fmt.Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : OpenOut)
    (e : _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    _root_.Fmt.listOK sh.a xs = true ∧
    ∃ cs,
      _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, o.given), o.next) ∧
      o.cols = cs.map Prod.fst ∧
      o.salts = cs.map Prod.snd := by
  unfold _root_.Fmt.readOpeningW at e
  split at e
  · rename_i hok
    have hl : _root_.Fmt.listOK sh.a xs = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).1
    split at e
    · cases e
    · rename_i cs given next ep
      simp only [idb, idp] at e
      obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.1 e
      subst hp
      exact ⟨hl, cs, ep, rfl, rfl⟩
  · cases e

/-- The openings after one draw. If all openings of os are of own trees and the strict reader's
`Fmt.readOpens`, from any record sn of the vertices met, gives the list l, then `laxOpens` gives l
without the vertices met (`stripO`) and ends at the same place k, and `rootOf` of each opening of l
is the root noted in it. -/
theorem readOpens_lax (cfg : ByteArray) (P : Plan) (run : ByteArray) (roots : Array ByteArray)
    (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (_root_.Fmt.Shape × Src)) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (_root_.Fmt.Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      (∀ x ∈ os, ∃ n, x.2 = .own n) →
      _root_.Fmt.readOpens (m := Id) h cfg P (some run) roots poss b os sn i = some (l, sn', k) →
      laxOpens P roots poss b os i = some (l.map fun x => (x.1, x.2.1, stripO x.2.2), k) ∧
      ∀ x ∈ l, rootOf h cfg run x.1 x.2.1 (stripO x.2.2) = x.2.2.root
  | [], sn, i, l, sn', k, _, e => by
      obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨rfl, fun x hx => by cases hx⟩
  | (sh, src) :: os, sn, i, l, sn', k, hown, e => by
      obtain ⟨n, hn⟩ := hown (sh, src) List.mem_cons_self
      have hn' : src = .own n := hn
      subst hn'
      unfold _root_.Fmt.readOpens at e
      dsimp only at e
      cases hr : roots[n]? with
      | none => rw [hr] at e; cases e
      | some root =>
        rw [hr] at e
        simp only [idb] at e
        cases ho : _root_.Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh run
            (_root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => rw [ho] at e; cases e
        | some o =>
          rw [ho] at e
          dsimp only at e
          split at e
          · rename_i hroot
            have hroot' : o.root = root := bytes_beq _ _ hroot
            split at e
            · cases e
            · rename_i sn1 hadd
              cases hrec : _root_.Fmt.readOpens
                  (m := Id) h cfg P (some run) roots poss b os sn1 o.next with
              | none => rw [hrec] at e; cases e
              | some z =>
                rw [hrec] at e
                obtain ⟨l1, sn2, k1⟩ := z
                simp only [idp] at e
                obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
                obtain ⟨ih1, ih2⟩ := readOpens_lax cfg P run roots poss b os sn1 o.next l1 sn2 k1
                  (fun x hx => hown x (List.mem_cons_of_mem _ hx)) hrec
                obtain ⟨hl, cs, hp, hc, hs⟩ :=
                  readOpening_some h cfg P.field P.salt sh run _ b i o ho
                refine ⟨?_, ?_⟩
                · unfold laxOpens
                  dsimp only
                  rw [hr, hl, hp]
                  dsimp only
                  rw [ih1]
                  show some _ = some _
                  rw [List.map_cons]
                  unfold stripO
                  rw [hc, hs, hroot']
                · intro x hx
                  rcases List.mem_cons.1 hx with rfl | hx'
                  · exact ((WalkTie.reader_id h cfg P.field P.salt sh run _ b i o ho).2.2.2).symm
                  · exact ih2 x hx'
          · cases e

theorem query_lax (c : Chain) (msg : ByteArray) (kind : _root_.Fmt.Kind) (work nonce K : ℕ)
    (c' : Chain) (vb : Array ByteArray)
    (e : Chain.queryW (m := Id) h c msg kind work nonce K = some (c', vb)) :
    laxQueryW (m := Id) h c msg kind work nonce K = some (c', vb) ∧
    _root_.Fmt.passesA work
        (_root_.Fmt.fetchW (m := Id) h c.label c.rho (c.round + 1)
          msg kind work nonce (_root_.Fmt.firstBlock work + K)) = true := by
  unfold Chain.queryW at e
  unfold laxQueryW
  split at e
  · rename_i hk
    rw [if_pos hk]
    simp only [idb, idp] at e ⊢
    split at e
    · rename_i hp
      exact ⟨e, hp⟩
    · cases e
  · cases e

end

section
variable (h : HId)

/-- One round. If all openings of r are of own trees (`hown`) and the strict reader's step succeeds
(`e`), it adds one round ro to the output. The lenient reader's step, from the same position, chain
and roots and any sn and out, then succeeds and adds `stripR ro`; the round's proof-of-work test
passes; and `rootOf` of each opening of ro is the root noted in it. -/
theorem step_lax (cfg : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray) (s s' : St)
    (r : _root_.Fmt.Round) (sn : _root_.Fmt.Seen) (out : Array RoundOut)
    (hown : ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (e : _root_.Fmt.step (m := Id) h cfg P (some run) b s r = some s') :
    ∃ ro : RoundOut,
      s'.out = s.out.push ro ∧
      cutStep (m := Id) h (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _)) P
          (some run) b ⟨s.pos, s.chain, s.roots, sn, out⟩ r =
        some ⟨s'.pos, s'.chain, s'.roots, sn, out.push (stripR ro)⟩ ∧
      s'.chain = nextOf h s.chain r (stripR ro) ∧
      _root_.Fmt.passesA r.entry.work (rowBs h s.chain r (stripR ro)) = true ∧
      ∀ x ∈ ro.opens, rootOf h cfg run x.1 x.2.1 (stripO x.2.2) = x.2.2.root := by
  unfold _root_.Fmt.step at e
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
        cases hq : Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          obtain ⟨hlq, hpass⟩ := query_lax h _ _ _ _ _ _ cv.1 cv.2 hq
          obtain ⟨-, hc, -⟩ := laxQuery_some h _ _ _ _ _ _ cv.1 cv.2 hlq
          split at e
          · cases e
          · rename_i u i2 hlist
            cases ho : _root_.Fmt.readOpens (m := Id) h cfg P (some run)
                (s.roots ++ (_root_.Fmt.rootsOf vals).toArray)
                (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss
                b r.opens s.seen i2 with
            | none => rw [ho] at e; cases e
            | some z =>
              rw [ho] at e
              obtain ⟨cols, sn2, i3⟩ := z
              simp only [idp] at e
              obtain rfl := Option.some.inj e
              obtain ⟨hl1, hl2⟩ :=
                readOpens_lax h cfg P run _ _ b r.opens s.seen i2 cols sn2 i3 hown ho
              refine ⟨⟨msg, vals, nonce, _, _, cols⟩, rfl, ?_, hc, hpass, hl2⟩
              unfold cutStep
              dsimp only
              rw [hmsg]
              dsimp only
              rw [hvals]
              dsimp only
              rw [hnon]
              simp only [idb]
              rw [hlq]
              dsimp only
              rw [hlist]
              simp only [idp]
              rw [hl1]
              rfl

/-- All rounds. If all openings of rs are of own trees and the strict reader's fold succeeds, adding
the rounds ros, then the lenient reader's fold, from the same position, chain and roots and any sn
and out, succeeds and adds the rounds `ros.map stripR`, of which `passL` and `rootsAll` hold. -/
theorem fold_lax (cfg : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray) :
    ∀ (rs : List _root_.Fmt.Round) (s s' : St) (sn : _root_.Fmt.Seen) (out : Array RoundOut),
      (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, x.2 = .own n) →
      _root_.Fmt.foldRounds (m := Id) h cfg P (some run) b rs s = some s' →
      ∃ ros : List RoundOut,
        s'.out.toList = s.out.toList ++ ros ∧
        cutFold (m := Id) h (fun _ roots poss os i => (pure (laxOpens P roots poss b os i) : Id _))
            P (some run) b rs ⟨s.pos, s.chain, s.roots, sn, out⟩ =
          some ⟨s'.pos, s'.chain, s'.roots, sn, (out.toList ++ ros.map stripR).toArray⟩ ∧
        passL h rs (ros.map stripR) s.chain = true ∧
        rootsAll h cfg run (ros.map stripR) = true
  | [], s, s', sn, out, _, e => by
      obtain rfl := Option.some.inj e
      refine ⟨[], (List.append_nil _).symm, ?_, rfl, rfl⟩
      show some _ = some _
      simp
  | r :: rs, s, s', sn, out, hown, e => by
      simp only [_root_.Fmt.foldRounds, idb] at e
      cases hc : _root_.Fmt.step (m := Id) h cfg P (some run) b s r with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2, h3, h4, h5⟩ :=
          step_lax h cfg P run b s s1 r sn out (hown r List.mem_cons_self) hc
        obtain ⟨ros, g1, g2, g3, g4⟩ :=
          fold_lax cfg P run b rs s1 s' sn (out.push (stripR ro))
            (fun r' hr' => hown r' (List.mem_cons_of_mem _ hr')) e
        refine ⟨ro :: ros, ?_, ?_, ?_, ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · simp only [cutFold, idb]
          rw [h2]
          dsimp only
          rw [g2, Array.toList_push, List.append_assoc]
          rfl
        · show (_root_.Fmt.passesA r.entry.work (rowBs h s.chain r (stripR ro)) &&
              passL h rs (ros.map stripR) (nextOf h s.chain r (stripR ro))) = true
          rw [h4, ← h3, g3]
          rfl
        · show ((stripR ro).opens.all (fun x => rootOf h cfg run x.1 x.2.1 x.2.2 == x.2.2.root) &&
              rootsAll h cfg run (ros.map stripR)) = true
          rw [g4, Bool.and_true, List.all_eq_true]
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          show (rootOf h cfg run y.1 y.2.1 (stripO y.2.2) == y.2.2.root) = true
          rw [h5 y hy]
          exact bytes_beq_self _

end

theorem own_of_ok (S : _root_.Fmt.Spec) (hok : ok S = true) :
    ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n := by
  simp only [ok, Bool.and_eq_true, and_assoc] at hok
  obtain ⟨-, -, ho, -, -⟩ := hok
  intro r hr x hx
  have := List.all_eq_true.1 ho x (List.mem_flatMap.2 ⟨r, hr, hx⟩)
  unfold ownNo at this
  split at this
  · rename_i n hn
    exact ⟨n, hn⟩
  · cases this

theorem rand_of_ok (S : _root_.Fmt.Spec) (hok : ok S = true) : S.rand = .inFile := by
  simp only [ok, Bool.and_eq_true, and_assoc] at hok
  obtain ⟨-, -, -, -, hr⟩ := hok
  split at hr
  · assumption
  · cases hr

theorem view_strip (first : ℕ) (pd : ByteArray) (run : Option ByteArray) (rho0 rho rho' : ByteArray)
    (sn sn' : _root_.Fmt.Seen) (ros : List RoundOut) (a a' : Array RoundOut)
    (ha : a.toList = ros.map stripR) (ha' : a'.toList = ros) :
    _root_.Fmt.viewOf first ⟨pd, run, rho0, rho, sn, a⟩ =
      _root_.Fmt.viewOf first ⟨pd, run, rho0, rho', sn', a'⟩ := by
  unfold _root_.Fmt.viewOf
  dsimp only
  rw [ha, ha', List.map_map, List.flatMap_map]
  congr 1
  congr 1
  funext r
  unfold _root_.Fmt.openedOf stripR
  dsimp only
  rw [List.flatMap_map]
  rfl

/-- Under the hypotheses of `Spec.pi_strict1` (Run/PageIs.lean): what the strict reader reads, the
lenient one reads: the same view; every proof-of-work test passes; every opening walks to its root.
-/
theorem pi_strict1 : Spec.pi_strict1 := by
  intro h hz S b o' hok e
  have hrand := rand_of_ok S hok
  have hown := own_of_ok S hok
  unfold _root_.Fmt.wholeChain at e
  simp only [idb] at e
  cases hc : _root_.Fmt.readChain (m := Id) h S [] b 0 with
  | none => rw [hc] at e; cases e
  | some oj =>
    rw [hc] at e
    obtain ⟨o1, j⟩ := oj
    dsimp only at e
    simp only [idp] at e
    split at e
    · rename_i hj
      obtain rfl := Option.some.inj e
      unfold _root_.Fmt.readChain at hc
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
            obtain ⟨h32, hrun0, hrho⟩ := startChain_some h _ _ _ _ hd hst
            obtain ⟨run, hrun⟩ : ∃ run : ByteArray, hd.run = some run := ⟨_, hrun0⟩
            rw [hrun] at hc
            cases hf : _root_.Fmt.foldRounds (m := Id) h S.cfg S.plan (some run) b S.rounds
                ⟨0 + 32, ⟨S.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
            | none => rw [hf] at hc; cases hc
            | some s =>
              rw [hf] at hc
              simp only [idp] at hc
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
              obtain ⟨ros, g1, g2, g3, g4⟩ :=
                fold_lax h S.cfg S.plan _ b S.rounds _ s [] #[] hown hf
              have g1' : s.out.toList = ros := by simpa using g1
              refine ⟨⟨h 169 0 1 _root_.Fmt.zero32 S.params, some run, hd.rho0, s.chain.rho, [],
                  ((#[] : Array RoundOut).toList ++ ros.map stripR).toArray⟩,
                run, ?_, rfl, ?_, ?_, ?_⟩
              · unfold laxWhole cutWhole
                simp only [idb]
                unfold cutChain
                rw [if_neg hSok, hrand]
                dsimp only
                rw [hsl]
                simp only [Option.map_some, idb, _root_.Fmt.paramsDigestW]
                rw [hst]
                dsimp only
                rw [hrun, g2]
                simp only [idp]
                rw [if_pos hj]
              · exact view_strip S.firstTree _ _ _ _ _ _ _ ros _ _ (by simp) g1'
              · show passL h S.rounds
                    ((#[] : Array RoundOut).toList ++ ros.map stripR).toArray.toList
                    ⟨S.label, hd.rho0, 0⟩ = true
                simpa using g3
              · show rootsAll h S.cfg _
                    ((#[] : Array RoundOut).toList ++ ros.map stripR).toArray.toList = true
                simpa using g4
    · cases e

end Run.PQ
