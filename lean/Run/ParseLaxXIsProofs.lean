-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLaxXIsProofs.lean: the proofs of the four statements of Run/ParseLaxXIs.lean, which compare
the lenient reader for proof files that open stored tables with the strict reader. Many statements
of this library are written twice: a definition in the namespace `Spec` states a proposition, and a
theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Sources. After Run/PageIsReaders.lean, whose `readOpening_some`, `readOpens_lax` and `query_lax` are
used as they are; new here is the part on the stored trees' openings.

1. What the file contains.  Lemmas:
     `lxi_stored`: what `Fmt.readStored` reads, `laxStored` parses, and hands on the same without
       the vertices met. Of `readStored` the proof uses only that it answered, not by what its
       record of vertices is keyed; so it does not depend on docs/format/FORMAT.md, R7.14, which
       differs between two editions, neither of them the one that ships.
     `lxi_rounds`, `lxi_storedB`, `lxi_off`, `lxi_opensB`, `lxi_rootsB`, `lxi_plains`: what the
       typing (`toBPrfX`, Run/PlanQX.lean) reads of a reader's output does not see the vertices met.
2. What is checked when the file compiles.  Nothing beyond the proofs.
3. Theorems. `laxX_reads`, `toBPrfX_strip`, `entry_lax`, `entry_half`, as stated in
   Run/ParseLaxXIs.lean.
4. What is not claimed. What the head of Run/ParseLaxXIs.lean lists as not claimed is not claimed
   here either.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ParseLaxXIs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src St SpecX Stored)

theorem lxi_opt (a : ByteArray) (o : Option ByteArray) (h : (some a == o) = true) : o = some a := by
  cases o with
  | none => cases h
  | some b => exact congrArg some (bytes_beq a b h).symm

section
variable (h : HId)

/-- The stored trees' openings after one draw. -/
theorem lxi_stored (cfg statement : ByteArray) (P : Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (_root_.Fmt.Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      _root_.Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
      laxStored statement P poss b ts i = some (l.map fun x => (x.1, x.2.1, stripO x.2.2), k)
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      rfl
  | t :: ts, sn, i, l, sn', k, e => by
      unfold _root_.Fmt.readStored at e
      simp only [idb] at e
      cases ho : _root_.Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
          (_root_.Fmt.listOf ((_root_.Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
      | none => rw [ho] at e; cases e
      | some o =>
        rw [ho] at e
        dsimp only at e
        split at e
        · rename_i hroot
          have hroot' : _root_.Fmt.itemRoot statement t.item = some o.root := lxi_opt _ _ hroot
          split at e
          · cases e
          · rename_i sn1 hadd
            cases hrec : _root_.Fmt.readStored (m := Id) h cfg statement P poss b ts sn1 o.next with
            | none => rw [hrec] at e; cases e
            | some z =>
              rw [hrec] at e
              obtain ⟨l1, sn2, k1⟩ := z
              simp only [idp] at e
              obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
              have ih := lxi_stored cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec
              obtain ⟨hl, cs, hp, hc, hs⟩ :=
                readOpening_some h cfg P.field t.salt t.sh cfg _ b i o ho
              unfold laxStored
              dsimp only
              rw [hroot', hl, hp]
              dsimp only
              rw [ih]
              show some _ = some _
              rw [List.map_cons]
              unfold stripO
              rw [hc, hs]
        · cases e

/-- One round. -/
theorem lxi_step (cfg statement : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray)
    (s s' : St) (r : _root_.Fmt.Round) (ts : List Stored) (sn : _root_.Fmt.Seen)
    (out : Array RoundOut) (hown : ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (e : _root_.Fmt.roundX (m := Id) h cfg statement P (some run) b s r ts = some s') :
    ∃ ro : RoundOut,
      s'.out = s.out.push ro ∧
      cutStepX (m := Id) h statement P b ⟨s.pos, s.chain, s.roots, sn, out⟩ r ts =
        some ⟨s'.pos, s'.chain, s'.roots, sn, out.push (stripR ro)⟩ := by
  unfold _root_.Fmt.roundX at e
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
          obtain ⟨hlq, -⟩ := query_lax h _ _ _ _ _ _ cv.1 cv.2 hq
          split at e
          · cases e
          · rename_i u i2 hlist
            cases hs : _root_.Fmt.readStored (m := Id) h cfg statement P
                (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss
                b ts s.seen i2 with
            | none => rw [hs] at e; cases e
            | some y =>
              rw [hs] at e
              obtain ⟨colsS, sn1, i2'⟩ := y
              dsimp only at e
              cases ho : _root_.Fmt.readOpens (m := Id) h cfg P (some run)
                  (s.roots ++ (_root_.Fmt.rootsOf vals).toArray)
                  (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss
                  b r.opens sn1 i2' with
              | none => rw [ho] at e; cases e
              | some z =>
                rw [ho] at e
                obtain ⟨cols, sn2, i3⟩ := z
                simp only [idp] at e
                obtain rfl := Option.some.inj e
                have hl0 := lxi_stored h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs
                obtain ⟨hl1, -⟩ :=
                  readOpens_lax h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 hown ho
                refine ⟨⟨msg, vals, nonce, _, _, colsS ++ cols⟩, rfl, ?_⟩
                unfold cutStepX
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
                dsimp only
                rw [hl0]
                dsimp only
                rw [hl1]
                simp only [idp, stripR, List.map_append]

/-- All rounds. -/
theorem lxi_fold (cfg statement : ByteArray) (P : Plan) (run : ByteArray) (b : ByteArray) :
    ∀ (rs : List (_root_.Fmt.Round × List Stored))
        (s s' : St) (sn : _root_.Fmt.Seen) (out : Array RoundOut),
      (∀ r ∈ rs, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n) →
      _root_.Fmt.foldRoundsX (m := Id) h cfg statement P (some run) b rs s = some s' →
      ∃ ros : List RoundOut,
        s'.out.toList = s.out.toList ++ ros ∧
        cutFoldX (m := Id) h statement P b rs ⟨s.pos, s.chain, s.roots, sn, out⟩ =
          some ⟨s'.pos, s'.chain, s'.roots, sn, (out.toList ++ ros.map stripR).toArray⟩
  | [], s, s', sn, out, _, e => by
      obtain rfl := Option.some.inj e
      refine ⟨[], (List.append_nil _).symm, ?_⟩
      show some _ = some _
      simp
  | r :: rs, s, s', sn, out, hown, e => by
      simp only [_root_.Fmt.foldRoundsX, idb] at e
      cases hc : _root_.Fmt.roundX (m := Id) h cfg statement P (some run) b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2⟩ :=
          lxi_step h cfg statement P run b s s1 r.1 r.2 sn out (hown r List.mem_cons_self) hc
        obtain ⟨ros, g1, g2⟩ := lxi_fold cfg statement P run b rs s1 s' sn (out.push (stripR ro))
          (fun r' hr' => hown r' (List.mem_cons_of_mem _ hr')) e
        refine ⟨ro :: ros, ?_, ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · simp only [cutFoldX, idb]
          rw [h2]
          dsimp only
          rw [g2, Array.toList_push, List.append_assoc]
          rfl

end

/-- What the strict reader reads, the lenient one reads, under the hypotheses of the statement. -/
theorem laxX_reads : Spec.laxX_reads := by
  intro h S b o' hown hrand e
  unfold _root_.Fmt.wholeChainX at e
  simp only [idb] at e
  cases hc : _root_.Fmt.readChainX (m := Id) h S [] b 0 with
  | none => rw [hc] at e; cases e
  | some oj =>
    rw [hc] at e
    obtain ⟨o1, j⟩ := oj
    dsimp only at e
    simp only [idp] at e
    split at e
    · rename_i hj
      obtain rfl := Option.some.inj e
      unfold _root_.Fmt.readChainX at hc
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
          cases hst : _root_.Fmt.startChainW (m := Id) h S.base.label
              (h 169 0 1 _root_.Fmt.zero32 S.base.params) S.base.statement (some rnd) with
          | none => rw [hst] at hc; cases hc
          | some hd =>
            rw [hst] at hc
            dsimp only at hc
            obtain ⟨-, hrun0, -⟩ := startChain_some h _ _ _ _ hd hst
            obtain ⟨run, hrun⟩ : ∃ run : ByteArray, hd.run = some run := ⟨_, hrun0⟩
            rw [hrun] at hc
            cases hf : _root_.Fmt.foldRoundsX (m := Id) h S.base.cfg S.base.statement S.base.plan
                (some run) b (S.base.rounds.zip S.stored)
                ⟨0 + 32, ⟨S.base.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
            | none => rw [hf] at hc; cases hc
            | some s =>
              rw [hf] at hc
              simp only [idp] at hc
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
              obtain ⟨ros, g1, g2⟩ := lxi_fold h S.base.cfg S.base.statement S.base.plan _ b
                (S.base.rounds.zip S.stored) _ s [] #[]
                (fun r hr => hown r.1 (List.of_mem_zip hr).1) hf
              have g1' : s.out.toList = ros := by simpa using g1
              unfold laxWholeX
              simp only [idb]
              unfold cutChainX
              rw [if_neg hSok, hrand]
              dsimp only
              rw [hsl]
              simp only [Option.map_some, idb, _root_.Fmt.paramsDigestW]
              rw [hst]
              dsimp only
              rw [g2]
              simp only [idp]
              rw [if_pos hj]
              unfold stripX
              dsimp only
              rw [hrun]
              congr 2
              apply Array.toList_inj.1
              simp [g1']
    · cases e

/-! ### The typing -/

theorem lxi_rounds (o : ChainOut) : (stripX o).rounds.toList = o.rounds.toList.map stripR := by
  unfold stripX
  simp

theorem lxi_storedB (xs : List XO) (o : ChainOut) : storedB xs (stripX o) = storedB xs o := by
  unfold storedB
  rw [lxi_rounds, List.zipIdx_map, List.flatMap_map]
  congr 1
  funext r
  show ((xsAt xs r.2).zip ((stripR r.1).opens)).map _ = _
  unfold stripR
  dsimp only
  rw [List.zip_map_right, List.map_map]
  rfl

theorem lxi_off (xs : List XO) (o : ChainOut) :
    (offStored xs (stripX o)).rounds.toList = (offStored xs o).rounds.toList.map stripR := by
  unfold offStored
  dsimp only
  rw [lxi_rounds, List.zipIdx_map, List.map_map, List.map_map]
  congr 1
  funext r
  show _ = stripR _
  unfold stripR
  simp [List.map_drop]

theorem lxi_opensB (o o' : ChainOut) (e : o.rounds.toList = o'.rounds.toList.map stripR) :
    opensB o = opensB o' := by
  unfold opensB
  rw [e, List.flatMap_map]
  congr 1
  funext r
  unfold stripR
  dsimp only
  rw [List.map_map]
  rfl

theorem lxi_rootsB (o o' : ChainOut) (e : o.rounds.toList = o'.rounds.toList.map stripR) :
    rootsB o = rootsB o' := by
  unfold rootsB
  rw [e, List.flatMap_map]
  rfl

theorem lxi_plains (C : CK) :
    ∀ (ds : List RD) (l : List RoundOut), plainsSL C ds (l.map stripR) = plainsSL C ds l
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, o :: os => by
      show (match PlainOf.ofGots d.items o.vals, plainsSL C ds (os.map stripR) with
        | some p, some r => some (GPlain.mk d.entry.work p o.nonce, r)
        | _, _ => none) = _
      rw [lxi_plains C ds os]
      rfl

/-- The typing does not look at the vertices met. -/
theorem toBPrfX_strip : Spec.toBPrfX_strip := by
  intro salt cfg C ds a xs dec o
  unfold toBPrfX
  rw [lxi_storedB]
  have e := lxi_off xs o
  have hP : toBPrfP (skeletonOverBothExternalStrings C ds a xs dec) (TYX salt C ds a xs dec) (offStored xs (stripX o)) =
      toBPrfP (skeletonOverBothExternalStrings C ds a xs dec) (TYX salt C ds a xs dec) (offStored xs o) := by
    unfold toBPrfP
    rw [lxi_opensB _ _ e, lxi_rootsB _ _ e]
    have hp : (TYX salt C ds a xs dec).plains (offStored xs (stripX o)).rounds =
        (TYX salt C ds a xs dec).plains (offStored xs o).rounds := by
      show (plainsSL C ds (offStored xs (stripX o)).rounds.toList).map _ =
        (plainsSL C ds (offStored xs o).rounds.toList).map _
      rw [e, lxi_plains]
    rw [hp]
    rfl
  rw [hP]

/-- Where the run behind the strict reader does not answer `.reader`, the two runs give one
outcome. -/
theorem entry_lax : Spec.entry_lax := by
  intro D dec r0 file hne
  unfold runEntryK at hne ⊢
  unfold runEntryLax
  by_cases hok : D.ok = true
  · rw [if_pos hok] at hne ⊢
    rw [if_pos hok]
    cases hh : readHead file with
    | none => rfl
    | some x =>
      obtain ⟨r1, rest⟩ := x
      rw [hh] at hne
      dsimp only at hne ⊢
      cases hw : _root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest with
      | none =>
        rw [hw] at hne
        exact absurd rfl hne
      | some o' =>
        have hb : PQ.ok D.base = true := by
          unfold XD.ok at hok
          simp only [Bool.and_eq_true] at hok
          exact hok.1.1
        have hl := laxX_reads _root_.Fmt.formatHash (D.atR r0 r1) rest o' (own_of_ok D.base hb)
          (rand_of_ok D.base hb) hw
        rw [_root_.Fmt.HF_eq, hl]
        show (match toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec (stripX o') with
          | none => Who.reader
          | some π => if VXK D dec r0 r1 π then Who.accepted else Who.verifier) = _
        rw [toBPrfX_strip]
        rfl
  · rw [if_neg hok, if_neg hok]

theorem entry_half : Spec.entry_half := fun D dec r0 file h => by
  rw [entry_lax D dec r0 file (by rw [h]; exact fun e => by cases e), h]

end Run.PQ
