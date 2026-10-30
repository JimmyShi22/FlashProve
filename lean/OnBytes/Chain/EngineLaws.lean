-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/EngineLaws.lean: the reader's text that the program runs (OnBytes/Chain/Engine.lean)
gives what the reader's text of OnBytes/Chain/Step.lean gives.

This is one step to the strict reader `Fmt.readChainX`, which reads one chain's bytes and refuses
what breaks a rule of the format. `readChain_eq` in OnBytes/Chain/ReaderLaws.lean joins four:
this one, `readChainQ_eq` of Step.lean, and the laws that the program's step and hash are the
format's (`queryH_eq_query` in OnBytes/Hash/QueryEq.lean, `formatHashFastForm_eq_formatHash` in OnBytes/Hash/HEq.lean).
Engine.lean differs from Step.lean in that it has loops in the place of deep recursion, and a
keeper: any way to keep the record of the tree vertices met (OnBytes/Chain/Keeper.lean). Of a
keeper the proofs use its two laws, `toSeen_ofSeen` and `toSeen_add`.
Last letters of names. Q: the text of Step.lean, which takes a chain's step (its query) as an
argument. K: the text of Engine.lean, which takes a keeper too. T and F: a function of Fmt/ stated
once more without deep recursion. W and X are Fmt/'s own: over any monad; with stored trees.

Main theorems: `readChainK_eq`, `viewF_eq`.
-/
import OnBytes.Chain.Engine

namespace OnBytes

open Fmt (Qry Hash Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld View)

/-- One opening: with loops it is `Fmt.readOpeningW` at the identity monad. -/
theorem openingF_eq (h : Hash) (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape)
    (start : ByteArray) (xs : List Nat) (b : ByteArray) (i : Nat) :
    openingF h cfg f salt sh start xs b i =
      Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i := by
  unfold openingF Fmt.readOpeningW
  rw [rdOpeningT_eq]
  simp only [walkT_eq, leavesT_eq]
  cases (Fmt.listOK sh.a xs && Fmt.saltLenOK salt) with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl]
    cases Fmt.rdOpening f salt sh xs b i with
    | none => rfl
    | some x => rfl

/-- `Fmt.readStored` at the identity monad, one step unfolded. -/
theorem readStored_cons (h : Hash) (cfg statement : ByteArray) (P : Plan) (poss : List Nat)
    (b : ByteArray) (t : Stored) (ts : List Stored) (sn : Seen) (i : Nat) :
    Fmt.readStored (m := Id) h cfg statement P poss b (t :: ts) sn i =
      (match Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
          (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
      | none => none
      | some o =>
        if some o.root == Fmt.itemRoot statement t.item then
          match Fmt.addSeen o.root (Fmt.entered o.seen) sn with
          | none => none
          | some sn' =>
            match Fmt.readStored (m := Id) h cfg statement P poss b ts sn' o.next with
            | none => none
            | some (l, sn'', k) =>
              some ((t.sh, Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a)), o) :: l,
                sn'', k)
        else none) := rfl

/-- The loop over the stored trees gives what `Fmt.readStored` gives, after what was read before.
The keeper's record, read back, is the list's. -/
theorem storedLoop_eq {R : Type} (K : Keeper R) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) : ∀ (ts : List Stored) (sn : R) (i : Nat)
      (acc : Array (Shape × List Nat × OpenOut)),
    (storedLoop K h cfg statement P poss b ts sn i acc).map
        (fun x => (x.1, K.toSeen x.2.1, x.2.2)) =
      (Fmt.readStored (m := Id) h cfg statement P poss b ts (K.toSeen sn) i).map
        fun x => (acc.toList ++ x.1, x.2.1, x.2.2)
  | [], _, _, acc => by
    show some _ = some _
    simp
  | t :: ts, sn, i, acc => by
    rw [readStored_cons]
    unfold storedLoop
    simp only [listOfT_eq]
    rw [openingF_eq]
    cases Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
        (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
    | none => rfl
    | some o =>
      dsimp only
      rw [← K.toSeen_add o.root (Fmt.entered o.seen) sn]
      cases (some o.root == Fmt.itemRoot statement t.item) with
      | false => rfl
      | true =>
        rw [if_pos rfl, if_pos rfl]
        cases K.add o.root (Fmt.entered o.seen) sn with
        | none => rfl
        | some sn' =>
          simp only [Option.map_some]
          rw [storedLoop_eq K h cfg statement P poss b ts sn' o.next]
          cases Fmt.readStored (m := Id) h cfg statement P poss b ts (K.toSeen sn') o.next with
          | none => rfl
          | some x =>
            show some _ = some _
            simp

/-- The stored trees' openings: the keeper's record, read back, is the list's. -/
theorem storedK_eq {R : Type} (K : Keeper R) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) (ts : List Stored) (sn : R) (i : Nat) :
    (storedK K h cfg statement P poss b ts sn i).map (fun x => (x.1, K.toSeen x.2.1, x.2.2)) =
      Fmt.readStored (m := Id) h cfg statement P poss b ts (K.toSeen sn) i := by
  rw [storedK, storedLoop_eq]
  cases Fmt.readStored (m := Id) h cfg statement P poss b ts (K.toSeen sn) i with
  | none => rfl
  | some _ => rfl

/-- `Fmt.readOpens` at the identity monad, one step unfolded. -/
theorem readOpens_cons (h : Hash) (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) (sh : Shape) (src : Src)
    (os : List (Shape × Src)) (sn : Seen) (i : Nat) :
    Fmt.readOpens (m := Id) h cfg P run roots poss b ((sh, src) :: os) sn i =
      (match rootAndStart roots run src with
      | none => none
      | some (root, start) =>
        match Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
            (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => none
        | some o =>
          if o.root == root then
            match Fmt.addSeen root (Fmt.entered o.seen) sn with
            | none => none
            | some sn' =>
              match Fmt.readOpens (m := Id) h cfg P run roots poss b os sn' o.next with
              | none => none
              | some (l, sn'', k) =>
                some ((sh, Fmt.listOf (poss.map (· % 2 ^ sh.a)), o) :: l, sn'', k)
          else none) := by
  cases src with
  | own n => rfl
  | given r s => rfl

/-- The loop over the other trees gives what `Fmt.readOpens` gives, after what was read before. -/
theorem opensLoop_eq {R : Type} (K : Keeper R) (h : Hash) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
    (opensLoop K h cfg P run roots poss b os sn i acc).map
        (fun x => (x.1, K.toSeen x.2.1, x.2.2)) =
      (Fmt.readOpens (m := Id) h cfg P run roots poss b os (K.toSeen sn) i).map
        fun x => (acc.toList ++ x.1, x.2.1, x.2.2)
  | [], _, _, acc => by
    show some _ = some _
    simp
  | (sh, src) :: os, sn, i, acc => by
    rw [readOpens_cons]
    unfold opensLoop
    simp only [listOfT_eq]
    cases rootAndStart roots run src with
    | none => rfl
    | some x =>
      obtain ⟨root, start⟩ := x
      dsimp only
      rw [openingF_eq]
      cases Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
          (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
      | none => rfl
      | some o =>
        dsimp only
        rw [← K.toSeen_add root (Fmt.entered o.seen) sn]
        cases (o.root == root) with
        | false => rfl
        | true =>
          rw [if_pos rfl, if_pos rfl]
          cases K.add root (Fmt.entered o.seen) sn with
          | none => rfl
          | some sn' =>
            simp only [Option.map_some]
            rw [opensLoop_eq K h cfg P run roots poss b os sn' o.next]
            cases Fmt.readOpens (m := Id) h cfg P run roots poss b os (K.toSeen sn') o.next with
            | none => rfl
            | some x =>
              show some _ = some _
              simp

/-- The other trees' openings: the keeper's record, read back, is the list's. -/
theorem opensK_eq {R : Type} (K : Keeper R) (h : Hash) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray)
    (os : List (Shape × Src)) (sn : R) (i : Nat) :
    (opensK K h cfg P run roots poss b os sn i).map (fun x => (x.1, K.toSeen x.2.1, x.2.2)) =
      Fmt.readOpens (m := Id) h cfg P run roots poss b os (K.toSeen sn) i := by
  rw [opensK, opensLoop_eq]
  cases Fmt.readOpens (m := Id) h cfg P run roots poss b os (K.toSeen sn) i with
  | none => rfl
  | some _ => rfl

/-- `roundK`, with the keeper's record read back, equals `roundQ`. -/
theorem roundK_eq {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (cfg statement : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round)
    (ts : List Stored) :
    (roundK K qry h cfg statement P run b s r ts).map (StK.toSt K) =
      roundQ qry h cfg statement P run b (s.toSt K) r ts := by
  unfold roundK roundQ
  rw [readItemsT_eq]
  simp only [drawRoundT_eq, listOfT_eq, readListT_eq, rootsT_eq]
  dsimp only [StK.toSt]
  cases Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some x =>
        obtain ⟨nonce, i1⟩ := x
        dsimp only
        cases qry s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rfl
        | some y =>
          obtain ⟨c, vb⟩ := y
          dsimp only
          cases Fmt.readList P r.entry.poss
              (Fmt.listOf (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)).poss) b i1 with
          | none => rfl
          | some z =>
            obtain ⟨u, i2⟩ := z
            dsimp only
            rw [← storedK_eq K h cfg statement P
              (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)).poss b ts s.kept i2]
            cases storedK K h cfg statement P
                (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)).poss b ts s.kept i2 with
            | none => rfl
            | some w =>
              obtain ⟨colsS, sn1, i2'⟩ := w
              simp only [Option.map_some]
              rw [← opensK_eq K h cfg P run (s.roots ++ (Fmt.rootsOf vals).toArray)
                (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)).poss b r.opens sn1 i2']
              cases opensK K h cfg P run (s.roots ++ (Fmt.rootsOf vals).toArray)
                  (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf vb)).poss b r.opens sn1
                  i2' with
              | none => rfl
              | some v => rfl

/-- `foldRoundsK`, with the keeper's record read back, equals `foldRoundsQ`. -/
theorem foldRoundsK_eq {R : Type} (K : Keeper R) (qry : Qry) (h : Hash)
    (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
    (foldRoundsK K qry h cfg statement P run b rs s).map (StK.toSt K) =
      foldRoundsQ qry h cfg statement P run b rs (s.toSt K)
  | [], _ => rfl
  | r :: rs, s => by
    unfold foldRoundsK foldRoundsQ
    rw [← roundK_eq K qry h cfg statement P run b s r.1 r.2]
    cases roundK K qry h cfg statement P run b s r.1 r.2 with
    | none => rfl
    | some s' => exact foldRoundsK_eq K qry h cfg statement P run b rs s'

/-- `restK` equals `restQ`: what follows the chain's random bytes. -/
theorem restK_eq {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen)
    (b : ByteArray) (x : Option ByteArray) (i0 : Nat) :
    restK K qry h S seen b x i0 = restQ qry h S seen b x i0 := by
  unfold restK restQ
  rw [zipT_eq]
  cases Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
  | none => rfl
  | some hd =>
    dsimp only
    have e := foldRoundsK_eq K qry h S.base.cfg S.base.statement S.base.plan hd.run b
      (S.base.rounds.zip S.stored) ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩
    simp only [StK.toSt, K.toSeen_ofSeen] at e
    rw [← e]
    cases foldRoundsK K qry h S.base.cfg S.base.statement S.base.plan hd.run b
        (S.base.rounds.zip S.stored)
        ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩ with
    | none => rfl
    | some s => rfl

/-- `readChainK` equals `readChainQ`, for every keeper, step and hash. -/
theorem readChainK_eq {R : Type} (K : Keeper R) (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen)
    (b : ByteArray) (i : Nat) :
    readChainK K qry h S seen b i = readChainQ qry h S seen b i := by
  unfold readChainK readChainQ
  simp only [restK_eq, specXOk_eq]
  rfl

/-- The view that the program makes is `Fmt.viewX`. -/
theorem viewF_eq (S : SpecX) (o : ChainOut) : viewF S o = Fmt.viewX S o := by
  unfold viewF Fmt.viewX openedXT openedOfT Fmt.openedX Fmt.openedOf
  simp only [noRoots_eq, zipT_eq]

end OnBytes
