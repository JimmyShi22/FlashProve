-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineAtId.lean: the engine over a monad m, at the identity monad, is the
pure engine of OnBytes/Chain/Engine.lean at the same hash. So the program's reader at Id is the
library's strict reader, at every hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.StepAny

set_option autoImplicit false

namespace OnBytes.TwoPort.M.EngineAtId

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld Hash)

section walk
variable {α σ : Type} (comb : Nat → Nat → α → α → α) (give : Nat → Nat → σ → Option (α × σ))

theorem loneM_id (d i : Nat) (x : α) (s : σ) :
    loneM (m := Id) comb give d i x s = loneT comb give d i x s := by
  unfold loneM loneT
  cases give d (if i % 2 == 0 then i + 1 else i - 1) s with
  | none => rfl
  | some r =>
    obtain ⟨o, s'⟩ := r
    by_cases hb : (i % 2 == 0) = true
    · simp only [if_pos hb]
      rfl
    · simp only [if_neg hb]
      rfl

theorem levelLoopM_id (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ) (acc : Array (Nat × α)),
      levelLoopM (m := Id) comb give d l s acc = levelLoop comb give d l s acc
  | [], _, _ => rfl
  | [(i, x)], s, acc => by
    unfold levelLoopM levelLoop
    rw [← loneM_id]
    cases loneM (m := Id) comb give d i x s with
    | none => rfl
    | some q => rfl
  | (i, x) :: (i', x') :: rest, s, acc => by
    unfold levelLoopM levelLoop
    by_cases hc : (i % 2 == 0 && i' == i + 1) = true
    · rw [if_pos hc, if_pos hc]
      exact levelLoopM_id d rest s _
    · rw [if_neg hc, if_neg hc, ← loneM_id]
      cases loneM (m := Id) comb give d i x s with
      | none => rfl
      | some q => exact levelLoopM_id d ((i', x') :: rest) _ _

theorem walkM_id :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      walkM (m := Id) comb give d now s met = walkT comb give d now s met
  | 0, [], _, _ => rfl
  | 0, [(_, _)], _, _ => rfl
  | 0, _ :: _ :: _, _, _ => rfl
  | d + 1, now, s, met => by
    unfold walkM walkT levelT
    rw [← levelLoopM_id]
    cases levelLoopM (m := Id) comb give (d + 1) now s #[] with
    | none => rfl
    | some p => exact walkM_id d _ _ _

end walk

variable (h : Hash)

theorem leavesLoopM_id (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
      leavesLoopM (m := Id) h sh start xs cs acc = leavesLoop h sh start xs cs acc
  | x :: xs, (col, salt) :: cs, acc => by
    unfold leavesLoopM leavesLoop
    exact leavesLoopM_id sh start xs cs _
  | [], _, acc => by
    unfold leavesLoopM leavesLoop
    rfl
  | _ :: _, [], acc => by
    unfold leavesLoopM leavesLoop
    rfl

theorem openingM_id (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) :
    openingM (m := Id) h cfg f salt sh start xs b i = openingF h cfg f salt sh start xs b i := by
  unfold openingM openingF leavesT
  by_cases hc : (Fmt.listOK sh.a xs && Fmt.saltLenOK salt) = true
  · rw [if_pos hc, if_pos hc]
    cases rdOpeningT f salt sh xs b i with
    | none => rfl
    | some y =>
      obtain ⟨⟨cs, given⟩, next⟩ := y
      show Option.map _ (walkM (m := Id) (fun _ _ l r => Fmt.vertexW (m := Id) h cfg l r)
        Fmt.takeGiven sh.a (leavesLoopM (m := Id) h sh start xs cs #[]) (given, []) []) = _
      rw [leavesLoopM_id, walkM_id]
      rfl
  · rw [if_neg hc, if_neg hc]
    rfl

theorem storedLoopM_id {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      storedLoopM (m := Id) K h cfg statement P poss b ts sn i acc =
        storedLoop K h cfg statement P poss b ts sn i acc
  | [], _, _, _ => rfl
  | t :: ts, sn, i, acc => by
    unfold storedLoopM storedLoop
    rw [← openingM_id]
    cases openingM (m := Id) h cfg P.field t.salt t.sh cfg
        (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
    | none => rfl
    | some o =>
      by_cases hr : (some o.root == Fmt.itemRoot statement t.item) = true
      · show (if (some o.root == Fmt.itemRoot statement t.item) = true then _ else _) =
          (if (some o.root == Fmt.itemRoot statement t.item) = true then _ else _)
        rw [if_pos hr, if_pos hr]
        cases K.add o.root (Fmt.entered o.seen) sn with
        | none => rfl
        | some sn' => exact storedLoopM_id K cfg statement P poss b ts _ _ _
      · show (if (some o.root == Fmt.itemRoot statement t.item) = true then _ else _) =
          (if (some o.root == Fmt.itemRoot statement t.item) = true then _ else _)
        rw [if_neg hr, if_neg hr]
        rfl

theorem opensLoopM_id {R : Type} (K : Keeper R) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      opensLoopM (m := Id) K h cfg P run roots poss b os sn i acc =
        opensLoop K h cfg P run roots poss b os sn i acc
  | [], _, _, _ => rfl
  | (sh, src) :: os, sn, i, acc => by
    unfold opensLoopM opensLoop
    cases rootAndStart roots run src with
    | none => rfl
    | some y =>
      obtain ⟨root, start⟩ := y
      show (match openingM (m := Id) h cfg P.field P.salt sh start
          (listOfT (poss.map (· % 2 ^ sh.a))) b i with
        | none => _
        | some o => _) = _
      simp only []
      rw [← openingM_id]
      cases openingM (m := Id) h cfg P.field P.salt sh start
          (listOfT (poss.map (· % 2 ^ sh.a))) b i with
      | none => rfl
      | some o =>
        by_cases hr : (o.root == root) = true
        · show (if (o.root == root) = true then _ else _) =
            (if (o.root == root) = true then _ else _)
          rw [if_pos hr, if_pos hr]
          cases K.add root (Fmt.entered o.seen) sn with
          | none => rfl
          | some sn' => exact opensLoopM_id K cfg P run roots poss b os _ _ _
        · show (if (o.root == root) = true then _ else _) =
            (if (o.root == root) = true then _ else _)
          rw [if_neg hr, if_neg hr]
          rfl

theorem roundM_id {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round) (ts : List Stored) :
    roundM (m := Id) K h cfg statement P run b s r ts =
      roundK K (stepOf h) h cfg statement P run b s r ts := by
  unfold roundM roundK storedK opensK stepOf
  simp only [← storedLoopM_id, ← opensLoopM_id]
  cases Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (readItemsT P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some y =>
        obtain ⟨nonce, i1⟩ := y
        dsimp only
        show (match Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
          | none => _
          | some (c, vb) => _) = _
        cases Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rfl
        | some cv =>
          obtain ⟨c, vb⟩ := cv
          dsimp only
          cases readListT P r.entry.poss
              (listOfT (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss) b i1 with
          | none => rfl
          | some z =>
            obtain ⟨z1, i2⟩ := z
            dsimp only
            show (match storedLoopM (m := Id) K h cfg statement P
                (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b ts s.kept i2 #[] with
              | none => _
              | some (colsS, sn1, i2') => _) = _
            cases storedLoopM (m := Id) K h cfg statement P
                (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b ts s.kept i2 #[] with
            | none => rfl
            | some w =>
              obtain ⟨colsS, sn1, i2'⟩ := w
              dsimp only
              show (match opensLoopM (m := Id) K h cfg P run (s.roots ++ (rootsT vals).toArray)
                  (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b r.opens sn1 i2' #[] with
                | none => _
                | some (cols, sn, i3) => _) = _
              cases opensLoopM (m := Id) K h cfg P run (s.roots ++ (rootsT vals).toArray)
                  (drawRoundT P.field r.entry r.kind (Fmt.rowOf vb)).poss b r.opens sn1 i2' #[] with
              | none => rfl
              | some v => rfl

theorem foldRoundsM_id {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
      foldRoundsM (m := Id) K h cfg statement P run b rs s =
        foldRoundsK K (stepOf h) h cfg statement P run b rs s
  | [], _ => rfl
  | r :: rs, s => by
    unfold foldRoundsM foldRoundsK
    rw [← roundM_id]
    cases roundM (m := Id) K h cfg statement P run b s r.1 r.2 with
    | none => rfl
    | some s' => exact foldRoundsM_id K cfg statement P run b rs s'

theorem restM_id {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) :
    restM (m := Id) K h S seen b x i0 = restK K (stepOf h) h S seen b x i0 := by
  unfold restM restK
  simp only [← foldRoundsM_id]
  show (match Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
    | none => _
    | some hd => _) = _
  cases Fmt.startChainW (m := Id) h S.base.label
      (Fmt.paramsDigestW (m := Id) h S.base.params) S.base.statement x with
  | none => rfl
  | some hd =>
    dsimp only
    show (match foldRoundsM (m := Id) K h S.base.cfg S.base.statement S.base.plan hd.run b
        (zipT S.base.rounds S.stored)
        ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩ with
      | none => _
      | some s => _) = _
    cases foldRoundsM (m := Id) K h S.base.cfg S.base.statement S.base.plan hd.run b
        (zipT S.base.rounds S.stored)
        ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], K.ofSeen seen, #[]⟩ with
    | none => rfl
    | some s => rfl

theorem readChainM_id {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) :
    readChainM (m := Id) K h S seen b i = readChainK K (stepOf h) h S seen b i := by
  unfold readChainM readChainK
  simp only [← restM_id]
  by_cases hc : (!specXOk S) = true
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    cases S.base.rand with
    | inFile =>
      dsimp only
      cases Fmt.slice b i 32 with
      | none => rfl
      | some x => rfl
    | given x => rfl
    | none => rfl

/-- The program's reader over m, at the identity monad, is the library's strict reader, at every
hash. -/
theorem readChain_id (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    readChain (m := Id) h S seen b i = Fmt.readChainX (m := Id) h S seen b i := by
  unfold readChain
  rw [readChainM_id, readChainK_eq]
  exact readChainQ_any h S seen b i

end OnBytes.TwoPort.M.EngineAtId
