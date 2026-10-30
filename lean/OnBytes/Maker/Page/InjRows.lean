-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/InjRows.lean: the roots and the plain part of a written round come back from the
message's bytes and the nonce, along a stretch of rounds as OnBytes/Maker/Page/Fill.lean reads it
(`saidLo`, `saidSh`).

Statements and proofs; no definition. `fillJ` gives the empty message and the nonce 0 to a plain
part that is not of the round that the query names, drops roots beyond the message's items "root",
and writes nothing where roots run out: so without a test many typed queries have one string.

Main names:
  `ext_cancel`, `bytesL_inj`: the spelling of a message (OnBytes/TypedOracleCompiler/Run/PlanQSpell.lean, `bytesL`)
    gives back roots and items, if there are as many roots as items "root" (`toRoots`).
  `gplain_ext`: a plain part with a nonce is known from its two parts.
  `splitPB_inj`: a plain part of two shapes laid behind each other is known from its cut.
  `saidLo_lt`, `saidSh_lt`, `saidLo_inj`, `saidSh_inj`: along a stretch of rounds: two plain parts
    that say the same place, with lists of roots that fit, the same bytes and the same nonce, are
    the same, and so are the lists.
No letter stands under "there is". The laws at a file's rounds and at `fillJ`:
OnBytes/Maker/Page/InjParts.lean.

What is not claimed. That a verifier's queries pass the tests. Nothing on the joining round's part
of a slot and the other parts that `partOf` reads as nothing. Nothing on any hash. Nothing on
soundness.


-/
import OnBytes.Maker.Page.FillLaws
import OnBytes.K.Arm.StrInj
import OnBytes.Tie.IdKey
import Fmt.Rules23In
import Run.CodingPage160

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open _root_.Fmt (Item)
open TypedOracleCompiler.Run.PQ (bytesL toRoots)
open OnBytes.Tie (u64_inj)
open OnBytes.K.Arm (digToBytes_inj)

/-! ## A message's bytes -/

theorem size_w (a b : UInt64) : (Fmt.u64 a).size = (Fmt.u64 b).size :=
  (Fmt.size_u64 a).trans (Fmt.size_u64 b).symm

theorem ext_cancel (x x' : UInt64 × UInt64 × UInt64) (b b' : ByteArray)
    (e : Fmt.ext x ++ b = Fmt.ext x' ++ b') : x = x' ∧ b = b' := by
  unfold Fmt.ext at e
  simp only [ByteArray.append_assoc] at e
  obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (size_w _ _) e
  obtain ⟨e3, e4⟩ := Fmt.append_cancel _ _ _ _ (size_w _ _) e2
  obtain ⟨e5, e6⟩ := Fmt.append_cancel _ _ _ _ (size_w _ _) e4
  exact ⟨Prod.ext (u64_inj e1) (Prod.ext (u64_inj e3) (u64_inj e5)), e6⟩

theorem bytesL_f (rts : List ByteArray) (l : List Item) (x : UInt64 × PlainOf l) :
    bytesL rts (.f :: l) x = Fmt.u64 x.1 ++ bytesL rts l x.2 := by cases rts <;> rfl

theorem bytesL_word (rts : List ByteArray) (l : List Item) (x : UInt64 × PlainOf l) :
    bytesL rts (.word :: l) x = Fmt.u64 x.1 ++ bytesL rts l x.2 := by cases rts <;> rfl

theorem bytesL_e (rts : List ByteArray) (l : List Item) (x : Fmt.Ext × PlainOf l) :
    bytesL rts (.e :: l) x = Fmt.ext x.1 ++ bytesL rts l x.2 := by cases rts <;> rfl

theorem bytesL_answer (rts : List ByteArray) (l : List Item) (x : Fmt.Ext × PlainOf l) :
    bytesL rts (.answer :: l) x = Fmt.ext x.1 ++ bytesL rts l x.2 := by cases rts <;> rfl

/-- **A message's bytes give back its roots and its items**, if there are as many roots as items
"root". -/
theorem bytesL_inj :
    ∀ (l : List Item) (rt rt' : List (Dig 256)) (y y' : RootOf l), toRoots l rt = some y →
      toRoots l rt' = some y' → ∀ x x' : PlainOf l,
        bytesL (rt.map digToBytes) l x = bytesL (rt'.map digToBytes) l x' → rt = rt' ∧ x = x'
  | [], [], [], _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, h, _, _, _, _ => by cases h
  | [], [], _ :: _, _, _, _, h, _, _, _ => by cases h
  | .root :: l, r :: rt, r' :: rt', y, y', h, h', x, x', e => by
      have h0 : (toRoots l rt).map (fun y => ((r, y) : Dig 256 × RootOf l)) = some y := h
      have h0' : (toRoots l rt').map (fun y => ((r', y) : Dig 256 × RootOf l)) = some y' := h'
      cases hy : toRoots l rt with
      | none => rw [hy] at h0; cases h0
      | some z =>
        cases hy' : toRoots l rt' with
        | none => rw [hy'] at h0'; cases h0'
        | some z' =>
          have e0 : digToBytes r ++ bytesL (rt.map digToBytes) l x =
              digToBytes r' ++ bytesL (rt'.map digToBytes) l x' := e
          obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _
            ((size_digToBytes r).trans (size_digToBytes r').symm) e0
          obtain ⟨a, b⟩ := bytesL_inj l rt rt' z z' hy hy' x x' e2
          exact ⟨by rw [digToBytes_inj e1, a], b⟩
  | .root :: _, [], _, _, _, h, _, _, _, _ => by cases h
  | .root :: _, _ :: _, [], _, _, _, h, _, _, _ => by cases h
  | .f :: l, rt, rt', y, y', h, h', (x : UInt64 × PlainOf l), (x' : UInt64 × PlainOf l), e => by
      rw [bytesL_f, bytesL_f] at e
      obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (size_w _ _) e
      obtain ⟨a, b⟩ := bytesL_inj l rt rt' y y' h h' x.2 x'.2 e2
      exact ⟨a, Prod.ext (u64_inj e1) b⟩
  | .word :: l, rt, rt', y, y', h, h', (x : UInt64 × PlainOf l), (x' : UInt64 × PlainOf l),
      e => by
      rw [bytesL_word, bytesL_word] at e
      obtain ⟨e1, e2⟩ := Fmt.append_cancel _ _ _ _ (size_w _ _) e
      obtain ⟨a, b⟩ := bytesL_inj l rt rt' y y' h h' x.2 x'.2 e2
      exact ⟨a, Prod.ext (u64_inj e1) b⟩
  | .e :: l, rt, rt', y, y', h, h', (x : Fmt.Ext × PlainOf l), (x' : Fmt.Ext × PlainOf l), e => by
      rw [bytesL_e, bytesL_e] at e
      obtain ⟨e1, e2⟩ := ext_cancel _ _ _ _ e
      obtain ⟨a, b⟩ := bytesL_inj l rt rt' y y' h h' x.2 x'.2 e2
      exact ⟨a, Prod.ext e1 b⟩
  | .answer :: l, rt, rt', y, y', h, h', (x : Fmt.Ext × PlainOf l), (x' : Fmt.Ext × PlainOf l),
      e => by
      rw [bytesL_answer, bytesL_answer] at e
      obtain ⟨e1, e2⟩ := ext_cancel _ _ _ _ e
      obtain ⟨a, b⟩ := bytesL_inj l rt rt' y y' h h' x.2 x'.2 e2
      exact ⟨a, Prod.ext e1 b⟩

/-- A plain part with a nonce is known from its two parts. -/
theorem gplain_ext {P : Type} : ∀ (b : ℕ) (p p' : GPlain ℕ b P),
    GPlain.old p = GPlain.old p' → GPlain.nonce p = GPlain.nonce p' → p = p'
  | 0, _, _, h, _ => h
  | _ + 1, (_, _), (_, _), h, h' => Prod.ext h h'

/-- One written round. -/
theorem saidOf_inj (C : CK) (d : RDT) (rt rt' : List (Dig 256)) (pl pl' : (roundT C d).Plain)
    (hf : (toRoots d.items rt).isSome = true) (hf' : (toRoots d.items rt').isSome = true)
    (em : (saidOf C d pl).msg (rt.map digToBytes) = (saidOf C d pl').msg (rt'.map digToBytes))
    (en : (saidOf C d pl).nonce = (saidOf C d pl').nonce) : rt = rt' ∧ pl = pl' := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hf
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hf'
  obtain ⟨a, b⟩ := bytesL_inj d.items rt rt' y y' hy hy' _ _ em
  exact ⟨a, gplain_ext d.entry.work pl pl' b en⟩

/-! ## A plain part of two shapes laid behind each other -/

theorem splitPB_inj : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (z z' : PlainPart (s ++ u) (RoundSplits.app A B)), splitPB z = splitPB z' → z = z'
  | [], _, _, _, _, _, h => Sum.inr.inj h
  | _ :: _, _, (_, _), _, .inl _, .inl _, h => congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj h))
  | _ :: s, u, (a, A), B, .inl x, .inr z', h => by
      have h1 : (Sum.inl (Sum.inl x) : ((a.P0 ⊕ a.Pj) ⊕ PlainPart s A) ⊕ PlainPart u B) =
          Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id (splitPB z') := h
      cases hz : splitPB z' with
      | inl w => rw [hz] at h1; cases Sum.inl.inj h1
      | inr w => rw [hz] at h1; cases h1
  | _ :: s, u, (a, A), B, .inr z, .inl x, h => by
      have h1 : Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id (splitPB z) =
          (Sum.inl (Sum.inl x) : ((a.P0 ⊕ a.Pj) ⊕ PlainPart s A) ⊕ PlainPart u B) := h
      cases hz : splitPB z with
      | inl w => rw [hz] at h1; cases Sum.inl.inj h1
      | inr w => rw [hz] at h1; cases h1
  | _ :: s, u, (a, A), B, .inr z, .inr z', h => by
      have h1 : Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id (splitPB z) =
          Sum.map (Sum.inr : PlainPart s A → (a.P0 ⊕ a.Pj) ⊕ PlainPart s A) id (splitPB z') := h
      have h2 : splitPB z = splitPB z' := by
        cases hz : splitPB z with
        | inl w =>
          cases hz' : splitPB z' with
          | inl w' =>
            rw [hz, hz'] at h1
            exact congrArg Sum.inl (Sum.inr.inj (Sum.inl.inj h1))
          | inr w' => rw [hz, hz'] at h1; cases h1
        | inr w =>
          cases hz' : splitPB z' with
          | inl w' => rw [hz, hz'] at h1; cases h1
          | inr w' =>
            rw [hz, hz'] at h1
            exact congrArg Sum.inr (Sum.inr.inj h1)
      exact congrArg Sum.inr (splitPB_inj z z' h2)

/-! ## Along a stretch of rounds -/

section
variable (C : CK)

theorem saidLo_lt : ∀ (ds : List RDT) (w : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds))) (s : Said),
    saidLo C ds w = some s → s.k < ds.length
  | [], _, _, h => by cases h
  | d :: ds, w, s, h => by
      obtain ⟨y, rfl⟩ : ∃ y : (Unit ⊕ (roundT C d).Plain) ⊕
          PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)), y = w := ⟨w, rfl⟩
      rcases y with (u | pl) | v
      · cases h
      · have h1 : some (saidOf C d pl) = some s := h
        rw [← Option.some.inj h1]
        exact Nat.succ_pos _
      · have h1 : (saidLo C ds v).map Said.next = some s := h
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h1
        have := saidLo_lt ds v t ht
        show t.k + 1 < ds.length + 1
        omega

theorem saidSh_lt : ∀ (ds : List RDT)
    (w : PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))) (s : Said),
    saidSh C ds w = some s → s.k < ds.length
  | [], _, _, h => by cases h
  | d :: ds, w, s, h => by
      obtain ⟨y, rfl⟩ : ∃ y : ((roundT C d).Plain ⊕ Unit) ⊕
          PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)), y = w := ⟨w, rfl⟩
      rcases y with (pl | u) | v
      · have h1 : some (saidOf C d pl) = some s := h
        rw [← Option.some.inj h1]
        exact Nat.succ_pos _
      · cases h
      · have h1 : (saidSh C ds v).map Said.next = some s := h
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h1
        have := saidSh_lt ds v t ht
        show t.k + 1 < ds.length + 1
        omega

variable (rt rt' : List (Dig 256))

/-- **Along a stretch of local rounds.** -/
theorem saidLo_inj : ∀ (ds : List RDT) (w w' : PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)))
    (s s' : Said), saidLo C ds w = some s → saidLo C ds w' = some s' → s.k = s'.k →
    (∀ d, ds[s.k]? = some d →
      (toRoots d.items rt).isSome = true ∧ (toRoots d.items rt').isSome = true) →
    s.msg (rt.map digToBytes) = s'.msg (rt'.map digToBytes) → s.nonce = s'.nonce →
    rt = rt' ∧ w = w'
  | [], _, _, _, _, h, _, _, _, _, _ => by cases h
  | d :: ds, w, w', s, s', h, h', hk, hf, em, en => by
      obtain ⟨y, rfl⟩ : ∃ y : (Unit ⊕ (roundT C d).Plain) ⊕
          PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)), y = w := ⟨w, rfl⟩
      obtain ⟨y', rfl⟩ : ∃ y : (Unit ⊕ (roundT C d).Plain) ⊕
          PlainPart (uLT C ds) (RoundSplits.allLocal (uLT C ds)), y = w' := ⟨w', rfl⟩
      rcases y with (u | pl) | v
      · cases h
      · have h1 : some (saidOf C d pl) = some s := h
        obtain rfl := Option.some.inj h1
        rcases y' with (u' | pl') | v'
        · cases h'
        · have h1' : some (saidOf C d pl') = some s' := h'
          obtain rfl := Option.some.inj h1'
          obtain ⟨f, f'⟩ := hf d rfl
          obtain ⟨a, b⟩ := saidOf_inj C d rt rt' pl pl' f f' em en
          exact ⟨a, by rw [b]⟩
        · have h1' : (saidLo C ds v').map Said.next = some s' := h'
          obtain ⟨t', -, rfl⟩ := Option.map_eq_some_iff.1 h1'
          exact absurd hk (Nat.succ_ne_zero t'.k).symm
      · have h1 : (saidLo C ds v).map Said.next = some s := h
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h1
        rcases y' with (u' | pl') | v'
        · cases h'
        · have h1' : some (saidOf C d pl') = some s' := h'
          obtain rfl := Option.some.inj h1'
          exact absurd hk (Nat.succ_ne_zero t.k)
        · have h1' : (saidLo C ds v').map Said.next = some s' := h'
          obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 h1'
          obtain ⟨a, b⟩ := saidLo_inj ds v v' t t' ht ht' (Nat.succ.inj hk)
            (fun d' hd => hf d' hd) em en
          exact ⟨a, by rw [b]⟩

/-- **Along a stretch of shared rounds.** -/
theorem saidSh_inj : ∀ (ds : List RDT)
    (w w' : PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)))
    (s s' : Said), saidSh C ds w = some s → saidSh C ds w' = some s' → s.k = s'.k →
    (∀ d, ds[s.k]? = some d →
      (toRoots d.items rt).isSome = true ∧ (toRoots d.items rt').isSome = true) →
    s.msg (rt.map digToBytes) = s'.msg (rt'.map digToBytes) → s.nonce = s'.nonce →
    rt = rt' ∧ w = w'
  | [], _, _, _, _, h, _, _, _, _, _ => by cases h
  | d :: ds, w, w', s, s', h, h', hk, hf, em, en => by
      obtain ⟨y, rfl⟩ : ∃ y : ((roundT C d).Plain ⊕ Unit) ⊕
          PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)), y = w := ⟨w, rfl⟩
      obtain ⟨y', rfl⟩ : ∃ y : ((roundT C d).Plain ⊕ Unit) ⊕
          PlainPart (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)), y = w' := ⟨w', rfl⟩
      rcases y with (pl | u) | v
      · have h1 : some (saidOf C d pl) = some s := h
        obtain rfl := Option.some.inj h1
        rcases y' with (pl' | u') | v'
        · have h1' : some (saidOf C d pl') = some s' := h'
          obtain rfl := Option.some.inj h1'
          obtain ⟨f, f'⟩ := hf d rfl
          obtain ⟨a, b⟩ := saidOf_inj C d rt rt' pl pl' f f' em en
          exact ⟨a, by rw [b]⟩
        · cases h'
        · have h1' : (saidSh C ds v').map Said.next = some s' := h'
          obtain ⟨t', -, rfl⟩ := Option.map_eq_some_iff.1 h1'
          exact absurd hk (Nat.succ_ne_zero t'.k).symm
      · cases h
      · have h1 : (saidSh C ds v).map Said.next = some s := h
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h1
        rcases y' with (pl' | u') | v'
        · have h1' : some (saidOf C d pl') = some s' := h'
          obtain rfl := Option.some.inj h1'
          exact absurd hk (Nat.succ_ne_zero t.k)
        · cases h'
        · have h1' : (saidSh C ds v').map Said.next = some s' := h'
          obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 h1'
          obtain ⟨a, b⟩ := saidSh_inj ds v v' t t' ht ht' (Nat.succ.inj hk)
            (fun d' hd => hf d' hd) em en
          exact ⟨a, by rw [b]⟩

end

end OnBytes.Maker.Page
