-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Run1IsProofs.lean: the proofs of the statements of Run/Run1Is.lean: the lenient parser's list at
`Fmt.formatHash` is the key of the description, and, under three tests, the outcome of the run function over
a single oracle is the run of a tree of oracle queries.

Limits: what the two statements do not claim is told in the head of Run/Run1Is.lean, under 4.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.Run1Is
import Run.RunIsPageHProofs
import Run.ParseLaws

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

theorem cutChain_pd (h : HId) (ops : ByteArray → OpsW Id) (S : _root_.Fmt.Spec) (b : ByteArray)
    (i : Nat) (o : _root_.Fmt.ChainOut) (j : Nat)
    (e : cutChain (m := Id) h ops S b i = some (o, j)) :
    o.pd = h 169 0 1 _root_.Fmt.zero32 S.params := by
  unfold cutChain at e
  split at e
  · cases e
  · dsimp only at e
    split at e
    · cases e
    · simp only [_root_.Fmt.paramsDigestW, idb] at e
      split at e
      · cases e
      · split at e
        · cases e
        · cases e
          rfl

theorem laxWhole_pd (h : HId) (S : _root_.Fmt.Spec) (b : ByteArray) (o : _root_.Fmt.ChainOut)
    (e : laxWhole (m := Id) h S b = some o) :
    o.pd = h 169 0 1 _root_.Fmt.zero32 S.params := by
  unfold laxWhole cutWhole at e
  simp only [idb] at e
  split at e
  · rename_i o' j hc
    have : o' = o := by
      simp only [idp] at e
      split at e
      · exact Option.some.inj e
      · cases e
    exact this ▸ cutChain_pd h _ S b 0 o' j hc
  · cases e

theorem parse_key {Y : Type} {E : ExtSpec} (P : PS Y E) (S : _root_.Fmt.Spec) (T : TypingP P)
    (b : ByteArray) (r : List (Dig 256) × OneProtocolProof 256 P.up)
    (e : parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b = some r) : r.1 = specKey S := by
  unfold parseLaxWP at e
  simp only [idb, idp] at e
  cases ho : laxWhole (m := Id) _root_.Fmt.formatHash S b with
  | none => rw [ho] at e; cases e
  | some o =>
    rw [ho] at e
    have e' : toBPrf T.up o = some r := (parseThin_to P T o).symm.trans e
    obtain ⟨run, pl, _, _, _, hx⟩ := (parseLaws_some T.up o r).1 e'
    rw [hx, laxWhole_pd _ S b o ho]
    rfl

theorem keep_key {Y : Type} {E : ExtSpec} (P : PS Y E) (S : _root_.Fmt.Spec)
    (T : TypingP P) (b : ByteArray) :
    keep (specKey S) (parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b) =
      (parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b).map Prod.snd := by
  cases hp : parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b with
  | none => rfl
  | some r =>
    show (if r.1 = specKey S then some r.2 else none) = some r.2
    rw [if_pos (parse_key P S T b r hp)]

theorem key_keep : Spec.key_keep := fun _ _ P S T b => keep_key P S T b

namespace PQ

theorem run1_is' (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) (hk : ok S = true)
    (h : OKQ S = true) (hs : smallB S file = true) :
    (tree1 S dec h file).run (oBits ()) = PMF.pure (decide (run1 S dec file = .accepted)) := by
  unfold tree1
  refine (run_pageW Unit Unit (kOf S + 1) (LbS (ck S.plan.field) (rds S) dec) Unit E0
      (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec)
      (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
      (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
      (fun s => some (.inl s)) 0 (pageQ S (ck S.plan.field) dec (kOf S + 1) h) (fun _ => S)
      (TYS S (ck S.plan.field) dec) (laxN S) (fun _ => Nat.le_refl _) (specKey S) () file hs).trans
    (congrArg PMF.pure ?_)
  rw [keep_key]
  unfold run1 run1On
  rw [if_pos hk, dif_pos h]
  cases hp : parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
      (TYS S (ck S.plan.field) dec) file with
  | none => rfl
  | some r =>
    obtain ⟨l, π⟩ := r
    have hl : l = specKey S := parse_key _ S _ file (l, π) hp
    subst hl
    show V1 S dec h _ π =
      decide ((if V1 S dec h _ π = true then Who.accepted else Who.verifier) = Who.accepted)
    cases V1 S dec h _ π <;> rfl

theorem run1_is : Spec.run1_is := fun S dec file hk h hs => run1_is' S dec file hk h hs

end PQ
end Run
