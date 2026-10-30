-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RbrLast.lean: the rounds after a part of a protocol can be replaced, under the condition below.
(Words of this library: lean/GLOSSARY.md.)
If the prover is doomed (`Doomed`) in s ++ t, and after every transcript of s "lost in t" implies
"lost in t'" (lost: doomed), then it is doomed in s ++ t', with the same errors in s.
Use: a last message sent in the clear is replaced by an encoded one with a sub-protocol that proves
a claim on it.
-/
import Iop.Rbr

namespace Iop
open Prob

/-- Replace what follows the first round, under `h` and `hd`. -/
theorem Doomed.cons_tail {r : Round} {s s' : Shape} {e : ℕ} {ε : Err s} {ε' : Err s'}
    {bad : Tr (r :: s) → Prop} {bad' : Tr (r :: s') → Prop}
    (h : ∀ m c, Doomed s ε (fun τ => bad (m, c, τ)) → Doomed s' ε' (fun τ => bad' (m, c, τ)))
    (hd : Doomed (r :: s) (e, ε) bad) : Doomed (r :: s') (e, ε') bad' :=
  fun m => le_trans (cnt_mono fun c hc hd' => hc (h m c hd')) (hd m)

/-- Replace what follows the part s, under the hypotheses below. -/
theorem Doomed.replace_tail :
    ∀ (s : Shape) {t t' : Shape} (ε : Err s) (εt : Err t) (εt' : Err t')
        (bad : Tr (s ++ t) → Prop) (bad' : Tr (s ++ t') → Prop),
      (∀ a : Tr s,
        Doomed t εt (fun b => bad (Tr.app a b)) → Doomed t' εt' (fun b => bad' (Tr.app a b))) →
      Doomed (s ++ t) (Err.app ε εt) bad → Doomed (s ++ t') (Err.app ε εt') bad'
  | [], _, _, _, _, _, _, _, h, hd => h () hd
  | _ :: s, _, _, (_, ε), εt, εt', _, _, h, hd =>
      Doomed.cons_tail (fun m c hd' =>
        Doomed.replace_tail s ε εt εt' _ _ (fun a => h (m, c, a)) hd') hd

/-- The converse of sequential composition (`Doomed.append`, Iop/Rbr.lean): doomed in s ++ t gives
doomed in s towards the goal that the prover is doomed in t. -/
theorem Doomed.split :
    ∀ (s t : Shape) (ε : Err s) (ε' : Err t) (bad : Tr (s ++ t) → Prop),
      Doomed (s ++ t) (Err.app ε ε') bad →
      Doomed s ε (fun a => Doomed t ε' (fun b => bad (Tr.app a b)))
  | [], _, _, _, _, h => h
  | _ :: s, t, (_, ε), ε', bad, h => fun m =>
      le_trans (cnt_mono
        (fun c hc hd' => hc (Doomed.split s t ε ε' (fun τ => bad (m, c, τ)) hd'))) (h m)

end Iop
