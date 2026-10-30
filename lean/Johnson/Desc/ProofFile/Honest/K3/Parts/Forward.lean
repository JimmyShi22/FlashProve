-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Forward.lean: the honest side of the kind "lookup" (K3): at
any number of parts of keys: the forward pieces that Honest/K3/Law/Forward.lean has at one part
alone: the parts' step, the parts' key trees, and the whole hearing from its pieces' results in
order. Conditional. General in the face. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, part, key tree, sumcheck, ledger, round and face.

What is shown.
  `partsV_zero_ret`, `partsV_succ_ret`: the parts' step: at its end; one step, from the return of
    its sumcheck.
  `keysV_nil_ret`, `keysV_cons_ret`: the key trees: behind the last; one tree, from the return of
    its run.
  `messagesV_introP`: the lookup's rounds are heard, where the pieces return one after the other,
    each from the ledger and the rounds that the one in front has left, and the three counts hold.

Hypotheses that remain.
  `h1`, `h2`: (in the two steps) the return of the piece in front, and of what follows it.
  `hkl`, `hsz`, `hslots`, `hlins`: (in `messagesV_introP`) the hearing's three tests on counts: as
    many key forms as parts; the table side's point has its size; and, the third test's two clauses,
    the ledger's count has gone on by the face's slots and there are as many rows as the face's
    number lins. Besides, the return of every piece is a hypothesis: `e5` to `e16`, ten of them, in
    the order of the text.

Users. Honest/K3/Shape/Returns.lean calls all five; Honest/K3/Parts/LookHeard.lean imports this file
too.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
No statement of this file says that a masked sumcheck's text returns: that is a hypothesis at every
piece. Nothing is said of what the values mean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Forward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE mulE subE)
open OnBytes.Model (Fork Aff orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV messagesV Hr drawsV drawV sumV openV tieV partsV keysV
  noVar leafVars
  bitsCall)
open VerifiableInference.Desc.First.ProdV (Carried)
open ProofFile.Honest.K3.Forward

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

theorem partsV_zero_ret (rows : Array Aff) (C : Aff) (F : Fork) (rs : List Fmt.RoundView) :
    partsV 0 rows C F rs = some ((rows, [C]), F, rs) := rfl

/-- One step of the parts' step. -/
theorem partsV_succ_ret {n : Nat} {rows : Array Aff} {C : Aff} {F F1 G : Fork}
    {rs r1 rest : List Fmt.RoundView} {w : MaskedSum.Heard × Aff} {x : Array Aff × List Aff}
    (h1 : sumV C (noVar 2 2) (fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) F rs =
      some (w, F1, r1))
    (h2 : partsV n (rows.push w.2) (Aff.slot (w.1.sEnd + 1)) F1 r1 = some (x, G, rest)) :
    partsV (n + 1) rows C F rs = some ((x.1, Aff.slot w.1.sEnd :: x.2), G, rest) := by
  unfold partsV
  refine (bind_ret h1).trans ?_
  refine (bind_ret h2).trans ?_
  rfl

theorem keysV_nil_ret (f : LFace) (Cs : List Aff) (rows : Array Aff) (F : Fork)
    (rs : List Fmt.RoundView) : keysV f [] Cs rows F rs = some ((rows, []), F, rs) := by
  unfold keysV
  rfl

/-- One part's key tree, in front of the others'. -/
theorem keysV_cons_ret {f : LFace} {x : Nat × Nat} {xs : List (Nat × Nat)} {C : Aff}
    {Cs : List Aff} {rows : Array Aff} {F F1 G : Fork} {rs r1 rest : List Fmt.RoundView} {k : Carried}
    {y : Array Aff × List (Array E × Aff)}
    (h1 : vRun 0 x.1 (f.orders x.2) { rows := rows, point := #[], form := C } F rs =
      some (k, F1, r1))
    (h2 : keysV f xs Cs k.rows F1 r1 = some (y, G, rest)) :
    keysV f (x :: xs) (C :: Cs) rows F rs = some ((y.1, (k.point, k.form) :: y.2), G, rest) := by
  unfold keysV
  refine (bind_ret (of_ret h1)).trans ?_
  refine (bind_ret h2).trans ?_
  rfl

/-- **The lookup's rounds are heard**, where the pieces return one after the other, each from the
ledger and the rounds that the one in front has left, and the three counts hold. General in the
face. Every piece's return is a hypothesis. No instance of these hypotheses is exhibited in this
file. -/
theorem messagesV_introP (f : LFace) {F F5 F6 F7 F8 F9 F10 F12 F14 F15 F16 : Fork}
    {rs r5 r6 r7 r8 r9 r10 r12 r14 r15 r16 : List Fmt.RoundView} {theta alpha : E}
    {rows rows2 rows3 : Array Aff} {sZ : Nat} {sG : Array Nat} {roots : List Aff} {jo ze : Array E}
    {keys : List (Array E × Aff)} {table : Carried} {leaves : MaskedSum.Heard}
    {bits : MaskedSum.Heard × Aff}
    (e5 : (if f.shifted then drawV else pure zeroE : Hr E) (owed3 F) rs = some (theta, F5, r5))
    (e6 : drawV F5 r5 = some (alpha, F6, r6))
    (e7 : tieV f.planes (f.factor theta alpha) F6 r6 = some ((rows, sZ, sG), F7, r7))
    (e8 : partsV (f.parts.length - 1) rows (Aff.slot sZ) F7 r7 = some ((rows2, roots), F8, r8))
    (e9 : drawsV f.mu F8 r8 = some (jo, F9, r9))
    (e10 : keysV f f.parts.zipIdx roots rows2 F9 r9 = some ((rows3, keys), F10, r10))
    (hkl : keys.length = f.parts.length)
    (e12 : vRun f.mu f.d orderDefault
      { rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse } F10 r10 =
      some (table, F12, r12))
    (hsz : table.point.size = f.mu + f.d)
    (e14 : openV table.form (leafVars f table.point) F12 r12 = some (leaves, F14, r14))
    (e15 : drawsV (f.mu + f.d) F14 r14 = some (ze, F15, r15))
    (e16 : sumV (Aff.ofConst zeroE) (bitsCall ze.reverse.toList) (fun _ x =>
      subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F15 r15 =
      some (bits, F16, r16))
    (hslots : F16.next = F.next + f.slots) (hlins : (table.rows.push bits.2).size = f.lins) :
    messagesV f F rs = some
      ({ theta := theta, alpha := alpha, a := f.factor theta alpha
         rows := table.rows.push bits.2, leaves := leaves, sBit := bits.1.sEnd
         keys := keys, zb0 := leaves.r.toArray
         zb1 := (bits.1.r.take (f.mu + f.d)).toArray
         owedObjects := (F.owe "look-up-mask-claims").1
         owedPlanes := ((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").1
         owedJoin :=
           (((F.owe "look-up-mask-claims").2.owe "look-up-plane-claims").2.owe "look-up-join").1 },
        F16, r16) := by
  unfold messagesV
  dsimp only
  refine (bind_ret (slot_ret _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (bind_ret (owe_ret _ _ _)).trans ?_
  refine (ite_bind_ret e5).trans ?_
  refine (bind_ret e6).trans ?_
  refine (bind_ret e7).trans ?_
  refine (bind_ret e8).trans ?_
  refine (bind_ret e9).trans ?_
  refine (bind_ret e10).trans ?_
  have m1 : (keys.length == f.parts.length) = true := by simp [hkl]
  refine (bind_ret (by dsimp only; rw [m1]; exact must_ret _ _)).trans ?_
  refine (bind_ret (of_ret e12)).trans ?_
  have m2 : (table.point.size == f.mu + f.d) = true := by simp [hsz]
  refine (bind_ret (by rw [m2]; exact must_ret _ _)).trans ?_
  refine (bind_ret e14).trans ?_
  refine (bind_ret e15).trans ?_
  refine (bind_ret e16).trans ?_
  refine (bind_ret (slot_ret _ _)).trans ?_
  have m3 : (F16.next == F.next + f.slots && (table.rows.push bits.2).size == f.lins) = true := by
    simp [hslots, hlins]
  refine (bind_ret (by rw [m3]; exact must_ret _ _)).trans ?_
  rfl

#print axioms ProofFile.Honest.K3.Parts.partsV_zero_ret
#print axioms ProofFile.Honest.K3.Parts.partsV_succ_ret
#print axioms ProofFile.Honest.K3.Parts.keysV_nil_ret
#print axioms ProofFile.Honest.K3.Parts.keysV_cons_ret
#print axioms ProofFile.Honest.K3.Parts.messagesV_introP

end ProofFile.Honest.K3.Parts
