-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/ViewWord.lean (kind K10): THE TEXT OF A MEMBER's CHANGE OF SHAPE
(`R.view a`) AT THE PROGRAMS' OWN MEMBER, ON WORDS: the verifier's side of ViewText.lean (beside
this
file), which has the messages' side. Statements and proofs.

What is said. f: a member's native word: at a native position of its main table (below 2 to the main
code's a) a symbol a main row; at a position of its tree (below 2 to aOf) a symbol a mask row.
  `tabSame_wd`, `maskSame_wd`, `mainAt_wd`, `maskAt_wd`: a table's change of shape, on words: a main
    table does not move; a mask table is read at the stage's position modulo the member's tree's
    length.
  `membPort_wd_main`, `membPort_wd_mask`: the same of the member's whole change of shape.
  `view_long_main`: **THE LONG SYMBOL OF THE MEMBER's NEW WORD AT THE GROUP's LONG POSITION x, MAIN
    ROW j, IS THE NATIVE WORD's SYMBOL OF ROW j AT x MODULO THE MAIN CODE's LENGTH.**
  `view_long_mask`: **AT THE MASK ROW j: THE NATIVE WORD's SYMBOL OF ROW j AT x MODULO THE MEMBER's
    TREE's LENGTH.**
  `port_long_main`, `port_long_mask`: the same at the group of the programs' shapes with kept
    members (`Rows.keep (rowsPort ..) kp`): the long symbol of the family's new word
    (`(RP).Sh.view.wd F`) at member a.

Limits. General in cs, l, mem, the stage and the corners. It says what the typed change of shape
does
to a native word; HOW A NATIVE WORD SITS TO A TREE's LEAF STRINGS OR TO A COLUMN OF THE VERIFIER's
TEXT IS NOT SAID HERE. Nothing on gather, arrange or the fold behind the view. Nothing on soundness.

-/
import Johnson.Top.H.SwitchKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

/-- A table under the stage's code, on words: nothing moves. -/
theorem tabSame_wd (e : C' = C) (f) (p : Fin (2 ^ C.a)) (p' : Fin (2 ^ C'.a))
    (hp : p'.val = p.val) (j : Fin n) :
    (tabSame C C' a a' n pos e).wd f p (j, ()) = f p' (j, ()) := by
  subst e
  obtain rfl : p' = p := Fin.ext hp
  rfl

/-- A table of mask rows, on words: read at the position modulo the tree's length. -/
theorem maskSame_wd (e : C' = C) (f) (x : Fin (2 ^ a)) (j : Fin n) :
    (maskSame C C' a a' n e).wd f x (j, ()) = f (modP a' a x) (j, ()) := by
  subst e
  rfl

end Tables

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

theorem mainAt_wd (f) (p : Fin (2 ^ s.C.a)) (p' : Fin (2 ^ (cMain cs sh).a))
    (hp : p'.val = p.val) (j : Fin sh.mainRows) :
    (Johnson.Top.H.mainAt cs sh s hM).wd f p (j, ()) = f p' (j, ()) := by
  unfold Johnson.Top.H.mainAt
  split
  · next h0 => exact absurd j.isLt (by omega)
  · exact tabSame_wd _ _ _ _ _ _ _ f p p' hp j

theorem maskAt_wd (f) (x : Fin (2 ^ s.C.a)) (j : Fin sh.maskRows) :
    (Johnson.Top.H.maskAt cs sh s hZ).wd f x (j, ()) = f (modP (aOf cs sh) s.C.a x) (j, ()) := by
  unfold Johnson.Top.H.maskAt
  split
  · next h0 => exact absurd j.isLt (by omega)
  · exact maskSame_wd _ _ _ _ _ _ f x j

/-- The member's whole change of shape, on words, at a main row. -/
theorem membPort_wd_main (f) (p : Fin (2 ^ s.C.a)) (p' : Fin (2 ^ (cMain cs sh).a))
    (hp : p'.val = p.val) (j : Fin sh.mainRows) :
    (membPort cs sh em s oM oZ hM hZ).view.wd f (.inl p) (j, ()) = f (.inl p') (j, ()) := by
  have h := mainAt_wd cs sh s hM (fun q => f (.inl q)) p p' hp j
  exact h

/-- And at a mask row. -/
theorem membPort_wd_mask (f) (x : Fin (2 ^ s.C.a)) (j : Fin sh.maskRows) :
    (membPort cs sh em s oM oZ hM hZ).view.wd f (.inr x) (j, ()) =
      f (.inr (modP (aOf cs sh) s.C.a x)) (j, ()) := by
  have h := maskAt_wd cs sh s hZ (fun q => f (.inr q)) x j
  exact h

/-- **THE LONG SYMBOL AT A MAIN ROW.** -/
theorem view_long_main (f) (x : s.Ps) (p' : Fin (2 ^ (cMain cs sh).a))
    (hp : p'.val = x.val % 2 ^ s.C.a) (j : Fin sh.mainRows) :
    ((s.cM.il (Fin sh.mainRows)).pair (s.cZ.il (Fin sh.maskRows))).T
      ((membPort cs sh em s oM oZ hM hZ).view.wd f) x (.inl (j, ())) = f (.inl p') (j, ()) :=
  membPort_wd_main cs sh em s oM oZ hM hZ f (posIn s.C x) p' hp j

/-- **THE LONG SYMBOL AT A MASK ROW.** -/
theorem view_long_mask (f) (x : s.Ps) (j : Fin sh.maskRows) :
    ((s.cM.il (Fin sh.mainRows)).pair (s.cZ.il (Fin sh.maskRows))).T
      ((membPort cs sh em s oM oZ hM hZ).view.wd f) x (.inr (j, ())) =
      f (.inr (modP (aOf cs sh) s.C.a x)) (j, ()) :=
  membPort_wd_mask cs sh em s oM oZ hM hZ f x j

end Port

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **AT THE GROUP: the long symbol of the family's new word at member a, main row j.** -/
theorem port_long_main (F : (RP).G.C.Word) (a : {i // mem i}) (x : s.Ps)
    (p' : Fin (2 ^ (cMain cs (l.get a.1).1).a)) (hp : p'.val = x.val % 2 ^ s.C.a)
    (j : Fin (l.get a.1).1.mainRows) :
    (LdCode.fam fun b : (RP).G.A => (s.cM.il (Fin ((RP).nM b))).pair (s.cZ.il (Fin ((RP).nZ b)))).T
      ((RP).Sh.view.wd F) x ⟨a, .inl (j, ())⟩ = F ⟨a, .inl p'⟩ (j, ()) :=
  view_long_main cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2) (hZ a.1 a.2)
    (fun q => F ⟨a, q⟩) x p' hp j

/-- **AND AT THE MASK ROW j.** -/
theorem port_long_mask (F : (RP).G.C.Word) (a : {i // mem i}) (x : s.Ps)
    (j : Fin (l.get a.1).1.maskRows) :
    (LdCode.fam fun b : (RP).G.A => (s.cM.il (Fin ((RP).nM b))).pair (s.cZ.il (Fin ((RP).nZ b)))).T
      ((RP).Sh.view.wd F) x ⟨a, .inr (j, ())⟩ =
      F ⟨a, .inr (modP (aOf cs (l.get a.1).1) s.C.a x)⟩ (j, ()) :=
  view_long_mask cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2) (hZ a.1 a.2)
    (fun q => F ⟨a, q⟩) x j

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.view_long_main
#print axioms VerifiableInference.Desc.First.Close.view_long_mask
#print axioms VerifiableInference.Desc.First.Close.port_long_main
#print axioms VerifiableInference.Desc.First.Close.port_long_mask
