-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchHeldPush.lean: the rows of a held message's old sample, as the typed code switch
carries them to the open word's entries, against the sample row that the program made.

Behind the positions the typed block claims, among its rows, the old samples' rows on the slots
(`LdLocD.rowsOf`, Cb/Req1/LdSegAfterRows.lean): the coefficients of a held message's sample row,
carried along `hd.sJ` (`pushTo`, same file). At the programs' shapes (`heldPort`,
Johnson/Top/H/SwitchKept.lean) that map is one-to-one and its values are known
(Johnson/Top/H/SwitchHeldSel.lean). Johnson/Pack/FormPortZF.lean has the library's sample row
against the program's. Here the two are joined. Statements and proofs.
Main names:
  `heldPort_sJ`: entry (row r, place j) of a held message's main table stands in the kept slot of
    the member's row r, at the place j.
  `push_held_at`, `push_held_off`: coefficients c on a held message, carried to the open word's
    entries: at that slot and place, c at (r, j); at every entry that is no such slot and place, 0
    (`Cb.pushTo_off`, Cb/Ld/LdGroupNewRows.lean, with "a held message has no mask row").
  `sample_held_at`: with c the library's sample row at the seed's point and factor, read: the
    coefficient of the program's row `Send.form` at the index r + 2 ^ (row bits) * j of the
    message's main table.
Limits: those of FormPortZF.lean: one answer; no mask row; main rows over the base field; the seed's
point has as many coordinates as the cube has bits. That a record's stored sample row is
`Send.form` at a seed is a premise. Nothing on the row's target.

-/
import Johnson.Top.H.SwitchHeldSel
import Cb.Ld.LdGroupNewRows
import Johnson.Pack.FormPortZF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack

variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop)

set_option quotPrecheck false in
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // kp a})

/-- Where an entry of a held message's main table stands in the open word. -/
theorem heldPort_sJ (k : {a // (hP).cl a})
    (x : Fin (l.get k.1.1).1.mainRows × Fin (cMain cs (l.get k.1.1).1).l) :
    (hP).sJ k (.inl x) = .inl (some ⟨aK k, x.1⟩, Fin.cast (congrArg Fmt.M1.Code.l
      (hM k.1.1 k.2.fst (h1 ⟨k.1.1, k.2.fst⟩ k.2.snd))) x.2) := by
  show Sum.inl (some ((hP).slot k ((hP).cJ k (.inl x)).1), ((hP).cJ k (.inl x)).2) = _
  rw [heldPort_cJ]
  rfl

/-- **Coefficients on a held message, carried to the open word's entries**: at the kept slot of the
member's row r, at the place j: the coefficient at (r, j). -/
theorem push_held_at (k : {a // (hP).cl a}) (c : (portCode cs (l.get k.1.1).1).J → GE)
    (x : Fin (l.get k.1.1).1.mainRows × Fin (cMain cs (l.get k.1.1).1).l) :
    pushTo ((hP).sJ k) c ((hP).sJ k (.inl x)) = c (.inl x) := by
  classical
  unfold pushTo
  refine (Finset.sum_eq_single (Sum.inl x) ?_ ?_).trans (if_pos rfl)
  · intro i _ hi
    rw [if_neg]
    intro q
    rcases i with y | y
    · rw [heldPort_sJ, heldPort_sJ] at q
      have q1 := Sum.inl.inj q
      have q2 : y.1 = x.1 :=
        eq_of_heq (Sigma.mk.inj (Option.some.inj (congrArg Prod.fst q1))).2
      have q3 : y.2 = x.2 := Fin.ext (congrArg (fun z => z.2.val) q1)
      exact hi (congrArg Sum.inl (Prod.ext q2 q3))
    · have hz : (l.get k.1.1).1.maskRows = 0 := h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
      exact absurd y.1.isLt (by omega)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Elsewhere: 0. -/
theorem push_held_off (k : {a // (hP).cl a}) (c : (portCode cs (l.get k.1.1).1).J → GE)
    (n : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.J) (hn : ∀ x, (hP).sJ k (.inl x) ≠ n) :
    pushTo ((hP).sJ k) c n = 0 := by
  refine pushTo_off _ _ _ fun i => ?_
  rcases i with y | y
  · exact hn y
  · have hz : (l.get k.1.1).1.maskRows = 0 := h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
    exact absurd y.1.isLt (by omega)

/-- **An old sample's row, carried to the open word's entries, is the program's sample row**: smp:
the row that the program makes for the held message (number o) at the seed; the typed seed is the
seed's point and factor, read. At the kept slot of the member's row r, at the place j: the program's
coefficient at the index r + 2 ^ (row bits) * j of the message's main table. -/
theorem sample_held_at (k : {a // (hP).cl a}) (o : ℕ) (seed : SampleSeed) (smp : Row)
    (h : Send.form cs (l.get k.1.1).1 o seed 0 = some smp) (ha : (l.get k.1.1).1.answers = 1)
    (hF : CaseF (l.get k.1.1).1) (hz : seed.z.length = bitsZ cs (l.get k.1.1).1) (β : GEˣ)
    (hβ : (β : GE) = readE seed.beta)
    (x : Fin (l.get k.1.1).1.mainRows × Fin (cMain cs (l.get k.1.1).1).l) :
    pushTo ((hP).sJ k)
        ((portZ cs (l.get k.1.1).1).mat (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) ())
        ((hP).sJ k (.inl x)) =
      coefAt smp o .main (x.1.val + 2 ^ k1 (l.get k.1.1).1 * x.2.val) := by
  rw [push_held_at]
  exact (form_portZ_F cs (l.get k.1.1).1 o seed smp h ha hF hz β hβ (.inl x)).symm

end Johnson.Top.H

#print axioms Johnson.Top.H.heldPort_sJ
#print axioms Johnson.Top.H.push_held_at
#print axioms Johnson.Top.H.push_held_off
#print axioms Johnson.Top.H.sample_held_at
