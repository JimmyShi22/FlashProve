-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Draws.lean: a written verifier message, read as field elements and positions.

In the protocol that a file holds, a round's verifier message is the round's hash blocks, with test
bits where the round asks for work (Run/PlanQS.lean: `roundS`, with hash blocks as challenges,
`Run.ckP`). The format's sampler makes typed values from the blocks (Run/PlanDraws.lean: `bsRound`):
elements of the extension field, elements other than 0, positions. The library's theory draws
elements of `Cb.Gl.E` and positions directly. This file has the map from the one to the other in the
form that OnBytes/Slice/Carry.lean asks for, with its bound on how many written messages go to one
value.

Main definitions.
 `evE`               a typed element as an element of the field.
 `elemsV`, `possV`   the elements and the positions among the typed values of a list of draws.
 `valsOf d c`        the typed values of the written verifier message c of the round d.
 `chalTo d g`        the map of verifier messages: `none` if the test of work fails, else g of the
                     typed values.
Main theorems.
 `evE_inj`           different typed elements are different field elements.
 `vals_inj`          typed values are determined by their elements and positions, if the list of
                     draws has nothing else (`PlainDraws`).
 `collect_elems`, `collect_poss`   the same lists, read off the format's record of what was drawn.
 `chalTo_fib`        if g is injective and the round's positions have at most 64 bits, at most w
                     written messages go to one value, where w is the sampler's own bound on how
                     many strings of blocks give one value.
Not claimed. Nothing on a protocol. Nothing on the hash: blocks are arbitrary strings here, and they
are counted.
-/
import Run.PlanPull
import Iop.GrindProofs
import OnBytes.Slice.Field
import OnBytes.Slice.Carry

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run

/-- The field with p = 2^64 - 2^32 + 1 elements and its cubic extension (X^3 = 2), as the library's
theory has them. -/
abbrev GF : Type := Cb.Gl.F
/-- See `GF`. -/
abbrev GE : Type := Cb.Gl.E

/-- A typed element of the extension field, as an element of the field. -/
def evE (e : EV .two) : GE := toE (toU3 e)

theorem ok_toU (x : FV .two) : Fmt.Fld.two.ok (toU x) = true := by
  unfold Fmt.Fld.ok
  rw [toU_toNat]
  exact decide_eq_true x.isLt

theorem okE_toU3 (e : EV .two) : Fmt.Fld.two.okE (toU3 e) = true := by
  simp only [Fmt.Fld.okE, toU3, ok_toU, Bool.and_self]

/-- Different typed elements are different field elements. -/
theorem evE_inj : Function.Injective evE := fun a b h =>
  toU3_inj (toE_inj _ _ (okE_toU3 a) (okE_toU3 b) h)

/-- The elements among the typed values of a list of draws, in their order. -/
def elemsV : (ds : List Fmt.Draw) → Vals .two ds → List GE
  | [], _ => []
  | .elem :: ds, v => evE v.1 :: elemsV ds v.2
  | .elemNZ :: ds, v => evE v.1.1 :: elemsV ds v.2
  | .pos _ :: ds, v => elemsV ds v.2
  | .trits _ :: ds, v => elemsV ds v.2
  | .sealed :: ds, v => elemsV ds v.2

/-- The positions among the typed values of a list of draws, in their order. -/
def possV : (ds : List Fmt.Draw) → Vals .two ds → List ℕ
  | [], _ => []
  | .elem :: ds, v => possV ds v.2
  | .elemNZ :: ds, v => possV ds v.2
  | .pos _ :: ds, v => v.1.val :: possV ds v.2
  | .trits _ :: ds, v => possV ds v.2
  | .sealed :: ds, v => possV ds v.2

/-- The list of draws has elements and positions alone, but for empty draws of matrix entries. -/
def PlainDraws : List Fmt.Draw → Prop
  | [] => True
  | .elem :: ds => PlainDraws ds
  | .elemNZ :: ds => PlainDraws ds
  | .pos _ :: ds => PlainDraws ds
  | .trits n :: ds => n = 0 ∧ PlainDraws ds
  | .sealed :: _ => False

/-- Typed values are determined by their elements and positions. -/
theorem vals_inj : ∀ (ds : List Fmt.Draw), PlainDraws ds → ∀ v w : Vals .two ds,
    elemsV ds v = elemsV ds w → possV ds v = possV ds w → v = w
  | [], _, _, _, _, _ => rfl
  | .elem :: ds, h, v, w, he, hp => by
      have h1 := List.cons.inj he
      exact Prod.ext (evE_inj h1.1) (vals_inj ds h v.2 w.2 h1.2 hp)
  | .elemNZ :: ds, h, v, w, he, hp => by
      have h1 := List.cons.inj he
      exact Prod.ext (Subtype.ext (evE_inj h1.1)) (vals_inj ds h v.2 w.2 h1.2 hp)
  | .pos _ :: ds, h, v, w, he, hp => by
      have h1 := List.cons.inj hp
      exact Prod.ext (Fin.ext h1.1) (vals_inj ds h v.2 w.2 he h1.2)
  | .trits n :: ds, h, v, w, he, hp => by
      obtain ⟨rfl, h2⟩ := h
      exact Prod.ext (funext fun i => i.elim0) (vals_inj ds h2 v.2 w.2 he hp)
  | .sealed :: _, h, _, _, _, _ => h.elim

/-- The elements in the format's record of what was drawn are these. -/
theorem collect_elems : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    (Fmt.collect (outAll .two ds v)).elems.map toE = elemsV ds v
  | [], _ => rfl
  | .elem :: ds, v => congrArg (evE v.1 :: ·) (collect_elems ds v.2)
  | .elemNZ :: ds, v => congrArg (evE v.1.1 :: ·) (collect_elems ds v.2)
  | .pos _ :: ds, v => collect_elems ds v.2
  | .trits _ :: ds, v => collect_elems ds v.2
  | .sealed :: ds, v => collect_elems ds v.2

/-- The positions in the format's record of what was drawn are these. -/
theorem collect_poss : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    (Fmt.collect (outAll .two ds v)).poss = possV ds v
  | [], _ => rfl
  | .elem :: ds, v => collect_poss ds v.2
  | .elemNZ :: ds, v => collect_poss ds v.2
  | .pos _ :: ds, v => congrArg (v.1.val :: ·) (collect_poss ds v.2)
  | .trits _ :: ds, v => collect_poss ds v.2
  | .sealed :: ds, v => collect_poss ds v.2

/-- The number of elements, and of positions, among a list of draws. -/
def nE : List Fmt.Draw → ℕ
  | [] => 0
  | .elem :: ds => nE ds + 1
  | .elemNZ :: ds => nE ds + 1
  | _ :: ds => nE ds

/-- See `nE`. -/
def nP : List Fmt.Draw → ℕ
  | [] => 0
  | .pos _ :: ds => nP ds + 1
  | _ :: ds => nP ds

theorem elemsV_length : ∀ (ds : List Fmt.Draw) (v : Vals .two ds), (elemsV ds v).length = nE ds
  | [], _ => rfl
  | .elem :: ds, v => congrArg (· + 1) (elemsV_length ds v.2)
  | .elemNZ :: ds, v => congrArg (· + 1) (elemsV_length ds v.2)
  | .pos _ :: ds, v => elemsV_length ds v.2
  | .trits _ :: ds, v => elemsV_length ds v.2
  | .sealed :: ds, v => elemsV_length ds v.2

theorem possV_length : ∀ (ds : List Fmt.Draw) (v : Vals .two ds), (possV ds v).length = nP ds
  | [], _ => rfl
  | .elem :: ds, v => possV_length ds v.2
  | .elemNZ :: ds, v => possV_length ds v.2
  | .pos _ :: ds, v => congrArg (· + 1) (possV_length ds v.2)
  | .trits _ :: ds, v => possV_length ds v.2
  | .sealed :: ds, v => possV_length ds v.2

/-- Every position among the draws is drawn below 2^k. -/
def AllPos (k : ℕ) : List Fmt.Draw → Prop
  | [] => True
  | .pos k' :: ds => k' = k ∧ AllPos k ds
  | _ :: ds => AllPos k ds

theorem possV_lt (k : ℕ) : ∀ (ds : List Fmt.Draw), AllPos k ds → ∀ (v : Vals .two ds),
    ∀ x ∈ possV ds v, x < 2 ^ k
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | .elem :: ds, h, v, x, hx => possV_lt k ds h v.2 x hx
  | .elemNZ :: ds, h, v, x, hx => possV_lt k ds h v.2 x hx
  | .pos _ :: ds, h, v, x, hx => by
      obtain ⟨rfl, h2⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact v.1.isLt
      · exact possV_lt _ ds h2 v.2 x hx
  | .trits _ :: ds, h, v, x, hx => possV_lt k ds h v.2 x hx
  | .sealed :: ds, h, v, x, hx => possV_lt k ds h v.2 x hx

/-- The element number i among the draws is drawn other than 0. -/
def IsNZ : List Fmt.Draw → ℕ → Prop
  | [], _ => False
  | .elem :: _, 0 => False
  | .elem :: ds, i + 1 => IsNZ ds i
  | .elemNZ :: _, 0 => True
  | .elemNZ :: ds, i + 1 => IsNZ ds i
  | .pos _ :: ds, i => IsNZ ds i
  | .trits _ :: ds, i => IsNZ ds i
  | .sealed :: ds, i => IsNZ ds i

theorem evE_zero : evE (zF .two, zF .two, zF .two) = 0 := toE_zeroE

theorem elemsV_nz : ∀ (ds : List Fmt.Draw) (i : ℕ), IsNZ ds i → ∀ v : Vals .two ds,
    (elemsV ds v).getD i 0 ≠ 0
  | [], _, h, _ => h.elim
  | .elem :: _, 0, h, _ => h.elim
  | .elem :: ds, i + 1, h, v => elemsV_nz ds i h v.2
  | .elemNZ :: _, 0, _, v => fun h0 => v.1.2 (evE_inj (h0.trans evE_zero.symm))
  | .elemNZ :: ds, i + 1, h, v => elemsV_nz ds i h v.2
  | .pos _ :: ds, i, h, v => elemsV_nz ds i h v.2
  | .trits _ :: ds, i, h, v => elemsV_nz ds i h v.2
  | .sealed :: ds, i, h, v => elemsV_nz ds i h v.2

/-- Two lists of one length with the same entries are equal. -/
theorem list_ext_getD {α : Type} (d : α) {l l' : List α} (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i d = l'.getD i d) : l = l' := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := h i h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-- The written round d, as a round of the library. -/
abbrev wRound (d : PQ.RD) : Round := (PQ.roundS (ckP .two) d).up

/-- The typed values of a written verifier message. -/
def valsOf (d : PQ.RD) (c : (wRound d).Chal) : Vals .two (Fmt.dsOf d.entry d.kind) :=
  (bsRound .two d.entry d.kind).φ (GChal.old (b := d.entry.work) c)

/-- The map of verifier messages: nothing if the test of work fails, else g of the typed values. -/
def chalTo {C' : Type} (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → C') :
    (wRound d).Chal → Option C' := fun c =>
  if GChal.pass (b := d.entry.work) c = true then some (g (valsOf d c)) else none

/-- If g is injective and the round's positions have at most 64 bits, at most w written verifier
messages go to one value. -/
theorem chalTo_fib {C' : Type} (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → C')
    (hg : Function.Injective g) (hlog : d.entry.logN ≤ 64) (c' : C') :
    cnt (fun c => chalTo d g c = some c') ≤ (bsRound .two d.entry d.kind).w := by
  have h1 : cnt (fun c => chalTo d g c = some c') ≤
      cnt (fun c : GChal d.entry.work (Fin (bsRound .two d.entry d.kind).b → Dig 256) =>
        GChal.pass c = true ∧ g ((bsRound .two d.entry d.kind).φ (GChal.old c)) = c') := by
    refine cnt_mono fun c hc => ?_
    unfold chalTo at hc
    split at hc
    · next hp => exact ⟨hp, Option.some.inj hc⟩
    · cases hc
  rw [GChal.cnt_pass d.entry.work
    (fun u => g ((bsRound .two d.entry d.kind).φ u) = c')] at h1
  refine h1.trans ?_
  by_cases hv : ∃ v, g v = c'
  · obtain ⟨v, hv⟩ := hv
    exact (cnt_mono fun u hu => hg (hu.trans hv.symm)).trans
      ((planDraws_law .two d.entry d.kind hlog).1.fib v)
  · exact (le_of_eq (cnt_false fun u hu => hv ⟨_, hu⟩)).trans (Nat.zero_le _)

/-- A verifier message without an image has failed its test of work. -/
theorem chalTo_none {C' : Type} (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → C')
    (c : (wRound d).Chal) (h : chalTo d g c = none) : GChal.pass (b := d.entry.work) c = false := by
  unfold chalTo at h
  split at h
  · cases h
  · next hp => exact Bool.eq_false_iff.2 hp

end OnBytes.Slice

#print axioms OnBytes.Slice.vals_inj
#print axioms OnBytes.Slice.chalTo_fib
