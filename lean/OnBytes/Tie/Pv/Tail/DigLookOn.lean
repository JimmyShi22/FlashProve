-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/DigLookOn.lean: the lookup on the digits of a smallness test as a block of the
link of a sub-proof, as a frame needs it: the lookup's entries are read off all messages of the
link, and there are conditions on statements: one carried past the lookup, one born at its output.

The seam in front of the lookup (Cb/Pv/Tail/InSubSeam.lean) reads the late message with the digits
alone, and its joints have the condition "True" on statements. A frame needs more of the lookup, in
three ways.

The entries. The lookup's end claims read the digits and the bits of the counts, which stand in the
late message, and entries of the link's mask row, which is sent at the link's start. So here the
lookup's entries are a letter on the whole tuple of messages (`msgL`, `msg₀`), which is asked to
agree with the late reading at the digits' places alone.

The condition in front. That the caller's ledger has at most n claims is a condition on the
statement in front, and the block behind the lookup, which batches one ledger, needs it at the
lookup's output. A condition P₂ on the statement in front is carried (`Cb.Pv.Att.ranCond`,
Cb/Pv/Att/RanCond.lean).

The condition behind. That block also lays the lookup's own end claims into the ledger, and the
lookup's out-statement holds a list of rows, which as a type is of any length. So behind the lookup
stands: P₂ at the statement in front, which the out-statement keeps, and the number of the
out-statement's rows.

No new proof of knowledge soundness is made. `Cb.Fo.hD₀` and `holeD_port` are general in the joint
R0 that rides along and in the reading of the entries; the joints in front and behind have R0's
condition; they are taken at R0 := ranCond eqs₁ P₂. The number of rows is `Fo.all_rows_len` and
`Fo.out_rows_len` (OnBytes/Tie/Pv/Lookup/Forest/FoOutLen.lean), laid on by `knowAt_ranCond`.

Main names:
  `P3 P₂ r`: the condition behind the lookup: P₂ at the statement in front, and r rows.
    `knowAt_born`: a condition that holds of whatever a block puts out is laid beside one that was
    carried.
  `outLM T left right k msgL`: the joint behind the lookup: `eqs₁` at the statement in front, and
    every form of `endCl` holds at the entries msgL m.
  `look_knowOn`: for every `LateU` with finite types, every `PlD` and every msgL that agrees with
    the late reading at the digits' places: `KnowAt` of `digB` from ranCond inD₁ P₂ to ranCond
    (outLM msgL) (P3 P₂ r), r := (P.n + 1) + (P.v' + 1) + d + 4.
  `look_forBOn`: the same for the block `forB` at h := tl.f9 and the letters `lateO`
    (DigLookPort.lean), at msgL m := zext (msg₀ m), with `Fo.nRows tl.f9` rows. Premises: three
    Bools, and the agreement at the digits' places.
  `tail3 T msg₃ endC i12 is e keep`: the letters `Tail3` of the last block
    (Cb/Pv/Tail/DigBatch.lean) at the lookup on the digits: the output statement is the lookup's
    own; `pr` gives back the statement in front; the end claims `endC` are a letter.
  `outD_of_outLM`: from ranCond (outLM msgL) P₃ to ranCond outD P₃ at `tail3`, for any reduction and
    any P₂, P₃, if endC x at the entries of all messages gives `endCl` x at msgL.
Limits: those of DigLookPort.lean. In `look_knowOn` the places of the lookup's masks and the orders
of its sumchecks are letters (`PlD`), and `NumOK` is a premise on public numbers; no statement here
says that `digB` and `forB` are one block. The forms of `endCl` are a function of the out-statement:
that they are the claims which the verifier adds is not said here. P₂, msgL and msg₀ are letters.
That `Fo.nRows tl.f9` + 1 is the number of claims which the verifier adds for this lookup is not
said here.

-/
import Cb.Pv.Tail.DigBatch
import Cb.Pv.Lookup.Digits.DigOut
import OnBytes.Tie.Pv.Lookup.Forest.FoOutLen
import OnBytes.Tie.Pv.Tail.DigLookPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.DgP Cb.Pv.Tail Cb.Pv.Att Iop IOR Cb.LdLkp Cb.Lkp Cb.Fo CbQ TWhole

/-- The condition behind the lookup: P₂ at the statement in front, and r rows. -/
def P3 {St E J : Type} {Ex : ExtSpec} (P₂ : St × Ex.Str → Prop) (r : ℕ) :
    TX (St × E) E J × Ex.Str → Prop := fun b => P₂ (b.1.1.1, b.2) ∧ b.1.2.2.length = r

/-- A condition that is born at a block's output, laid beside one that was carried. -/
theorem knowAt_born {K M X X' Wp Wp' : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp')}
    {ext : M → X × Ei.Str → Tr R.shape → Wp' → Wp} {ε : Err R.shape} {P : X × Ei.Str → Prop}
    {P' N : X' × Eo.Str → Prop} (h : KnowAt R (ranCond A P) (ranCond B P') ext ε)
    (hN : ∀ a τ b, R.red.out a τ = some b → N b) :
    KnowAt R (ranCond A P) (ranCond B fun b => P' b ∧ N b) ext ε :=
  knowAt_mono (knowAt_ranCond (fun _ => True) N h fun a τ b _ _ hb => hN a τ b hb)
    (fun _ h => ⟨h, trivial⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    (fun _ h => ⟨h.1.1, h.1.2, h.2⟩)

section
variable {E : Type} [Field E] {s : Size} {Λ : Letters E s} {U W₀ : Type}
  (T : LateU Λ U W₀) [Fintype T.I] [Fintype T.J] [DecidableEq T.J]
  {MM Kc : Type} (left : MM → Λ.M) (right : MM → U) (k : MM × W₀ → Kc) (msgL : MM → T.J → E)

/-- The joint behind the lookup, its entries read off all messages. -/
def outLM : Rels Kc (TX ((Λ.X × Dr s) × E) E T.J) Λ.E (MM × W₀) where
  rel x y v := (T.eqs₁ left right k).rel x.1.1 y v ∧
    TWhole.Ledger.Holds (T.Q.endCl x) (msgL v.1)
  relR b v := (T.eqs₁ left right k).relR (b.1.1.1, b.2) v ∧
    TWhole.Ledger.Holds (T.Q.endCl b.1) (msgL v.1)
  on _ := True
  core := k

variable [Fintype E] (P₂ : (Λ.X × Dr s) × Λ.E.Str → Prop)

/-- Knowledge soundness of the lookup on the digits, as a frame needs it. -/
theorem look_knowOn (P : PlD E T.J T.Q.d) (p : ℕ) [CharP E p] {q H : ℕ} (hQ : T.Q.DatOK q H p)
    (hN : NumOK T.Q P p)
    (hlo : ∀ m i, msgL m (T.Q.lo i) = T.ent (right m) (T.Q.lo i))
    (hhi : ∀ m i, msgL m (T.Q.hi i) = T.ent (right m) (T.Q.hi i)) :
    KnowAt (digB (Λ.X × Dr s) T.Q P (Ex := Λ.E)).R (ranCond (T.inD₁ left right k) P₂)
      (ranCond (outLM T left right k msgL) (P3 P₂ ((P.n + 1) + (P.v' + 1) + T.Q.d + 4)))
      Cb.Sub.idW (digB (Λ.X × Dr s) T.Q P (Ex := Λ.E)).e := by
  have h0 : KnowAt (digB (Λ.X × Dr s) T.Q P (Ex := Λ.E)).R (ranCond (T.inD₁ left right k) P₂)
      (ranCond (outLM T left right k msgL) fun b => P₂ (b.1.1.1, b.2)) Cb.Sub.idW
      (digB (Λ.X × Dr s) T.Q P (Ex := Λ.E)).e := by
    refine knowAt_mono
      (hD₀ E p (Λ.X × Dr s) T.I T.J T.Q P q H Λ.E Kc MM W₀ (ranCond (T.eqs₁ left right k) P₂)
        msgL hQ hN)
      (fun _ h => h) ?_ ?_ (fun _ h => h)
    · rintro a w _ ⟨h1, h2⟩
      have g := (dgQ_in T.Q hQ (msgL w.1)).1 h2
      refine ⟨h1, (dgQ_in T.Q hQ (T.ent (right w.1))).2 ⟨fun i => ?_, fun i => ?_⟩⟩
      · rw [← hlo w.1 i]
        exact g.1 i
      · rw [← hhi w.1 i]
        exact g.2 i
    · rintro b w _ ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := (endCl_iff T.Q hQ b.1 _).1 h2
      refine ⟨h1, ?_, h4, trivial⟩
      show b.1.2.1.Holds (P.v' + 1) _ _
      rw [← hN.1]
      exact h3
  exact knowAt_born h0 fun a τ b hb =>
    Fo.all_rows_len Λ.E (digA (Λ.X × Dr s) T.Q P) (T.Q.sh (Λ.X × Dr s)) true a τ b hb

end

/-- The same for the lookup of a sub-proof at the verifier's own numbers. -/
theorem look_forBOn {tl : HTailF2} {U W₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (Λ : Letters Cb.Gl.E (sizeOf tl).size) (h : colsTest tl = true) (entU : U → J₀ → Cb.Gl.E)
    (en : Ent3 → J₀) (bk : U → W₀ → Λ.W) (mk : ℕ → J₀) (jLK : ℕ)
    (H : FoNums.ok tl.f9 = true) (hs : shapeTest2 tl Cb.Gl.p = true)
    {MM Kc : Type} (left : MM → Λ.M) (right : MM → U) (k : MM × W₀ → Kc)
    (P₂ : (Λ.X × Dr (sizeOf tl).size) × Λ.E.Str → Prop) (msg₀ : MM → J₀ → Cb.Gl.E)
    (hlo : ∀ m i, msg₀ m (en ((portQ tl).lo i)) = entU (right m) (en ((portQ tl).lo i)))
    (hhi : ∀ m i, msg₀ m (en ((portQ tl).hi i)) = entU (right m) (en ((portQ tl).hi i))) :
    KnowAt
      (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK (Λ.X × Dr (sizeOf tl).size)) V₀ V₀C
        (Ex := Λ.E)).R
      (ranCond ((lateO Λ h entU en bk).inD₁ left right k) P₂)
      (ranCond (outLM (lateO Λ h entU en bk) left right k fun m => zext (msg₀ m))
        (P3 P₂ (Fo.nRows tl.f9)))
      Cb.Sub.idW
      (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK (Λ.X × Dr (sizeOf tl).size)) V₀ V₀C
        (Ex := Λ.E)).e := by
  obtain ⟨_, hT, hP⟩ := shape2_parts hs
  have hQ := lateU_ok Λ h (fun u => zext (entU u)) (fun n => some (en n)) bk hs
  have h0 : KnowAt
      (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK (Λ.X × Dr (sizeOf tl).size)) V₀ V₀C
        (Ex := Λ.E)).R
      (ranCond ((lateO Λ h entU en bk).inD₁ left right k) P₂)
      (ranCond (outLM (lateO Λ h entU en bk) left right k fun m => zext (msg₀ m))
        fun b => P₂ (b.1.1.1, b.2))
      Cb.Sub.idW
      (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK (Λ.X × Dr (sizeOf tl).size)) V₀ V₀C
        (Ex := Λ.E)).e := by
    refine knowAt_mono
      (holeD_port (Λ.X × Dr (sizeOf tl).size) tl en mk jLK Λ.E Kc MM W₀
        (ranCond ((lateO Λ h entU en bk).eqs₁ left right k) P₂) msg₀ H)
      (fun _ h => h) ?_ ?_ (fun _ h => h)
    · exact fun a w _ hw =>
        (forIn_iff_inD₁ Λ h entU en bk mk jLK hs left right k msg₀ hlo hhi a w).1 hw
    · rintro b w _ ⟨h1, h2⟩
      obtain ⟨h3, h4⟩ := (endCl_iff (portQJ tl fun n => some (en n)) hQ b.1 _).1 h2
      refine ⟨h1, ?_, h4, trivial⟩
      show b.1.2.1.Holds (FoNums.v' tl.f9 + 1) _ _
      rw [← ok_v H]
      have e := forA_key hT hP en mk jLK b.1.1 (zext (msg₀ w.1))
      show b.1.2.1.Holds tl.f9.v
        ((forA Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK (Λ.X × Dr (sizeOf tl).size))).key b.1.1
          (zext (msg₀ w.1))) _
      rw [e]
      exact h3
  exact knowAt_born h0 fun a τ b hb => Fo.out_rows_len tl.f9 _ Λ.E a τ b hb

section
variable {K : Type} [Field K] {s : Size} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  {Q : Host K s J₁ J₂} {U W₀ MM J₃ : Type} [Fintype J₃] [DecidableEq J₃]
  (T : LateU Q.let U W₀) [Fintype T.I] [Fintype T.J] [DecidableEq T.J]

/-- The letters of the last block, at the lookup on the digits. -/
def tail3 (msg₃ : MM → J₃ → K) (endC : TX ((Q.let.X × Dr s) × K) K T.J → TWhole.Ledger K J₃)
    (i12 : J₁ ⊕ J₂ → J₃) (is : Cb.Pv.Tail.J s → J₃) (e : Exps s)
    (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool) : Tail3 Q MM J₃ where
  X' := TX ((Q.let.X × Dr s) × K) K T.J
  pr := fun x => x.1.1
  msg₃ := msg₃
  endCl := endC
  i12 := i12
  is := is
  e := e
  keep := keep

omit [DecidableEq J₃] in
/-- From the joint on the lookup's own entries to the joint that the last block asks, the
conditions kept. -/
theorem outD_of_outLM (left : MM → Q.M) (right : MM → U) (k₂ : MM × W₀ → Q.Kc)
    (msgL : MM → T.J → K) (msg₃ : MM → J₃ → K)
    (endC : TX ((Q.let.X × Dr s) × K) K T.J → TWhole.Ledger K J₃)
    (i12 : J₁ ⊕ J₂ → J₃) (is : Cb.Pv.Tail.J s → J₃) (e : Exps s)
    (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool)
    (hE : ∀ x m, TWhole.Ledger.Holds (endC x) (msg₃ m) →
      TWhole.Ledger.Holds (T.Q.endCl x) (msgL m))
    (P₂ : (Q.let.X × Dr s) × Q.Ex.Str → Prop)
    (P₃ : TX ((Q.let.X × Dr s) × K) K T.J × Q.Ex.Str → Prop)
    {L : IOR (Q.let.X × Dr s) Q.Ex (TX ((Q.let.X × Dr s) × K) K T.J) Q.Ex} {η : Err L.shape}
    (hL : KnowAt L (ranCond (T.inD₁ left right k₂) P₂)
      (ranCond (outLM T left right k₂ msgL) P₃) Cb.Sub.idW η) :
    KnowAt L (ranCond (T.inD₁ left right k₂) P₂)
      (ranCond (outD T left right k₂ (tail3 T msg₃ endC i12 is e keep)) P₃) Cb.Sub.idW η :=
  knowAt_mono hL (fun _ h => h) (fun _ _ _ h => h)
    (fun b w _ hw => ⟨hw.1, hE b.1 w.1 hw.2⟩) (fun _ h => h)

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.knowAt_born
#print axioms OnBytes.Tie.Pv.Tail.look_knowOn
#print axioms OnBytes.Tie.Pv.Tail.look_forBOn
#print axioms OnBytes.Tie.Pv.Tail.outD_of_outLM
