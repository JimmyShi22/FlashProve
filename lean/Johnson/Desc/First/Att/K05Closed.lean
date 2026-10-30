-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Closed.lean: towards a closed caller of the proved chain's letters
(Cb/Pv/Att/OwnSteps.lean: OwnPar): parameters whose places of mask entries are the slots' own
numbers, so that
every premise of K05_law at the library's letters that is "a place" becomes a lemma.

Main names:
  `Nums`, `numsOf h`: a plain record of slot numbers; those that the record Heard holds.
    Att/K05Numbers.lean
    proves that they are a function of the plan and of the ledger's next slot in front of the
      hearing alone.
  `Lin P0 Mg`: over any type Mg of messages: two readings (maskOf: the ledger's mask entries;
    restOf: P0's
    message) and the three free linear claims, which read the whole message: a hidden value is what
      was sent
    less its mask entry, so a claim on it must see the mask.
  `closedOf P0 Λ ns N`: the entries are the ledger's slots 0 … ns beside P0's; every place of a mask
    entry is a
    slot's number by N.
  `msg_slot` and the place lemmas `closed_kE`, `closed_kM`, `closed_kD`, `closed_kV`, `closed_kF`,
    `closed_c`,
    `closed_cH`, `closed_c18`, `closed_w`, `closed_wH`, `closed_w18`.

Limits. P0's reading of the cells, its message, the lookup's point and Λ stay parameters. A number
above ns
is taken modulo ns + 1, so two places may then fall on one entry; the chain's knowledge soundness
asks no
distinct places, and where a hearing has returned every number used is below ns. That the
neighbouring
kinds' statements are made at these parameters is not shown in this file or in what it imports.
Sources: Cb/Pv/Att/OwnSteps.lean (OwnPar); Step18.lean (size18); OnBytes/Tie/Pv/Att (sc3Num,
scdNum).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SlotsAt
import Johnson.Desc.First.Att.K05Prem2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (sc3Num scdNum)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {M0 X : Type}

/-- Slot numbers. -/
structure Nums where
  /-- the first slot of each plane message -/
  planes : List ℕ
  /-- of each unit: where its seven scalars, its coefficients and its end values begin -/
  units : List (ℕ × ℕ × ℕ)
  five : ℕ
  bits : ℕ
  two : ℕ
  values : ℕ
  maxima : ℕ
  fE : ℕ
  eE : ℕ
  fM : ℕ
  eM : ℕ
  fVD : ℕ
  eVD : ℕ
  fF : ℕ
  eF : ℕ
  fD : ℕ
  eD : ℕ
  fH : ℕ
  eH : ℕ

/-- The numbers that Heard holds. -/
def numsOf (h : Heard) : Nums where
  planes := h.remainders.toList
  units := h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd)
  five := h.five
  bits := h.bits
  two := h.two
  values := h.values
  maxima := h.maxima
  fE := h.division.first
  eE := h.division.sEnd
  fM := h.below.first
  eM := h.below.sEnd
  fVD := h.on.first
  eVD := h.on.sEnd
  fF := h.atIndex.first
  eF := h.atIndex.sEnd
  fD := h.key.first
  eD := h.key.sEnd
  fH := h.cells.first
  eH := h.cells.sEnd

namespace Nums

def plane (N : Nums) (n : ℕ) : ℕ := N.planes.getD n 0
def seven (N : Nums) (n : ℕ) : ℕ := ((N.units[n]?).map (·.1)).getD 0
def uFirst (N : Nums) (n : ℕ) : ℕ := ((N.units[n]?).map (·.2.1)).getD 0
def uEnd (N : Nums) (n : ℕ) : ℕ := ((N.units[n]?).map (·.2.2)).getD 0

/-- Where a step's coefficients begin; where its end values begin. -/
def firstOf (N : Nums) : AttSeg.Step → ℕ
  | .s6b => N.uFirst 0
  | .s6d => N.uFirst 1
  | .s8 => N.fE
  | .s11 => N.fM
  | .s12 => N.fVD
  | .s16 => N.fF
  | .s21 => 0

def endOf (N : Nums) : AttSeg.Step → ℕ
  | .s6b => N.uEnd 0
  | .s6d => N.uEnd 1
  | .s8 => N.eE
  | .s11 => N.eM
  | .s12 => N.eVD
  | .s16 => N.eF
  | .s21 => 0

end Nums

/-- Slot j as an entry. -/
def slotJ (ns : ℕ) {J0 : Type} (j : ℕ) : Fin (ns + 1) ⊕ J0 := Sum.inl (Fin.ofNat (ns + 1) j)

/-- How a message of the frame is read, and the three free linear claims on further scalars. Mg: ANY
type of messages.
maskOf: the ledger's mask entries in a message · restOf: P0's message in it · the three claims read
the whole message (a hidden
value is what was sent less its mask entry: a claim on it must see the mask). -/
structure Lin (P0 : OwnPar K M0 X) (Mg : Type) where
  maskOf : Mg → ℕ → K
  restOf : Mg → M0
  LM : Seen K X → (Fin (3 * P0.npl + 7) → K) → Mg → Prop
  LD : Seen K X → (Fin 7 → K) → Mg → Prop
  LE : Seen K X → (Fin (5 + P0.D.lT + 2) → K) → Mg → Prop

/-- **The parameters whose places are the slots' numbers.** -/
noncomputable def closedOf (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) : OwnPar K Mg X where
  D := P0.D
  C := P0.C
  J := Fin (ns + 1) ⊕ P0.J
  msg := fun m => Sum.elim (fun i => Λ.maskOf m i.1) (P0.msg (Λ.restOf m))
  rd := fun e => P0.rd fun j => e (Sum.inr j)
  zOf := P0.zOf
  npl := P0.npl
  kap := P0.kap
  wAt := fun s i => slotJ ns (posP _ (N.firstOf s) i)
  cAt := fun s a => slotJ ns (N.endOf s + sc3Num a)
  w18 := fun i => slotJ ns (posP _ N.fD i)
  c18 := fun a => slotJ ns (N.eD + scdNum (size18 P0.D) a)
  wH := fun i => slotJ ns (posP _ N.fH i)
  cH := fun a => slotJ ns (N.eH + sc3Num a)
  kM := fun j => slotJ ns (if j.1 < 3 * P0.npl then N.plane (j.1 / 3) + j.1 % 3 else N.seven 0 + (j.1 - 3 * P0.npl))
  kD := fun j => slotJ ns (N.seven 1 + j.1)
  kE := fun j => slotJ ns (if j.1 < 5 then N.five + j.1 else if j.1 < 5 + P0.D.lT then N.bits + (j.1 - 5)
    else N.two + (j.1 - (5 + P0.D.lT)))
  kV := fun j => slotJ ns (N.values + j.1)
  kF := fun j => slotJ ns (N.maxima + j.1)
  LM := Λ.LM
  LD := Λ.LD
  LE := Λ.LE

variable (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums)

/-- The entry at slot j of a message is the mask at j. -/
theorem msg_slot (m : Mg) {j : ℕ} (hj : j ≤ ns) : (closedOf P0 Λ ns N).msg m (slotJ ns j) = Λ.maskOf m j := by
  show Λ.maskOf m (Fin.ofNat (ns + 1) j).1 = Λ.maskOf m j
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem closed_kE (m : Mg) (hj : N.five + 1 ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kE (closedOf P0 Λ ns N).iZO) = Λ.maskOf m (N.five + 1) :=
  msg_slot P0 Λ ns N m hj

theorem closed_kM (m : Mg) (hj : N.seven 0 + 6 ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kM (Fin.last _)) = Λ.maskOf m (N.seven 0 + 6) := by
  have e : (closedOf P0 Λ ns N).kM (Fin.last _) = slotJ ns (N.seven 0 + 6) := by
    show slotJ ns (if 3 * P0.npl + 6 < 3 * P0.npl then _ else N.seven 0 + (3 * P0.npl + 6 - 3 * P0.npl)) = _
    rw [if_neg (by omega), show 3 * P0.npl + 6 - 3 * P0.npl = 6 by omega]
  rw [e]
  exact msg_slot P0 Λ ns N m hj

theorem closed_kD (m : Mg) (hj : N.seven 1 + 6 ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kD (Fin.last _)) = Λ.maskOf m (N.seven 1 + 6) :=
  msg_slot P0 Λ ns N m hj

theorem closed_kV (m : Mg) (j : Fin 2) (hj : N.values + j.1 ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kV j) = Λ.maskOf m (N.values + j.1) :=
  msg_slot P0 Λ ns N m hj

theorem closed_kF (m : Mg) (j : Fin P0.D.nb) (hj : N.maxima + j.1 ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).kF j) = Λ.maskOf m (N.maxima + j.1) :=
  msg_slot P0 Λ ns N m hj

theorem closed_c (m : Mg) (s : AttSeg.Step) (a : Fin P0.D.nb × Bool) (hj : N.endOf s + sc3Num a ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).cAt s a) = Λ.maskOf m (N.endOf s + sc3Num a) :=
  msg_slot P0 Λ ns N m hj

theorem closed_cH (m : Mg) (a : Fin P0.D.nb × Bool) (hj : N.eH + sc3Num a ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).cH a) = Λ.maskOf m (N.eH + sc3Num a) :=
  msg_slot P0 Λ ns N m hj

theorem closed_c18 (m : Mg) (a : (size18 P0.D).A) (hj : N.eD + scdNum (size18 P0.D) a ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).c18 a) = Λ.maskOf m (N.eD + scdNum (size18 P0.D) a) :=
  msg_slot P0 Λ ns N m hj

theorem closed_w (m : Mg) (s : AttSeg.Step)
    (i : PIdx (ldPartFmt K (s.g P0.D) (fun _ => 3) ++ [pDummy K 2])) (hj : posP _ (N.firstOf s) i ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).wAt s i) = Λ.maskOf m (posP _ (N.firstOf s) i) :=
  msg_slot P0 Λ ns N m hj

theorem closed_wH (m : Mg)
    (i : PIdx (ldPartFmt K (P0.D.lT + P0.D.lg + P0.kap) (fun _ => 3) ++ [pDummy K 2])) (hj : posP _ N.fH i ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).wH i) = Λ.maskOf m (posP _ N.fH i) :=
  msg_slot P0 Λ ns N m hj

theorem closed_w18 (m : Mg)
    (i : PIdx (ldPartFmt K (size18 P0.D).k (size18 P0.D).deg ++ [pDummy K ((size18 P0.D).lt + 1)]))
    (hj : posP _ N.fD i ≤ ns) :
    (closedOf P0 Λ ns N).msg m ((closedOf P0 Λ ns N).w18 i) = Λ.maskOf m (posP _ N.fD i) :=
  msg_slot P0 Λ ns N m hj

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.msg_slot
#print axioms VerifiableInference.Desc.First.Att.P.closed_w
