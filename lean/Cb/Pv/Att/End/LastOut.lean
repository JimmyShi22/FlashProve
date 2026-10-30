-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/LastOut.lean: the ledgers of the last four sumchecks of an attention sub-proof, pulled
back, give the blocks' output claims; and the claims on the pairs' scalars give their rule values.

Definitions, statements and proofs. As Cb/Pv/Att/End/FirstOut.lean, for the value product on the
diagonal tiles (step s12), the score at the index (step s16), the key at the index (step 18) and the
bits of the index (Cb/Pv/Att/BitsSc3.lean, with any number kap of variables that number a bit), with
the reading forms of Cb/Pv/Att/End/Last.lean at the challenges and the point of the output statement
o. Three of the four have a form of their own. Of the score at the index only the first end values
are tied to a table. The key at the index is a sumcheck by degrees, with one end value a layer and
one a pair and bit. Of the bits the claim on a pair's second end value reads no table: it says that
the second hidden value is the first minus 1.

Main names:
  slotF T o a: the hidden value under an end value, as a form. It is the first part of endF
    (endF_slot). slotF_val, slot_holds.
  firsts nb: the first end values of a sumcheck of products. ends18 s: the end values of the
  sumcheck by degrees.
  bitsR: the reading forms of the bits' ledger: rA21 for a first end value; the first hidden value
    minus 1 for a second.
  Tabs12, Tabs16, Tabs18, TabsH, TabsM: what the weights of a step's tables are. Good12, Good16,
    Good18, GoodH, GoodM: the names that a step's forms read are names of late entries.
  out12, outBits: all output claims of the block. score16: the claim on the row and those on the
  first end values. out18: all output claims, for step 18 read at other public states (PlainSc.pull
  in Cb/Pv/Att/OwnSteps.lean is of that form). m6: the hidden value of a pair's scalar is rvM6.
  out12_iff, score16_iff, out18_iff, outBits_iff, m6_iff: the same as equivalences: a ledger's
    pull-back says no more than these claims.

Limits: those of Cb/Pv/Att/End/Tabs.lean and Cb/Pv/Att/End/Step.lean. That the ledgers are the
programs' is not said here.


-/
import Cb.Pv.Att.End.Last
import Cb.Pv.Att.End.FirstOut
import Cb.Pv.Att.End.Lin
import Cb.Pv.Att.Step18Ends
import Cb.Pv.Att.End.Dec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] [Fintype E]

/-! ### The hidden value under an end value -/

section Plain
variable (T : PlainSc E) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] [DecidableEq T.J]

/-- The hidden value under an end value, as a form: what was shown less the last coordinate times
the mask entry. -/
noncomputable def slotF (o : T.our.par.Out) (a : T.A) : Aff E (T.J ⊕ J₂) :=
  aSub (aConst (o.vals a))
    (aSmul (T.our.lst o.st (T.our.par.hp o.st o.pt)) (aEnt (.inl (T.cAt a))))

omit [Fintype J₂] in
/-- The claim on an end value is: the hidden value less the form is 0. -/
theorem endF_slot (o : T.our.par.Out) (a : T.A) (r : Aff E (T.J ⊕ J₂)) :
    endF T o a r = (aSub (slotF T o a) r).claim := rfl

theorem slotF_val (al : J₂ → Aff E T.J) (o : T.our.par.Out) (a : T.A) (m : T.J → E) :
    (slotF (J₂ := J₂) T o a).val (late al m) =
      o.vals a - T.our.lst o.st (T.our.par.hp o.st o.pt) * m (T.cAt a) := by
  unfold slotF
  rw [val_aSub, val_aConst, val_aSmul, val_aEnt]
  rfl

/-- The output claim on an end value says that the hidden value is the map at the point. -/
theorem slot_holds (al : J₂ → Aff E T.J) (o : T.our.par.Out) (a : T.A) (m : T.J → E) :
    T.our.par.EHolds o m a ↔
      (slotF (J₂ := J₂) T o a).val (late al m) = T.map o.st m a (pointAt T o) := by
  rw [slotF_val, psc_our_val E T.our o m a]
  show T.map o.st m a (pointAt T o) + m (T.cAt a) * T.our.lst o.st (T.our.par.hp o.st o.pt) =
      o.vals a ↔ _
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

end Plain

/-- The first end values of a sumcheck of products. -/
def firsts (nb : ℕ) : List (Fin nb × Bool) := (List.finRange nb).map fun b => (b, false)

theorem mem_firsts {nb : ℕ} (b : Fin nb) : (b, false) ∈ firsts nb :=
  List.mem_map_of_mem (List.mem_finRange b)

/-- The end values of the sumcheck by degrees: the layers', then those of the pairs and bits. -/
def ends18 (s : ScdSize) : List s.A :=
  (List.finRange s.Lam).map Sum.inl ++
    (List.finRange s.pairs).flatMap fun b => (List.finRange s.lt).map fun t => Sum.inr (b, t)

theorem mem_ends18 {s : ScdSize} (a : s.A) : a ∈ ends18 s := by
  rcases a with l | ⟨b, t⟩
  · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange l))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨b, List.mem_finRange b, List.mem_map_of_mem (List.mem_finRange t)⟩)

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁] [DecidableEq J₂]

variable (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂) (tb : AttTab → TabW E)

/-! ### What is asked of tables and names -/

structure Tabs12 (p : Pub E) (ξ : ℕ → E) : Prop where
  tVD : tb .tVD = .col (eqN lmS (D.lD - lmS) (ptOn D C p ξ))
  qVD : tb .qVD = .long (eqN ls (D.ln - ls) (yn D C p.z)) (eqT D (sh ξ D.lg))

structure Good12 : Prop where
  tVD : ∀ b < D.nb, ∀ jj < 5, ∀ hi < 2 ^ (D.lD - lmS),
    Y.good (.tVD, (Raw.c .D jj b 0).addX (hi * 2 ^ lmS))
  qVD : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.qVD, (Raw.val k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))

structure TabsM (p : Pub E) : Prop where
  hT : tb .hT = .row (eqT D p.ti)

structure GoodM : Prop where
  hT : ∀ b < D.nb, ∀ g < D.nG, ∀ k < 4, Y.good (.hT, .mx k b g 0)

structure Tabs16 (ξ : ℕ → E) : Prop where
  qF : tb .qF = .long (eqN ls (D.ln - ls) (sh ξ (D.lT + D.lg))) (eqT D ξ)

structure Good16 : Prop where
  qF : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.qF, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))

structure Tabs18 (p : Pub E) (ξ : ℕ → E) : Prop where
  qKx : tb .qKx = .long (eqN ls (D.ln - ls) p.fn) (eqT D ξ)
  hPi : tb .hPi = .row (eqT D (sh ξ (D.lT + D.lg)))

structure Good18 : Prop where
  qKx : ∀ lam < D.nl, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
    Y.good (.qKx, (Raw.key k lam g 0 0).addN (ch * 2 ^ ls))
  hPi : ∀ b < D.nb, ∀ k < D.lT, ∀ g < D.nG, Y.good (.hPi, .ib k b g 0)

structure TabsH (ξ : ℕ → E) : Prop where
  hR2 : tb .hR2 = .row (eqT D ξ)

structure GoodH : Prop where
  hR2 : ∀ b < D.nb, ∀ k < D.lT, ∀ g < D.nG, Y.good (.hR2, .ib k b g 0)

/-! ### The pairs' scalars -/

omit [Fintype E] in
/-- The claim on a pair's scalar, pulled back, says that the scalar's hidden value is the library's
rule value. s: what was sent; k: the place of its mask entry. -/
theorem m6_iff (cellJ : Raw → J₁) (p : Pub E) (hT : TabsM D tb p) (hG : GoodM D Y) (b : ℕ)
    (hb : b < D.nb) (s : E) (k : J₁) (m : J₁ → E) :
    (pullF (lateA cellJ D ls lmS Y tb) (linF s k (rM6 D Y p b))).Holds m ↔
      s - m k = rvM6 D p (rdOf cellJ m) b := by
  rw [linF_pull m _ s k _, rM6_val cellJ D ls lmS Y tb p m hT.hT b (hG.hT b hb)]

omit [Fintype E] in
/-- The hidden value of a pair's scalar is the library's rule value. -/
theorem m6 (cellJ : Raw → J₁) (p : Pub E) (hT : TabsM D tb p) (hG : GoodM D Y) (b : ℕ)
    (hb : b < D.nb) (s : E) (k : J₁) (m : J₁ → E)
    (h : (pullF (lateA cellJ D ls lmS Y tb) (linF s k (rM6 D Y p b))).Holds m) :
    s - m k = rvM6 D p (rdOf cellJ m) b :=
  (m6_iff D ls lmS Y tb cellJ p hT hG b hb s k m).mp h

/-! ### The sumchecks -/

variable (cellJ : Raw → J₁) (rd : (J₁ → E) → Raw → E) (hrd : ∀ m, rd m = rdOf cellJ m)
  (inc : Pub E → J₁ → E)
include hrd

/-- The value product on the diagonal tiles: the ledger's pull-back says what the block's output
claims say. -/
theorem out12_iff (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (Step.s12.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s12 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hl : lmS ≤ D.lD) (hT : Tabs12 D C ls lmS tb o.st (ptN _ o)) (hG : Good12 D ls lmS Y)
    (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s12 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA12 D C lmS Y o.st (ptN _ o)) (rB12 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (stepSc3 D C rd .s12 inc wAt cAt).plain.our.par.OutHolds o m :=
  stepCl_iff (stepSc3 D C rd .s12 inc wAt cAt) _ o _ _ m
    (fun b => by
      show _ = Aext D C o.st (rd m) .s12 b.val (ptN _ o)
      rw [hrd m]
      exact rA12_val cellJ D C ls lmS Y tb o.st _ m hl hT.tVD b.val (hG.tVD b.val b.isLt))
    (fun b => by
      show _ = Bext D C o.st (rd m) .s12 b.val (ptN _ o)
      rw [hrd m]
      exact rB12_val cellJ D C ls lmS Y tb o.st _ m hls hT.qVD b.val (hG.qVD b.val b.isLt))

/-- The value product on the diagonal tiles. -/
theorem out12 (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (Step.s12.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s12 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hl : lmS ≤ D.lD) (hT : Tabs12 D C ls lmS tb o.st (ptN _ o)) (hG : Good12 D ls lmS Y)
    (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s12 inc wAt cAt).plain o (pairs D.nb)
        (pick (rA12 D C lmS Y o.st (ptN _ o)) (rB12 D C ls Y o.st (ptN _ o))),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s12 inc wAt cAt).plain.our.par.OutHolds o m :=
  (out12_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hl hT hG m).mp h

/-- The score at the index: the ledger's pull-back says what the claim on the row and those on the
first end values say. -/
theorem score16_iff (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (Step.s16.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs16 D ls tb (ptN _ o)) (hG : Good16 D ls Y) (m : J₁ → E) :
    (∀ f ∈ plainCl (stepSc3 D C rd .s16 inc wAt cAt).plain o (firsts D.nb)
        (fun a => rA16 D ls Y (ptN _ o) a.1.val),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      ((stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.UHolds o m ∧
        ∀ b, (stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.EHolds o m (b, false)) := by
  have hr : ∀ a ∈ firsts D.nb, (rA16 (J₁ := J₁) D ls Y (ptN _ o) a.1.val).val
      (late (lateA cellJ D ls lmS Y tb) m) =
      (stepSc3 D C rd .s16 inc wAt cAt).plain.map o.st m a
        (pointAt (stepSc3 D C rd .s16 inc wAt cAt).plain o) := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    show _ = Aext D C o.st (rd m) .s16 b.val (ptN _ o)
    rw [hrd m]
    exact rA16_val cellJ D C ls lmS Y tb o.st _ m hls hT.qF b.val (hG.qF b.val b.isLt)
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := plainCl_out (stepSc3 D C rd .s16 inc wAt cAt).plain _ o (firsts D.nb) _ m
      hr h
    exact ⟨h1, fun b => h2 _ (mem_firsts b)⟩
  · intro h
    refine plainCl_in (stepSc3 D C rd .s16 inc wAt cAt).plain _ o (firsts D.nb) _ m hr
      ⟨h.1, fun a ha => ?_⟩
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    exact h.2 b

/-- The score at the index: the claim on the row and those on the first end values. -/
theorem score16 (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (Step.s16.g D) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs16 D ls tb (ptN _ o)) (hG : Good16 D ls Y) (m : J₁ → E)
    (h : ∀ f ∈ plainCl (stepSc3 D C rd .s16 inc wAt cAt).plain o (firsts D.nb)
        (fun a => rA16 D ls Y (ptN _ o) a.1.val),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.UHolds o m ∧
      ∀ b, (stepSc3 D C rd .s16 inc wAt cAt).plain.our.par.EHolds o m (b, false) :=
  (score16_iff D C ls lmS Y tb cellJ rd hrd inc cAt wAt o hls hT hG m).mp h

/-- The reading forms of the ledger of the key at the index. -/
def keyR (p : Pub E) (ξ : ℕ → E) : (size18 D).A → Aff E (J₁ ⊕ J₂)
  | .inl l => rKC D ls Y p ξ l.val
  | .inr x => rIBP D Y ξ x.1.val x.2.val

omit hrd in
/-- The forms of the key at the index are worth the maps of step 18. -/
theorem keyR_val (hrd : ∀ m, rd m = rdOf cellJ m)
    (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J₁)
    (cAt : (size18 D).A → J₁) (p : Pub E) (z : Fin (size18 D).k → E) (hls : ls ≤ D.ln)
    (hT : Tabs18 D ls tb p (Blocks.nat z)) (hG : Good18 D ls Y) (m : J₁ → E)
    (a : (size18 D).A) :
    (keyR D ls Y p (Blocks.nat z) a).val (late (lateA cellJ D ls lmS Y tb) m) =
      (step18 D rd inc wAt cAt).map p m a z := by
  rcases a with l | ⟨b, t⟩
  · show (rKC D ls Y p (Blocks.nat z) l.val).val _ = _
    rw [step18_KC, hrd m]
    exact rKC_val cellJ D ls lmS Y tb p _ m hls hT.qKx l.val (hG.qKx l.val l.isLt)
  · show (rIBP D Y (Blocks.nat z) b.val t.val).val _ = _
    rw [step18_IB, hrd m]
    exact rIBP_val cellJ D ls lmS Y tb _ m hT.hPi b.val t.val (hG.hPi b.val b.isLt t.val t.isLt)

/-- The key at the index, read at other public states St' through f, with an incoming form of its
own: the ledger's pull-back says what the block's output claims say. -/
theorem out18_iff {St' : Type} (f : St' → Pub E) (inc' : St' → J₁ → E)
    (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J₁)
    (cAt : (size18 D).A → J₁)
    (o : ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs18 D ls tb (f o.st) (ptN _ o)) (hG : Good18 D ls Y) (m : J₁ → E) :
    (∀ g ∈ plainCl ((step18 D rd inc wAt cAt).plain.pull f inc') o (ends18 (size18 D))
        (keyR D ls Y (f o.st) (ptN _ o)),
      (pullF (lateA cellJ D ls lmS Y tb) g).Holds m) ↔
      ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.OutHolds o m := by
  have hr : ∀ a ∈ ends18 (size18 D), (keyR (J₁ := J₁) D ls Y (f o.st) (ptN _ o) a).val
      (late (lateA cellJ D ls lmS Y tb) m) =
      ((step18 D rd inc wAt cAt).plain.pull f inc').map o.st m a
        (pointAt ((step18 D rd inc wAt cAt).plain.pull f inc') o) :=
    fun a _ => keyR_val D ls lmS Y tb cellJ rd inc hrd wAt cAt (f o.st) _ hls hT hG m a
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := plainCl_out ((step18 D rd inc wAt cAt).plain.pull f inc') _ o
      (ends18 (size18 D)) _ m hr h
    exact ⟨h1, fun a => h2 a (mem_ends18 a)⟩
  · intro h
    exact plainCl_in ((step18 D rd inc wAt cAt).plain.pull f inc') _ o (ends18 (size18 D)) _ m hr
      ⟨h.1, fun a _ => h.2 a⟩

/-- The key at the index. -/
theorem out18 {St' : Type} (f : St' → Pub E) (inc' : St' → J₁ → E)
    (wAt : PIdx (ldPartFmt E (size18 D).k (size18 D).deg ++ [pDummy E ((size18 D).lt + 1)]) → J₁)
    (cAt : (size18 D).A → J₁)
    (o : ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.Out) (hls : ls ≤ D.ln)
    (hT : Tabs18 D ls tb (f o.st) (ptN _ o)) (hG : Good18 D ls Y) (m : J₁ → E)
    (h : ∀ g ∈ plainCl ((step18 D rd inc wAt cAt).plain.pull f inc') o (ends18 (size18 D))
        (keyR D ls Y (f o.st) (ptN _ o)),
      (pullF (lateA cellJ D ls lmS Y tb) g).Holds m) :
    ((step18 D rd inc wAt cAt).plain.pull f inc').our.par.OutHolds o m :=
  (out18_iff D ls lmS Y tb cellJ rd hrd inc f inc' wAt cAt o hls hT hG m).mp h

/-- The reading forms of the bits' ledger: rA21 for a first end value; the first hidden value minus
1 for a second. -/
noncomputable def bitsR (kap : ℕ) (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (bitsSc3 kap D rd inc wAt cAt).plain.our.par.Out) (a : Fin D.nb × Bool) :
    Aff E (J₁ ⊕ J₂) :=
  if a.2 then aSub (slotF (bitsSc3 kap D rd inc wAt cAt).plain o (a.1, false)) (aConst 1)
  else rA21 D Y kap (ptN _ o) a.1.val

/-- The bits of the index: the ledger's pull-back says what the block's output claims say. -/
theorem outBits_iff (kap : ℕ) (hK : D.lT ≤ 2 ^ kap) (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (bitsSc3 kap D rd inc wAt cAt).plain.our.par.Out)
    (hT : TabsH D tb (ptN _ o)) (hG : GoodH D Y) (m : J₁ → E) :
    (∀ f ∈ plainCl (bitsSc3 kap D rd inc wAt cAt).plain o (pairs D.nb)
        (bitsR D Y rd inc kap cAt wAt o),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) ↔
      (bitsSc3 kap D rd inc wAt cAt).plain.our.par.OutHolds o m := by
  have hA : ∀ b : Fin D.nb, (bitsR (J₂ := J₂) D Y rd inc kap cAt wAt o (b, false)).val
      (late (lateA cellJ D ls lmS Y tb) m) =
      (bitsSc3 kap D rd inc wAt cAt).plain.map o.st m (b, false)
        (pointAt (bitsSc3 kap D rd inc wAt cAt).plain o) := by
    intro b
    show (rA21 (J₁ := J₁) D Y kap (ptN _ o) b.val).val _ =
      Blocks.ext (D.lT + D.lg + kap) (bitCube kap D (rd m) b.val) (ptN _ o)
    rw [hrd m]
    exact rA21_val cellJ D ls lmS Y tb _ m kap hK hT.hR2 b.val (hG.hR2 b.val b.isLt)
  have hB : ∀ b : Fin D.nb,
      (bitsSc3 kap D rd inc wAt cAt).plain.our.par.EHolds o m (b, false) →
      (bitsR (J₂ := J₂) D Y rd inc kap cAt wAt o (b, true)).val
        (late (lateA cellJ D ls lmS Y tb) m) =
      (bitsSc3 kap D rd inc wAt cAt).plain.map o.st m (b, true)
        (pointAt (bitsSc3 kap D rd inc wAt cAt).plain o) := by
    intro b eA
    show (aSub (slotF (bitsSc3 kap D rd inc wAt cAt).plain o (b, false)) (aConst 1)).val _ =
      Blocks.ext (D.lT + D.lg + kap) (fun X => bitCube kap D (rd m) b.val X - 1) (ptN _ o)
    have e := (slot_holds (J₂ := J₂) (bitsSc3 kap D rd inc wAt cAt).plain
      (lateA cellJ D ls lmS Y tb) o (b, false) m).mp eA
    rw [val_aSub, val_aConst, Blocks.ext_sub, Blocks.ext_const]
    exact congrArg (fun t => t - 1) e
  have mem : ∀ a : Fin D.nb × Bool,
      endF (bitsSc3 kap D rd inc wAt cAt).plain o a (bitsR D Y rd inc kap cAt wAt o a) ∈
        plainCl (bitsSc3 kap D rd inc wAt cAt).plain o (pairs D.nb)
          (bitsR D Y rd inc kap cAt wAt o) := fun a =>
    List.mem_cons_of_mem _ (List.mem_map_of_mem (mem_pairs a))
  constructor
  · intro h
    have eA : ∀ b : Fin D.nb,
        (bitsSc3 kap D rd inc wAt cAt).plain.our.par.EHolds o m (b, false) := fun b =>
      (endF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o (b, false) _ m (hA b)).mp
        (h _ (mem (b, false)))
    refine ⟨(rowF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o m).mp
      (h _ List.mem_cons_self), ?_⟩
    rintro ⟨b, x⟩
    cases x with
    | false => exact eA b
    | true =>
      exact (endF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o (b, true) _ m (hB b (eA b))).mp
        (h _ (mem (b, true)))
  · intro h f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (rowF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o m).mpr h.1
    · obtain ⟨⟨b, x⟩, -, rfl⟩ := List.mem_map.mp hf
      cases x with
      | false =>
        exact (endF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o (b, false) _ m (hA b)).mpr
          (h.2 (b, false))
      | true =>
        exact (endF_pull (bitsSc3 kap D rd inc wAt cAt).plain _ o (b, true) _ m
          (hB b (h.2 (b, false)))).mpr (h.2 (b, true))

/-- The bits of the index. -/
theorem outBits (kap : ℕ) (hK : D.lT ≤ 2 ^ kap) (cAt : Fin D.nb × Bool → J₁)
    (wAt : PIdx (ldPartFmt E (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy E 2]) → J₁)
    (o : (bitsSc3 kap D rd inc wAt cAt).plain.our.par.Out)
    (hT : TabsH D tb (ptN _ o)) (hG : GoodH D Y) (m : J₁ → E)
    (h : ∀ f ∈ plainCl (bitsSc3 kap D rd inc wAt cAt).plain o (pairs D.nb)
        (bitsR D Y rd inc kap cAt wAt o),
      (pullF (lateA cellJ D ls lmS Y tb) f).Holds m) :
    (bitsSc3 kap D rd inc wAt cAt).plain.our.par.OutHolds o m :=
  (outBits_iff D ls lmS Y tb cellJ rd hrd inc kap hK cAt wAt o hT hG m).mp h

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.m6_iff
#print axioms Cb.Pv.Att.End.out12_iff
#print axioms Cb.Pv.Att.End.score16_iff
#print axioms Cb.Pv.Att.End.out18_iff
#print axioms Cb.Pv.Att.End.outBits_iff
