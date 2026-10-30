-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbThree.lean: pairs with bits (E2E/ClimbPair.lean, E2E/ClimbPairBatch.lean) for a list of
rounds of the form
  front round | chain 1 | joining round | chain 2 | seam | chain 3
(Compile/Joined/Types.lean, `Chains.sh`), from pairs of the three chains; the three single rounds
stay as they are. With the annotation of such a list (`Chains.ann`: front and chain 1 local, joining
round and chain 2 shared, seam and chain 3 local).

Main names:
  `RPair.slot`, `RPair.shared`, `Pair.slot`, `Pair.shared`: a pair as one that fits the annotations
    "only the requests send" and "only the shared part is sent" of kind k; `toPair_slot`,
    `toPair_shared`: behind them is the pair.
  `BPair.consSlot`, `BPair.consShared`, `BPair.app` and what is behind them.
  `pair3`, `ann3`, `bpair3`, `toPair_bpair3`: the pair of the whole list, the annotation, the pair
    that fits it, and that the first is behind the last.
  `pair3_tr₁` ... `pair3_msg3`: the parts of a stripped transcript are the stripped parts.
  `pair3_pass`: the whole passes if and only if the three chains' parts pass.
  `bits3`, `pair3_bits`: the numbers of bits; 0 at the three single rounds.

Limits: definitions and equations.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbPairBatch
import Compile.Joined.Types

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob

/-! ## 1. The two plain annotations -/

/-- A round's pair, fitting "only the requests send", of kind k. -/
def RPair.slot (k : Iop.Kind) {r r' : Round} (u : RPair r r') :
    RBPair (RAnn.ofSlot k r) (RAnn.ofSlot k r') :=
  ⟨id, u.fill, id, u.strip, u.zero, u.old, u.pass, fun _ => rfl, u.strip_fill, u.old_zero,
    u.pass_zero, u.zero_old, rfl⟩

/-- A round's pair, fitting "only the shared part is sent", of kind k. -/
def RPair.shared (k : Iop.Kind) {r r' : Round} (u : RPair r r') :
    RBPair (RAnn.ofShared k r) (RAnn.ofShared k r') :=
  ⟨u.fill, id, u.strip, id, u.zero, u.old, u.pass, u.strip_fill, fun _ => rfl, u.old_zero,
    u.pass_zero, u.zero_old, rfl⟩

theorem RPair.toRPair_slot (k : Iop.Kind) {r r' : Round} (u : RPair r r') :
    (u.slot k).toRPair = u := rfl

theorem RPair.toRPair_shared (k : Iop.Kind) {r r' : Round} (u : RPair r r') :
    (u.shared k).toRPair = u := rfl

def Pair.slot (k : Iop.Kind) : {s t : Iop.Shape} → Pair s t →
    BPair (RoundSplits.const (RAnn.ofSlot k) s) (RoundSplits.const (RAnn.ofSlot k) t)
  | [], [], _ => ()
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (u, p) => (u.slot k, Pair.slot k p)

def Pair.shared (k : Iop.Kind) : {s t : Iop.Shape} → Pair s t →
    BPair (RoundSplits.const (RAnn.ofShared k) s) (RoundSplits.const (RAnn.ofShared k) t)
  | [], [], _ => ()
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (u, p) => (u.shared k, Pair.shared k p)

theorem toPair_slot (k : Iop.Kind) : ∀ {s t : Iop.Shape} (p : Pair s t), (p.slot k).toPair = p
  | [], [], () => rfl
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (u, p) => congrArg (fun v => (u, v)) (toPair_slot k p)

theorem toPair_shared (k : Iop.Kind) : ∀ {s t : Iop.Shape} (p : Pair s t), (p.shared k).toPair = p
  | [], [], () => rfl
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (u, p) => congrArg (fun v => (u, v)) (toPair_shared k p)

/-- One more local round in front, in which only the requests send, kept as it is. -/
def BPair.consSlot (r : Round) {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (q : BPair A A') :
    BPair (s := r :: s) (t := r :: t) (RAnn.ofSlot .lo r, A) (RAnn.ofSlot .lo r, A') :=
  ((RPair.refl r).slot .lo, q)

/-- One more shared round in front, in which only the shared part is sent, kept as it is. -/
def BPair.consShared (r : Round) {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (q : BPair A A') :
    BPair (s := r :: s) (t := r :: t) (RAnn.ofShared .sh r, A) (RAnn.ofShared .sh r, A') :=
  ((RPair.refl r).shared .sh, q)

theorem toPair_consSlot (r : Round) {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t}
    (q : BPair A A') : (BPair.consSlot r q).toPair = Pair.cons r q.toPair := rfl

theorem toPair_consShared (r : Round) {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t}
    (q : BPair A A') : (BPair.consShared r q).toPair = Pair.cons r q.toPair := rfl

/-- Two in a row. -/
def BPair.app : {s t s' t' : Iop.Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → {B : RoundSplits s'} →
    {B' : RoundSplits t'} → BPair A A' → BPair B B' → BPair (RoundSplits.app A B) (RoundSplits.app A' B')
  | [], [], _, _, _, _, _, _, _, q' => q'
  | [], _ :: _, _, _, _, _, _, _, q, _ => Empty.elim q
  | _ :: _, [], _, _, _, _, _, _, q, _ => Empty.elim q
  | _ :: _, _ :: _, _, _, (_, _), (_, _), _, _, (u, q), q' => (u, BPair.app q q')

theorem BPair.toPair_app : ∀ {s t s' t' : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} {B : RoundSplits s'}
    {B' : RoundSplits t'} (q : BPair A A') (q' : BPair B B'),
      (BPair.app q q').toPair = Pair.app q.toPair q'.toPair
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, _, q, _ => Empty.elim q
  | _ :: _, [], _, _, _, _, _, _, q, _ => Empty.elim q
  | _ :: _, _ :: _, _, _, (_, _), (_, _), _, _, (u, q), q' =>
    congrArg (fun v => (u.toRPair, v)) (BPair.toPair_app q q')

/-! ## 2. The numbers of bits -/

theorem Pair.cons_bits (r : Round) {s t : Iop.Shape} {p : Pair s t} {g : GBits s}
    (h : p.toEmb.Bits g) :
    Emb.Bits (s := r :: s) (t := r :: t) (Pair.cons r p).toEmb (0, g) :=
  ⟨by rw [pow_zero, mul_one], h⟩

theorem Pair.app_bits {s t s' t' : Iop.Shape} {p : Pair s t} {p' : Pair s' t'} {g : GBits s}
    {g' : GBits s'} (h : p.toEmb.Bits g) (h' : p'.toEmb.Bits g') :
    (Pair.app p p').toEmb.Bits (GBits.app g g') :=
  (congrArg (fun e => Emb.Bits e (GBits.app g g')) (Pair.toEmb_app p p')).mpr (Emb.Bits.app h h')

/-! ## 3. Three chains -/

section
variable (rF rJ r3 : Round) {s₁ t₁ s₂ t₂ s₃ t₃ : Iop.Shape}
  (p₁ : Pair s₁ t₁) (p₂ : Pair s₂ t₂) (p₃ : Pair s₃ t₃)

/-- From the joining round on. -/
def pairJ : Pair (rJ :: (s₂ ++ r3 :: s₃)) (rJ :: (t₂ ++ r3 :: t₃)) :=
  Pair.cons rJ (Pair.app p₂ (Pair.cons r3 p₃))

/-- The whole list. -/
def pair3 : Pair (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃))) (rF :: (t₁ ++ rJ :: (t₂ ++ r3 :: t₃))) :=
  Pair.cons rF (Pair.app p₁ (pairJ rJ r3 p₂ p₃))

variable (τ : Tr (rF :: (t₁ ++ rJ :: (t₂ ++ r3 :: t₃))))

theorem pair3_msgF : ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).1 = τ.1 := Pair.cons_strip_1 rF _ τ

theorem pair3_tr₁ : Tr.fst ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2 = p₁.strip (Tr.fst τ.2.2) := by
  unfold pair3
  rw [Pair.cons_strip_22, Pair.fst_strip]

theorem pair3_trJ : Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2 =
    (pairJ rJ r3 p₂ p₃).strip (Tr.snd (s := t₁) τ.2.2) := by
  unfold pair3
  rw [Pair.cons_strip_22, Pair.snd_strip]

theorem pair3_msgJ : (Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2).1 =
    (Tr.snd (s := t₁) τ.2.2).1 := by
  rw [pair3_trJ]
  exact Pair.cons_strip_1 rJ _ _

theorem pair3_tr₂ : Tr.fst (Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2).2.2 =
    p₂.strip (Tr.fst (Tr.snd (s := t₁) τ.2.2).2.2) := by
  rw [pair3_trJ]
  unfold pairJ
  rw [Pair.cons_strip_22, Pair.fst_strip]

theorem pair3_tr3' :
    Tr.snd (s := s₂) (Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2).2.2 =
      (Pair.cons r3 p₃).strip (Tr.snd (s := t₂) (Tr.snd (s := t₁) τ.2.2).2.2) := by
  rw [pair3_trJ]
  unfold pairJ
  rw [Pair.cons_strip_22, Pair.snd_strip]

theorem pair3_msg3 :
    (Tr.snd (s := s₂) (Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2).2.2).1 =
      (Tr.snd (s := t₂) (Tr.snd (s := t₁) τ.2.2).2.2).1 := by
  rw [pair3_tr3']
  exact Pair.cons_strip_1 r3 _ _

theorem pair3_tr₃ :
    (Tr.snd (s := s₂) (Tr.snd (s := s₁) ((pair3 rF rJ r3 p₁ p₂ p₃).strip τ).2.2).2.2).2.2 =
      p₃.strip (Tr.snd (s := t₂) (Tr.snd (s := t₁) τ.2.2).2.2).2.2 := by
  rw [pair3_tr3']
  exact Pair.cons_strip_22 r3 _ _

/-- The whole passes if and only if the three chains' parts pass. -/
theorem pair3_pass : (pair3 rF rJ r3 p₁ p₂ p₃).passTr τ =
    (p₁.passTr (Tr.fst τ.2.2) &&
      (p₂.passTr (Tr.fst (Tr.snd (s := t₁) τ.2.2).2.2) &&
        p₃.passTr (Tr.snd (s := t₂) (Tr.snd (s := t₁) τ.2.2).2.2).2.2)) := by
  unfold pair3 pairJ
  rw [Pair.cons_pass, Pair.app_pass, Pair.cons_pass, Pair.app_pass, Pair.cons_pass]

end

/-- The numbers of bits of the whole list: 0 at the three single rounds. -/
def bits3 (rF rJ r3 : Round) {s₁ s₂ s₃ : Iop.Shape} (g₁ : GBits s₁) (g₂ : GBits s₂)
    (g₃ : GBits s₃) : GBits (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃))) :=
  (0, GBits.app g₁ ((0, GBits.app g₂ ((0, g₃) : GBits (r3 :: s₃))) :
    GBits (rJ :: (s₂ ++ r3 :: s₃))))

theorem pair3_bits (rF rJ r3 : Round) {s₁ t₁ s₂ t₂ s₃ t₃ : Iop.Shape} {p₁ : Pair s₁ t₁}
    {p₂ : Pair s₂ t₂} {p₃ : Pair s₃ t₃} {g₁ : GBits s₁} {g₂ : GBits s₂} {g₃ : GBits s₃}
    (h₁ : p₁.toEmb.Bits g₁) (h₂ : p₂.toEmb.Bits g₂) (h₃ : p₃.toEmb.Bits g₃) :
    (pair3 rF rJ r3 p₁ p₂ p₃).toEmb.Bits (bits3 rF rJ r3 g₁ g₂ g₃) :=
  Pair.cons_bits rF (Pair.app_bits h₁ (Pair.cons_bits rJ (Pair.app_bits h₂
    (Pair.cons_bits r3 h₃))))

/-- The annotation of such a list (`Chains.ann` written out). -/
def ann3 (rF rJ r3 : Round) (s₁ s₂ s₃ : Iop.Shape) :
    RoundSplits (rF :: (s₁ ++ rJ :: (s₂ ++ r3 :: s₃))) :=
  (RAnn.ofSlot .lo rF, RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) s₁)
    ((RAnn.ofShared .sh rJ, RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s₂)
      ((RAnn.ofSlot .lo r3, RoundSplits.const (RAnn.ofSlot .lo) s₃) : RoundSplits (r3 :: s₃))) :
      RoundSplits (rJ :: (s₂ ++ r3 :: s₃))))

/-- The pair that fits the annotations. -/
def bpair3 (rF rJ r3 : Round) {s₁ t₁ s₂ t₂ s₃ t₃ : Iop.Shape} (p₁ : Pair s₁ t₁) (p₂ : Pair s₂ t₂)
    (p₃ : Pair s₃ t₃) : BPair (ann3 rF rJ r3 s₁ s₂ s₃) (ann3 rF rJ r3 t₁ t₂ t₃) :=
  BPair.consSlot rF (BPair.app (p₁.slot .lo)
    (BPair.consShared rJ (BPair.app (p₂.shared .sh) (BPair.consSlot r3 (p₃.slot .lo)))))

/-- Behind it is `pair3`. -/
theorem toPair_bpair3 (rF rJ r3 : Round) {s₁ t₁ s₂ t₂ s₃ t₃ : Iop.Shape} (p₁ : Pair s₁ t₁)
    (p₂ : Pair s₂ t₂) (p₃ : Pair s₃ t₃) :
    (bpair3 rF rJ r3 p₁ p₂ p₃).toPair = pair3 rF rJ r3 p₁ p₂ p₃ := by
  have h3 : (BPair.consSlot r3 (p₃.slot .lo)).toPair = Pair.cons r3 p₃ :=
    (toPair_consSlot r3 _).trans (congrArg (Pair.cons r3) (toPair_slot .lo p₃))
  have h2 : (BPair.app (p₂.shared .sh) (BPair.consSlot r3 (p₃.slot .lo))).toPair =
      Pair.app p₂ (Pair.cons r3 p₃) :=
    (BPair.toPair_app _ _).trans (congrArg₂ Pair.app (toPair_shared .sh p₂) h3)
  have hJ : (BPair.consShared rJ
      (BPair.app (p₂.shared .sh) (BPair.consSlot r3 (p₃.slot .lo)))).toPair =
      pairJ rJ r3 p₂ p₃ :=
    (toPair_consShared rJ _).trans (congrArg (Pair.cons rJ) h2)
  have h1 : (BPair.app (p₁.slot .lo) (BPair.consShared rJ
      (BPair.app (p₂.shared .sh) (BPair.consSlot r3 (p₃.slot .lo))))).toPair =
      Pair.app p₁ (pairJ rJ r3 p₂ p₃) :=
    (BPair.toPair_app _ _).trans (congrArg₂ Pair.app (toPair_slot .lo p₁) hJ)
  exact (toPair_consSlot rF _).trans (congrArg (Pair.cons rF) h1)

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.pair3_tr₃
#print axioms AtPublicFiles.Climb.pair3_pass
#print axioms AtPublicFiles.Climb.pair3_bits
#print axioms AtPublicFiles.Climb.toPair_bpair3
