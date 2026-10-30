-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutKit.lean: composed plans of splits and merges, with their conditions and further data.

A plan of splits and merges (`XPlan`, Iop/Recut.lean) goes through a protocol's list of rounds
(`Shape`): the first round stays; or a first part is split off and the plan goes on with the
remainder; or it is merged with the next round and the plan goes on with the merged round. This file
builds plans from smaller ones and shows that the conditions on plans carry over (words of this
library: lean/GLOSSARY.md). In a protocol with slots (`BatchInteractiveOracleProof`, Iop/Batch.lean) a round is
shared or local (its kind: one challenge for all slots, or one for each), and its annotation
(`RAnn`) divides the prover message into a shared component and the slot's component. There a plan
comes with an annotation of its splits (`AXPlan`, Iop/BatchRecut.lean).
  `XPlan.app P Q`: for plans P of s and Q of t, the plan of s ++ t. It merges nothing across the
      border between s and t. To merge the last round r of s with the first round r' of t, write
      the list as .. :: r :: r' :: .. (a list that is given by a definition unfolds to this form):
      the merges `XPlan.msg` and `XPlan.chal` (Iop/Recut.lean) are plans of a list r1 :: r2 :: ..
  `XPlan.repLast r n X0 X1`: n copies of r before a list t: all copies but the last are unchanged,
      and the plan X1 of r :: t deals with the last copy and t; X0 is the plan of t for n = 0.
  `RPlan.thenX p X`: a chain of splits of one round, and then the plan X with the last part as its
      first round, so that the last part can be merged with the next round.
  `RCut.unJoin r1 r2`, `ACut.unJoin k a1 a2`: a split of a round merged by (J1) of Iop/Join.lean
      (two prover messages become one), between its two messages. (`ACut.ofSlot` and `ofShared` do
      not apply to a merged round: the components of
      `(RAnn.ofSlot k r1).joinMsg (RAnn.ofSlot k r2)` are pairs.) `ACut.ofSlot`, `ACut.ofShared`
      (Iop/SplitKit.lean): the annotation of a split of a round that is sent whole by the slots, or
      whole in the shared component.
  `XPlan.NoMsg`, `XPlan.NoCut`: all merges are by (J2) (two challenges become one); no split (then
      no annotation is needed: `AXPlan.noCut`).
For these plans the file proves, not each for every plan, from the same conditions on their parts
and in some cases under further hypotheses:
  `XPlan.OK`, `AXPlan.OK`;
  `AXPlan.Kinds`: two rounds merged by (J2) have the same kind;
  `AXPlan.Fit`: the plan fits the format `RoundSplits.Fmt` of Iop/BatchFmt.lean;
  `AXPlan.Late`: the condition at the round `BatchProtocol.late`.
For these plans, again not each for every plan, it also counts splits and merges, bounds
`XPlan.maxRun` (the largest number of old rounds whose errors are in a new round), and gives the
further data (`RKit`, `AKit`, Iop/SplitData.lean).

Limits: nothing on the protocols of an instantiation.
-/
import Iop.RecutData
import Iop.SplitUnderJoin

namespace Iop

/-! ## 1. Plans -/

def XPlan.app : {s t : Shape} → XPlan s → XPlan t → XPlan (s ++ t)
  | _, _, .nil, Q => Q
  | _, _, .keep r P, Q => .keep r (XPlan.app P Q)
  | _, _, .cut c P, Q => .cut c (XPlan.app P Q)
  | _, _, .msg r1 r2 u P, Q => .msg r1 r2 u (XPlan.app P Q)
  | _, _, .chal r1 r2 np P, Q => .chal r1 r2 np (XPlan.app P Q)

def XPlan.repLast (r : Round) :
    (n : ℕ) → {t : Shape} → XPlan t → XPlan (r :: t) → XPlan (List.replicate n r ++ t)
  | 0, _, X0, _ => X0
  | 1, _, _, X1 => X1
  | n + 2, _, X0, X1 => .keep r (XPlan.repLast r (n + 1) X0 X1)

/-- The last part of a chain of splits. -/
def RPlan.last : {r : Round} → RPlan r → Round
  | r, .keep _ => r
  | _, .cut _ rest => rest.last

/-- A chain of splits, and then a plan with the last part as its first round. -/
def RPlan.thenX : {r : Round} → (p : RPlan r) → {s : Shape} → XPlan (p.last :: s) → XPlan (r :: s)
  | _, .keep _, _, X => X
  | _, .cut c rest, _, X => .cut c (rest.thenX X)

/-- The last part is unchanged. -/
def RPlan.ontoX {r : Round} (p : RPlan r) {s : Shape} (X : XPlan s) : XPlan (r :: s) :=
  p.thenX (.keep p.last X)


/-- All merges of the plan are by (J2). -/
def XPlan.NoMsg : {s : Shape} → XPlan s → Prop
  | _, .nil => True
  | _, .keep _ P => P.NoMsg
  | _, .cut _ P => P.NoMsg
  | _, .msg _ _ _ _ => False
  | _, .chal _ _ _ P => P.NoMsg

/-! ### The conditions -/

theorem XPlan.keepAll_ok : ∀ s : Shape, (XPlan.keepAll s).OK
  | [] => trivial
  | _ :: s => XPlan.keepAll_ok s

theorem XPlan.app_ok {s t : Shape} {P : XPlan s} {Q : XPlan t} (hP : P.OK) (hQ : Q.OK) :
    (XPlan.app P Q).OK := by
  induction P with
  | nil => exact hQ
  | keep r P ih => exact ih hP
  | cut c P ih => exact ⟨hP.1, ih hP.2⟩
  | msg r1 r2 u P ih => exact ⟨hP.1, ih hP.2⟩
  | chal r1 r2 np P ih => exact ⟨hP.1, ih hP.2⟩

theorem XPlan.repLast_ok (r : Round) :
    ∀ (n : ℕ) {t : Shape} {X0 : XPlan t} {X1 : XPlan (r :: t)},
      X0.OK → X1.OK → (XPlan.repLast r n X0 X1).OK
  | 0, _, _, _, h0, _ => h0
  | 1, _, _, _, _, h1 => h1
  | n + 2, _, _, _, h0, h1 => XPlan.repLast_ok r (n + 1) h0 h1

theorem RPlan.thenX_ok {r : Round} {p : RPlan r} (hp : p.OK) {s : Shape}
    {X : XPlan (p.last :: s)} (hX : X.OK) : (p.thenX X).OK := by
  induction p with
  | keep r => exact hX
  | cut c rest ih => exact ⟨hp.1, ih hp.2 hX⟩

theorem RPlan.ontoX_ok {r : Round} {p : RPlan r} (hp : p.OK) {s : Shape} {X : XPlan s} (hX : X.OK) :
    (p.ontoX X).OK :=
  RPlan.thenX_ok hp hX



/-! ### Counts -/

theorem XPlan.cuts_keepAll : ∀ s : Shape, (XPlan.keepAll s).cuts = 0
  | [] => rfl
  | _ :: s => XPlan.cuts_keepAll s

theorem XPlan.joins_keepAll : ∀ s : Shape, (XPlan.keepAll s).joins = 0
  | [] => rfl
  | _ :: s => XPlan.joins_keepAll s

theorem XPlan.cuts_app {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    (XPlan.app P Q).cuts = P.cuts + Q.cuts := by
  induction P with
  | nil => exact (Nat.zero_add _).symm
  | keep r P ih => exact ih
  | cut c P ih =>
      show (XPlan.app P Q).cuts + 1 = P.cuts + 1 + Q.cuts
      omega
  | msg r1 r2 u P ih => exact ih
  | chal r1 r2 np P ih => exact ih

theorem XPlan.joins_app {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    (XPlan.app P Q).joins = P.joins + Q.joins := by
  induction P with
  | nil => exact (Nat.zero_add _).symm
  | keep r P ih => exact ih
  | cut c P ih => exact ih
  | msg r1 r2 u P ih =>
      show (XPlan.app P Q).joins + 1 = P.joins + 1 + Q.joins
      omega
  | chal r1 r2 np P ih =>
      show (XPlan.app P Q).joins + 1 = P.joins + 1 + Q.joins
      omega

theorem RPlan.cuts_thenX {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s)) :
    (p.thenX X).cuts = p.cuts + X.cuts := by
  induction p with
  | keep r => exact (Nat.zero_add _).symm
  | cut c rest ih =>
      exact (congrArg (· + 1) (ih X)).trans (Nat.add_right_comm _ _ _)

theorem RPlan.joins_thenX {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s)) :
    (p.thenX X).joins = X.joins := by
  induction p with
  | keep r => rfl
  | cut c rest ih => exact ih X

theorem XPlan.cuts_repLast_succ (r : Round) :
    ∀ (n : ℕ) {t : Shape} (X0 : XPlan t) (X1 : XPlan (r :: t)),
      (XPlan.repLast r (n + 1) X0 X1).cuts = X1.cuts
  | 0, _, _, _ => rfl
  | n + 1, _, X0, X1 => XPlan.cuts_repLast_succ r n X0 X1

theorem XPlan.joins_repLast_succ (r : Round) :
    ∀ (n : ℕ) {t : Shape} (X0 : XPlan t) (X1 : XPlan (r :: t)),
      (XPlan.repLast r (n + 1) X0 X1).joins = X1.joins
  | 0, _, _, _ => rfl
  | n + 1, _, X0, X1 => XPlan.joins_repLast_succ r n X0 X1

/-! ### `NoMsg` and `maxRun` -/

theorem XPlan.keepAll_noMsg : ∀ s : Shape, (XPlan.keepAll s).NoMsg
  | [] => trivial
  | _ :: s => XPlan.keepAll_noMsg s

theorem XPlan.app_noMsg {s t : Shape} {P : XPlan s} {Q : XPlan t} (hP : P.NoMsg) (hQ : Q.NoMsg) :
    (XPlan.app P Q).NoMsg := by
  induction P with
  | nil => exact hQ
  | keep r P ih => exact ih hP
  | cut c P ih => exact ih hP
  | msg r1 r2 u P ih => exact hP.elim
  | chal r1 r2 np P ih => exact ih hP

theorem XPlan.repLast_noMsg (r : Round) :
    ∀ (n : ℕ) {t : Shape} {X0 : XPlan t} {X1 : XPlan (r :: t)},
      X0.NoMsg → X1.NoMsg → (XPlan.repLast r n X0 X1).NoMsg
  | 0, _, _, _, h0, _ => h0
  | 1, _, _, _, _, h1 => h1
  | n + 2, _, _, _, h0, h1 => XPlan.repLast_noMsg r (n + 1) h0 h1

theorem RPlan.thenX_noMsg {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} (hX : X.NoMsg) : (p.thenX X).NoMsg := by
  induction p with
  | keep r => exact hX
  | cut c rest ih => exact ih hX


theorem XPlan.maxRunFrom_keepAll : ∀ (s : Shape) (w : ℕ), (XPlan.keepAll s).maxRunFrom w ≤ max w 1
  | [], _ => Nat.zero_le _
  | _ :: s, w =>
    max_le (le_max_left _ _)
      ((XPlan.maxRunFrom_keepAll s 1).trans (by rw [max_self]; exact le_max_right _ _))

theorem XPlan.maxRun_keepAll (s : Shape) : (XPlan.keepAll s).maxRun ≤ 1 :=
  (XPlan.maxRunFrom_keepAll s 1).trans (by rw [max_self])

theorem XPlan.maxRunFrom_app {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    ∀ w, (XPlan.app P Q).maxRunFrom w ≤ max (P.maxRunFrom w) (Q.maxRunFrom (s.restW w)) := by
  induction P with
  | nil => exact fun w => le_max_right _ _
  | @keep r s P ih =>
      intro w
      refine max_le ((le_max_left _ _).trans (le_max_left _ _))
        ((ih 1).trans (max_le ((le_max_right _ _).trans (le_max_left _ _)) ?_))
      have e : s.restW 1 = 1 := by cases s <;> rfl
      rw [e]
      exact le_max_right _ _
  | cut c P ih => exact fun w => ih w
  | msg r1 r2 u P ih => exact fun w => ih (w + 1)
  | chal r1 r2 np P ih => exact fun w => ih (w + 1)

theorem XPlan.maxRun_app {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    (XPlan.app P Q).maxRun ≤ max P.maxRun Q.maxRun := by
  refine (XPlan.maxRunFrom_app P Q 1).trans (le_of_eq ?_)
  have e : s.restW 1 = 1 := by cases s <;> rfl
  rw [e]
  rfl

theorem XPlan.maxRun_repLast (r : Round) :
    ∀ (n : ℕ) {t : Shape} (X0 : XPlan t) (X1 : XPlan (r :: t)),
      (XPlan.repLast r n X0 X1).maxRun ≤ max 1 (max X0.maxRun X1.maxRun)
  | 0, _, _, _ => (le_max_left _ _).trans (le_max_right _ _)
  | 1, _, _, _ => (le_max_right _ _).trans (le_max_right _ _)
  | n + 2, _, X0, X1 => max_le (le_max_left _ _) (XPlan.maxRun_repLast r (n + 1) X0 X1)

theorem RPlan.maxRunFrom_thenX
    {r : Round} (p : RPlan r) {s : Shape} (X : XPlan (p.last :: s)) (w : ℕ) :
    (p.thenX X).maxRunFrom w = X.maxRunFrom w := by
  induction p with
  | keep r => rfl
  | cut c rest ih => exact ih X

/-! ### Where an old round begins -/

theorem XPlan.idx_keepAll : ∀ (s : Shape) (n : ℕ), (XPlan.keepAll s).idx n = n
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: s, n + 1 => congrArg (· + 1) (XPlan.idx_keepAll s n)

theorem XPlan.idx_app_lt {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    ∀ n, n < s.length → (XPlan.app P Q).idx n = P.idx n := by
  induction P with
  | nil => intro n h; exact absurd h (Nat.not_lt_zero n)
  | keep r P ih =>
      rintro (_ | n) h
      · rfl
      · exact congrArg (· + 1) (ih n (Nat.lt_of_succ_lt_succ h))
  | cut c P ih =>
      rintro (_ | n) h
      · rfl
      · exact congrArg (· + 1) (ih (n + 1) h)
  | @msg r1 r2 s u P ih =>
      intro n h
      have h' : n < s.length + 1 + 1 := h
      exact ih (n - 1) (by show n - 1 < s.length + 1; omega)
  | @chal r1 r2 s np P ih =>
      intro n h
      have h' : n < s.length + 1 + 1 := h
      exact ih (n - 1) (by show n - 1 < s.length + 1; omega)

theorem XPlan.idx_app_ge {s t : Shape} (P : XPlan s) (Q : XPlan t) :
    ∀ m, (XPlan.app P Q).idx (s.length + m) = P.shape.length + Q.idx m := by
  induction P with
  | nil => intro m; show Q.idx (0 + m) = 0 + Q.idx m; rw [Nat.zero_add, Nat.zero_add]
  | @keep r s P ih =>
      intro m
      show (XPlan.keep r (XPlan.app P Q)).idx (s.length + 1 + m) = P.shape.length + 1 + Q.idx m
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      show (XPlan.app P Q).idx (s.length + m) + 1 = _
      rw [ih m]
      omega
  | @cut r s c P ih =>
      intro m
      show (XPlan.cut c (XPlan.app P Q)).idx (s.length + 1 + m) = P.shape.length + 1 + Q.idx m
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      show (XPlan.app P Q).idx (s.length + m + 1) + 1 = _
      have := ih m
      rw [show s.length + m + 1 = (c.snd :: s).length + m by show _ = s.length + 1 + m; omega, this]
      omega
  | @msg r1 r2 s u P ih =>
      intro m
      show (XPlan.app P Q).idx (s.length + 1 + 1 + m - 1) = P.shape.length + Q.idx m
      rw [show s.length + 1 + 1 + m - 1 =
          (r1.joinMsg r2 :: s).length + m by show _ = s.length + 1 + m; omega]
      exact ih m
  | @chal r1 r2 s np P ih =>
      intro m
      show (XPlan.app P Q).idx (s.length + 1 + 1 + m - 1) = P.shape.length + Q.idx m
      rw [show s.length + 1 + 1 + m - 1 =
          (r1.joinChal r2 :: s).length + m by show _ = s.length + 1 + m; omega]
      exact ih m

/-! ### A split of a merged round -/

/-- The split of a round merged by (J1), between its two messages. -/
def RCut.unJoin (r1 r2 : Round) : RCut (r1.joinMsg r2) where
  OrcA := r1.Orc
  OrcB := r2.Orc
  PosA := r1.Pos
  PosB := r2.Pos
  PlainA := r1.Plain
  PlainB := r2.Plain
  orc := Equiv.refl _
  pos := Equiv.refl _
  plain := Equiv.refl _
  rdA := r1.rd
  rdB := r2.rd

theorem RCut.unJoin_ok (r1 r2 : Round) : (RCut.unJoin r1 r2).OK := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 2. Annotated plans -/

/-- The annotation of `RCut.unJoin`: the components of the parts are those of the two old rounds; k
is the kind of the round of the first part. -/
def ACut.unJoin (k : Kind) {r1 r2 : Round} (a1 : RAnn r1) (a2 : RAnn r2) :
    ACut (RCut.unJoin r1 r2) (a1.joinMsg a2) where
  kind := k
  A := ⟨a1.M0, a1.Mj, a1.split, a1.P0, a1.Pj, a1.pl0, a1.plj, a1.plain, a1.own⟩
  B := ⟨a2.M0, a2.Mj, a2.split, a2.P0, a2.Pj, a2.pl0, a2.plj, a2.plain, a2.own⟩
  m0 := Equiv.refl _
  mj := Equiv.refl _

/-- `ACut.unJoin` satisfies `ACut.OK`, if the plain parts of the two old annotations are those of
their components (a clause of `RAnn.Coherent`). -/
theorem ACut.unJoin_ok (k : Kind) {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2}
    (h1 : ∀ m0 mj, a1.plain (a1.join m0 mj).2 = (a1.pl0 m0, a1.plj mj))
    (h2 : ∀ m0 mj, a2.plain (a2.join m0 mj).2 = (a2.pl0 m0, a2.plj mj)) :
    (ACut.unJoin k a1 a2).OK :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, h1, h2⟩


def AXPlan.app :
    {s t : Shape} → (P : XPlan s) → (Q : XPlan t) → (A : RoundSplits s) → (B : RoundSplits t) →
    AXPlan P A → AXPlan Q B → AXPlan (XPlan.app P Q) (RoundSplits.app A B)
  | _, _, .nil, _ => fun _ _ _ W => W
  | _, _, .keep r P, Q => fun (A : RAnn r × RoundSplits _) B Z W => AXPlan.app P Q A.2 B Z W
  | _, _, .cut (r := r) (s := s) c P, Q =>
      fun (A : RAnn r × RoundSplits s) B
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) W =>
      ⟨Z.1, AXPlan.app P Q (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) B Z.2 W⟩
  | _, _, .msg r1 r2 (s := s) _ P, Q =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) B Z W =>
      AXPlan.app P Q (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) B Z W
  | _, _, .chal r1 r2 (s := s) _ P, Q =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) B Z W =>
      AXPlan.app P Q (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) B Z W

/-- Splits of a round that is sent whole by the slots: all first parts have the kind k1. -/
def AXPlan.thenSlot (k1 k : Kind) :
    {r : Round} → (p : RPlan r) → {s : Shape} → {X : XPlan (p.last :: s)} → {A : RoundSplits s} →
    AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot k p.last, A)) →
    AXPlan (p.thenX X) (show RoundSplits (r :: s) from (RAnn.ofSlot k r, A))
  | _, .keep _ => fun Z => Z
  | _, .cut c rest => fun Z => ⟨ACut.ofSlot k1 k c, AXPlan.thenSlot k1 k rest Z⟩

/-- Splits of a round that is sent whole in the shared component. -/
def AXPlan.thenShared (k1 k : Kind) :
    {r : Round} → (p : RPlan r) → {s : Shape} → {X : XPlan (p.last :: s)} → {A : RoundSplits s} →
    AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofShared k p.last, A)) →
    AXPlan (p.thenX X) (show RoundSplits (r :: s) from (RAnn.ofShared k r, A))
  | _, .keep _ => fun Z => Z
  | _, .cut c rest => fun Z => ⟨ACut.ofShared k1 k c, AXPlan.thenShared k1 k rest Z⟩

/-- All first parts are rounds of the kind k. -/
def AXPlan.CutKinds (k : Kind) : {s : Shape} → (P : XPlan s) → (A : RoundSplits s) → AXPlan P A → Prop
  | _, .nil => fun _ _ => True
  | _, .keep r P => fun (A : RAnn r × RoundSplits _) Z => AXPlan.CutKinds k P A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      Z.1.kind = k ∧ AXPlan.CutKinds k P (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.CutKinds k P (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.CutKinds k P (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-- The plan has no split. -/
def XPlan.NoCut : {s : Shape} → XPlan s → Prop
  | _, .nil => True
  | _, .keep _ P => P.NoCut
  | _, .cut _ _ => False
  | _, .msg _ _ _ P => P.NoCut
  | _, .chal _ _ _ P => P.NoCut

/-- Nothing is split, so there is nothing to annotate. -/
def AXPlan.noCut : {s : Shape} → (P : XPlan s) → P.NoCut → (A : RoundSplits s) → AXPlan P A
  | _, .nil => fun _ _ => PUnit.unit
  | _, .keep r P => fun h (A : RAnn r × RoundSplits _) => AXPlan.noCut P h A.2
  | _, .cut _ _ => fun h _ => h.elim
  | _, .msg r1 r2 (s := s) _ P =>
    fun h (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan.noCut P h (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
  | _, .chal r1 r2 (s := s) _ P =>
    fun h (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan.noCut P h (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))

theorem XPlan.keepAll_noCut : ∀ s : Shape, (XPlan.keepAll s).NoCut
  | [] => trivial
  | _ :: s => XPlan.keepAll_noCut s

theorem XPlan.app_noCut {s t : Shape} {P : XPlan s} {Q : XPlan t} (hP : P.NoCut) (hQ : Q.NoCut) :
    (XPlan.app P Q).NoCut := by
  induction P with
  | nil => exact hQ
  | keep r P ih => exact ih hP
  | cut c P ih => exact hP.elim
  | msg r1 r2 u P ih => exact ih hP
  | chal r1 r2 np P ih => exact ih hP

theorem XPlan.repLast_noCut (r : Round) :
    ∀ (n : ℕ) {t : Shape} {X0 : XPlan t} {X1 : XPlan (r :: t)},
      X0.NoCut → X1.NoCut → (XPlan.repLast r n X0 X1).NoCut
  | 0, _, _, _, h0, _ => h0
  | 1, _, _, _, _, h1 => h1
  | n + 2, _, _, _, h0, h1 => XPlan.repLast_noCut r (n + 1) h0 h1

theorem XPlan.cuts_of_noCut {s : Shape} (P : XPlan s) (h : P.NoCut) : P.cuts = 0 := by
  induction P with
  | nil => rfl
  | keep r P ih => exact ih h
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact ih h
  | chal r1 r2 np P ih => exact ih h

theorem AXPlan.noCut_ok {s : Shape} (P : XPlan s) (h : P.NoCut) :
    ∀ A : RoundSplits s, AXPlan.OK P A (AXPlan.noCut P h A) := by
  induction P with
  | nil => intro _; trivial
  | keep r P ih => exact fun A => ih h A.2
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact fun A => ih h (A.1.joinMsg A.2.1, A.2.2)
  | chal r1 r2 np P ih => exact fun A => ih h (A.1.joinChal r2, A.2.2)

theorem AXPlan.noCut_cutKinds (k : Kind) {s : Shape} (P : XPlan s) (h : P.NoCut) :
    ∀ A : RoundSplits s, AXPlan.CutKinds k P A (AXPlan.noCut P h A) := by
  induction P with
  | nil => intro _; trivial
  | keep r P ih => exact fun A => ih h A.2
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact fun A => ih h (A.1.joinMsg A.2.1, A.2.2)
  | chal r1 r2 np P ih => exact fun A => ih h (A.1.joinChal r2, A.2.2)

/-! ### The conditions on annotated splits -/

theorem AXPlan.keepAll_ok :
    ∀ (s : Shape) (A : RoundSplits s), AXPlan.OK (XPlan.keepAll s) A (AXPlan.keepAll s A)
  | [], _ => trivial
  | _ :: s, A => AXPlan.keepAll_ok s A.2

theorem AXPlan.app_ok {s t : Shape} (P : XPlan s) (Q : XPlan t) (B : RoundSplits t)
    (W : AXPlan Q B) (hW : AXPlan.OK Q B W) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A),
      AXPlan.OK P A Z → AXPlan.OK (XPlan.app P Q) (RoundSplits.app A B) (AXPlan.app P Q A B Z W) := by
  induction P with
  | nil => intro _ _ _; exact hW
  | keep r P ih => exact fun A Z h => ih A.2 Z h
  | cut c P ih => exact fun A Z h => ⟨h.1, ih (Z.1.ann2, A.2) Z.2 h.2⟩
  | msg r1 r2 u P ih => exact fun A Z h => ih (A.1.joinMsg A.2.1, A.2.2) Z h
  | chal r1 r2 np P ih => exact fun A Z h => ih (A.1.joinChal r2, A.2.2) Z h

theorem AXPlan.thenSlot_ok (k1 k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot k p.last, A))} (hZ : AXPlan.OK X _ Z) :
    AXPlan.OK (p.thenX X) _ (AXPlan.thenSlot k1 k p Z) := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ⟨ACut.ofSlot_ok k1 k c, ih hZ⟩

theorem AXPlan.thenShared_ok (k1 k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofShared k p.last, A))}
    (hZ : AXPlan.OK X _ Z) :
    AXPlan.OK (p.thenX X) _ (AXPlan.thenShared k1 k p Z) := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ⟨ACut.ofShared_ok k1 k c, ih hZ⟩

/-! ### Kinds -/

theorem AXPlan.kinds_of_allKind (k : Kind) {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), RoundSplits.AllKind k A → AXPlan.Kinds P A Z := by
  induction P with
  | nil => intro _ _ _; trivial
  | keep r P ih => exact fun A Z h => ih A.2 Z h.2
  | cut c P ih => exact fun A Z h => ih (Z.1.ann2, A.2) Z.2 ⟨h.1, h.2⟩
  | msg r1 r2 u P ih => exact fun A Z h => ih (A.1.joinMsg A.2.1, A.2.2) Z ⟨h.2.1, h.2.2⟩
  | chal r1 r2 np P ih => exact fun A Z h => ⟨h.2.1.trans h.1.symm, ih (A.1.joinChal r2, A.2.2) Z ⟨h.1, h.2.2⟩⟩

theorem AXPlan.kinds_keepAll :
    ∀ (s : Shape) (A : RoundSplits s), AXPlan.Kinds (XPlan.keepAll s) A (AXPlan.keepAll s A)
  | [], _ => trivial
  | _ :: s, A => AXPlan.kinds_keepAll s A.2

theorem AXPlan.kinds_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (B : RoundSplits t)
    (W : AXPlan Q B) (hW : AXPlan.Kinds Q B W) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.Kinds P A Z →
      AXPlan.Kinds (XPlan.app P Q) (RoundSplits.app A B) (AXPlan.app P Q A B Z W) := by
  induction P with
  | nil => intro _ _ _; exact hW
  | keep r P ih => exact fun A Z h => ih A.2 Z h
  | cut c P ih => exact fun A Z h => ih (Z.1.ann2, A.2) Z.2 h
  | msg r1 r2 u P ih => exact fun A Z h => ih (A.1.joinMsg A.2.1, A.2.2) Z h
  | chal r1 r2 np P ih => exact fun A Z h => ⟨h.1, ih (A.1.joinChal r2, A.2.2) Z h.2⟩

theorem AXPlan.kinds_thenSlot (k1 k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot k p.last, A))}
    (hZ : AXPlan.Kinds X _ Z) :
    AXPlan.Kinds (p.thenX X) _ (AXPlan.thenSlot k1 k p Z) := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ih hZ

theorem AXPlan.kinds_thenShared (k1 k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofShared k p.last, A))}
    (hZ : AXPlan.Kinds X _ Z) :
    AXPlan.Kinds (p.thenX X) _ (AXPlan.thenShared k1 k p Z) := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ih hZ

/-! ### The format (Iop/BatchFmt.lean) -/

theorem AXPlan.fit_keepAll :
    ∀ (s : Shape) (A : RoundSplits s) (ph : FPhase), AXPlan.Fit (XPlan.keepAll s) A (AXPlan.keepAll s A) ph
  | [], _, _ => trivial
  | _ :: s, A, _ => AXPlan.fit_keepAll s A.2 _

/-- Local rounds may be split into local parts and merged freely: the plan fits the format from
every phase. -/
theorem AXPlan.fit_allLo {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (ph : FPhase),
      RoundSplits.AllKind .lo A → AXPlan.CutKinds .lo P A Z → AXPlan.Fit P A Z ph := by
  induction P with
  | nil => intro _ _ _ _ _; trivial
  | keep r P ih => exact fun A Z ph h hc => ih A.2 Z _ h.2 hc
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ph h hc
      refine ⟨?_, ih (b.ann2, A) Z _ ⟨h.1, h.2⟩ hc.2⟩
      show FPhase.fit b.kind a.kind ph _ _
      rw [hc.1, h.1]
      cases ph <;> trivial
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z ph h hc
      refine ⟨?_, ih (a1.joinMsg a2, A) Z ph ⟨h.2.1, h.2.2⟩ hc⟩
      show FPhase.fitMsg a1.kind a2.kind ph
      rw [h.1, h.2.1]
      cases ph <;> trivial
  | chal r1 r2 np P ih => exact fun A Z ph h hc => ih (A.1.joinChal r2, A.2.2) Z ph ⟨h.1, h.2.2⟩ hc

/-- Shared rounds after the joining round (Iop/BatchFmt.lean) may be split into shared parts and
merged freely: the plan fits the format from `.shr`. -/
theorem AXPlan.fit_allSh {s : Shape} (P : XPlan s) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A),
      RoundSplits.AllKind .sh A → AXPlan.CutKinds .sh P A Z → AXPlan.Fit P A Z .shr := by
  induction P with
  | nil => intro _ _ _ _; trivial
  | keep r P ih =>
      rintro ⟨a, A⟩ Z h hc
      show AXPlan.Fit P A Z (FPhase.after a.kind .shr)
      rw [h.1]
      exact ih A Z h.2 hc
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ h hc
      refine ⟨?_, ?_⟩
      · show FPhase.fit b.kind a.kind .shr _ _
        rw [hc.1, h.1]
        trivial
      · show AXPlan.Fit P (b.ann2, A) Z (FPhase.after b.kind .shr)
        rw [hc.1]
        exact ih (b.ann2, A) Z ⟨h.1, h.2⟩ hc.2
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z h hc
      refine ⟨?_, ih (a1.joinMsg a2, A) Z ⟨h.2.1, h.2.2⟩ hc⟩
      show FPhase.fitMsg a1.kind a2.kind .shr
      rw [h.1, h.2.1]
      trivial
  | chal r1 r2 np P ih => exact fun A Z h hc => ih (A.1.joinChal r2, A.2.2) Z ⟨h.1, h.2.2⟩ hc

theorem AXPlan.fit_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (B : RoundSplits t) (W : AXPlan Q B) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (ph : FPhase), AXPlan.Kinds P A Z → AXPlan.Fit P A Z ph →
      AXPlan.Fit Q B W (RoundSplits.endPhase A ph) →
      AXPlan.Fit (XPlan.app P Q) (RoundSplits.app A B) (AXPlan.app P Q A B Z W) ph := by
  induction P with
  | nil => intro _ _ _ _ _ h; exact h
  | keep r P ih => exact fun A Z ph hK hP hQ => ih A.2 Z _ hK hP hQ
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ ph hK hP hQ
      refine ⟨hP.1, ih (b.ann2, A) Z _ hK hP.2 ?_⟩
      show AXPlan.Fit Q B W (RoundSplits.endPhase A (FPhase.after a.kind (FPhase.after b.kind ph)))
      rw [FPhase.after_after_of_fit hP.1]
      exact hQ
  | msg r1 r2 u P ih =>
      rintro ⟨a1, a2, A⟩ Z ph hK hP hQ
      refine ⟨hP.1, ih (a1.joinMsg a2, A) Z ph hK hP.2 ?_⟩
      show AXPlan.Fit Q B W (RoundSplits.endPhase A (FPhase.after a2.kind ph))
      rw [← FPhase.after_after_of_fitMsg hP.1]
      exact hQ
  | chal r1 r2 np P ih =>
      rintro ⟨a1, a2, A⟩ Z ph hK hP hQ
      refine ih (a1.joinChal r2, A) Z ph hK.2 hP ?_
      have hQ' : AXPlan.Fit Q B W
          (RoundSplits.endPhase A (FPhase.after a2.kind (FPhase.after a1.kind ph))) := hQ
      rw [hK.1] at hQ'
      show AXPlan.Fit Q B W (RoundSplits.endPhase A (FPhase.after a1.kind ph))
      have e : FPhase.after a1.kind (FPhase.after a1.kind ph) = FPhase.after a1.kind ph := by
        cases a1.kind <;> cases ph <;> rfl
      rwa [e] at hQ'

/-- If X fits the format from `.shr`, so does the plan that first splits a shared round that is sent
whole in the shared component into shared parts. -/
theorem AXPlan.fit_thenShared_sh {r : Round} (p : RPlan r) {s : Shape} {X : XPlan (p.last :: s)}
    {A : RoundSplits s} {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofShared .sh p.last, A))}
    (hZ : AXPlan.Fit X _ Z .shr) :
    AXPlan.Fit (p.thenX X) _ (AXPlan.thenShared .sh .sh p Z) .shr := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ⟨trivial, ih hZ⟩

/-- If X fits the format from ph and `ph.afterLo`, the plan that first splits a local round that is
sent whole by the slots into local parts fits it from ph. -/
theorem AXPlan.fit_thenSlot_lo {r : Round} (p : RPlan r) {s : Shape} {X : XPlan (p.last :: s)}
    {A : RoundSplits s} {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot .lo p.last, A))} :
    ∀ ph : FPhase, (∀ ph' : FPhase, ph' = ph ∨ ph' = ph.afterLo → AXPlan.Fit X _ Z ph') →
      AXPlan.Fit (p.thenX X) _ (AXPlan.thenSlot .lo .lo p Z) ph := by
  induction p with
  | keep r => exact fun ph h => h ph (Or.inl rfl)
  | cut c rest ih =>
      intro ph h
      refine ⟨by cases ph <;> trivial, ih (FPhase.after .lo ph) fun ph' h' => h ph' (Or.inr ?_)⟩
      rcases h' with rfl | rfl
      · rfl
      · cases ph <;> rfl

/-! ### The round `BatchProtocol.late` -/

theorem AXPlan.late_keepAll :
    ∀ (s : Shape) (A : RoundSplits s) (n : ℕ), AXPlan.Late (XPlan.keepAll s) A (AXPlan.keepAll s A) n
  | [], _, _ => trivial
  | _ :: _, _, 0 => trivial
  | _ :: s, A, n + 1 => AXPlan.late_keepAll s A.2 n

theorem AXPlan.late_app_lt {s t : Shape} (P : XPlan s) (Q : XPlan t) (B : RoundSplits t) (W : AXPlan Q B) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A) (n : ℕ), n < s.length → AXPlan.Late P A Z n →
      AXPlan.Late (XPlan.app P Q) (RoundSplits.app A B) (AXPlan.app P Q A B Z W) n := by
  induction P with
  | nil => intro _ _ n h; exact absurd h (Nat.not_lt_zero n)
  | keep r P ih =>
      rintro ⟨a, A⟩ Z (_ | n) h hl
      · trivial
      · exact ih A Z n (Nat.lt_of_succ_lt_succ h) hl
  | cut c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ (_ | n) h hl
      · exact hl
      · exact ⟨hl.1, ih (b.ann2, A) Z (n + 1) h hl.2⟩
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) h hl
      · exact ⟨hl.1, ih (a1.joinMsg a2, A) Z 0 (Nat.succ_pos _) hl.2⟩
      · exact hl.elim
      · exact ih (a1.joinMsg a2, A) Z (n + 1) (Nat.lt_of_succ_lt_succ h) hl
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z (_ | _ | n) h hl
      · exact ih (a1.joinChal r2, A) Z 0 (Nat.succ_pos _) hl
      · exact hl.elim
      · exact ih (a1.joinChal r2, A) Z (n + 1) (Nat.lt_of_succ_lt_succ h) hl

/-- The round `late` is in the second list: every first part that is split off in the first list
must be local. (not all hypotheses are named here: see the statement below) -/
theorem AXPlan.late_app_ge {s t : Shape} (P : XPlan s) (Q : XPlan t) (B : RoundSplits t) (W : AXPlan Q B)
    (m : ℕ) (hQ : AXPlan.Late Q B W m) :
    ∀ (A : RoundSplits s) (Z : AXPlan P A), AXPlan.CutKinds .lo P A Z →
      AXPlan.Late (XPlan.app P Q) (RoundSplits.app A B) (AXPlan.app P Q A B Z W) (s.length + m) := by
  induction P with
  | nil =>
      intro _ _ _
      show AXPlan.Late Q B W (0 + m)
      rw [Nat.zero_add]
      exact hQ
  | @keep r s P ih =>
      rintro ⟨a, A⟩ Z hc
      show AXPlan.Late (.keep r (XPlan.app P Q)) (show RoundSplits (r :: (s ++ t)) from (a, RoundSplits.app A B))
        (AXPlan.app P Q A B Z W) (s.length + 1 + m)
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      exact ih A Z hc
  | @cut r s c P ih =>
      rintro ⟨a, A⟩ ⟨b, Z⟩ hc
      show AXPlan.Late (.cut c (XPlan.app P Q)) (show RoundSplits (r :: (s ++ t)) from (a, RoundSplits.app A B))
        ⟨b, AXPlan.app P Q (b.ann2, A) B Z W⟩ (s.length + 1 + m)
      rw [show s.length + 1 + m = (s.length + m) + 1 by omega]
      have := ih (b.ann2, A) Z hc.2
      rw [show (c.snd :: s).length + m =
          (s.length + m) + 1 by show s.length + 1 + m = _; omega] at this
      exact ⟨hc.1, this⟩
  | @msg r1 r2 s u P ih =>
      rintro ⟨a1, a2, A⟩ Z hc
      show AXPlan.Late (.msg r1 r2 u (XPlan.app P Q))
        (show RoundSplits (r1 :: r2 :: (s ++ t)) from (a1, a2, RoundSplits.app A B))
        (AXPlan.app P Q (a1.joinMsg a2, A) B Z W) (s.length + 1 + 1 + m)
      rw [show s.length + 1 + 1 + m = (s.length + m) + 2 by omega]
      have := ih (a1.joinMsg a2, A) Z hc
      rw [show (r1.joinMsg r2 :: s).length + m =
          (s.length + m) + 1 by show s.length + 1 + m = _; omega] at this
      exact this
  | @chal r1 r2 s np P ih =>
      rintro ⟨a1, a2, A⟩ Z hc
      show AXPlan.Late (.chal r1 r2 np (XPlan.app P Q))
        (show RoundSplits (r1 :: r2 :: (s ++ t)) from (a1, a2, RoundSplits.app A B))
        (AXPlan.app P Q (a1.joinChal r2, A) B Z W) (s.length + 1 + 1 + m)
      rw [show s.length + 1 + 1 + m = (s.length + m) + 2 by omega]
      have := ih (a1.joinChal r2, A) Z hc
      rw [show (r1.joinChal r2 :: s).length + m =
          (s.length + m) + 1 by show s.length + 1 + m = _; omega] at this
      exact this

/-- `AXPlan.Late` (Iop/BatchRecut.lean) at n = 0: the round `late` is r itself. It is sent whole by
the slots and is split by p, with local first parts. If p has a split, `Late` asks that the first
part is local, and nothing of what follows it; otherwise it asks what it asks of the plan X. The
statement takes `hZ` in both cases. -/
theorem AXPlan.late_thenSlot_zero (k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot k p.last, A))}
    (hZ : AXPlan.Late X _ Z 0) :
    AXPlan.Late (p.thenX X) _ (AXPlan.thenSlot .lo k p Z) 0 := by
  cases p with
  | keep r => exact hZ
  | cut c rest => rfl

/-- The round `late` comes after a round that is sent whole by the slots and is split with local
first parts. -/
theorem AXPlan.late_thenSlot_succ (k : Kind) {r : Round} (p : RPlan r) {s : Shape}
    {X : XPlan (p.last :: s)} {A : RoundSplits s}
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofSlot k p.last, A))}
    {n : ℕ} (hZ : AXPlan.Late X _ Z (n + 1)) :
    AXPlan.Late (p.thenX X) _ (AXPlan.thenSlot .lo k p Z) (n + 1) := by
  induction p with
  | keep r => exact hZ
  | cut c rest ih => exact ⟨rfl, ih hZ⟩

/-! ## 3. Further data -/



def XPlan.Kits.app :
    {s t : Shape} → (P : XPlan s) → (Q : XPlan t) → P.Kits → Q.Kits → (XPlan.app P Q).Kits
  | _, _, .nil, _ => fun _ y => y
  | _, _, .keep _ P, Q => fun x y => XPlan.Kits.app P Q x y
  | _, _, .cut c P, Q => fun (x : RKit c.fst × RKit c.snd × P.Kits) y => (x.1, x.2.1, XPlan.Kits.app P Q x.2.2 y)
  | _, _, .msg _ _ _ P, Q => fun x y => XPlan.Kits.app P Q x y
  | _, _, .chal _ _ _ P, Q => fun x y => XPlan.Kits.app P Q x y

def RPlan.Kits.thenX :
    {r : Round} → (p : RPlan r) → p.Kits → {s : Shape} → {X : XPlan (p.last :: s)} →
    X.Kits → (p.thenX X).Kits
  | _, .keep _ => fun _ _ _ y => y
  | _, .cut c rest =>
    fun (x : RKit c.fst × RKit c.snd × rest.Kits) _ _ y =>
      (x.1, x.2.1, RPlan.Kits.thenX rest x.2.2 y)

/-- A plan without a split has no further data. -/
def XPlan.Kits.noCut : {s : Shape} → (P : XPlan s) → P.NoCut → P.Kits
  | _, .nil => fun _ => ()
  | _, .keep _ P => fun h => XPlan.Kits.noCut P h
  | _, .cut _ _ => fun h => h.elim
  | _, .msg _ _ _ P => fun h => XPlan.Kits.noCut P h
  | _, .chal _ _ _ P => fun h => XPlan.Kits.noCut P h

def AXPlan.Kits.noCut :
    {s : Shape} → (P : XPlan s) → (h : P.NoCut) → (A : RoundSplits s) →
    AXPlan.Kits P (XPlan.Kits.noCut P h) A (AXPlan.noCut P h A)
  | _, .nil => fun _ _ => ()
  | _, .keep r P => fun h (A : RAnn r × RoundSplits _) => AXPlan.Kits.noCut P h A.2
  | _, .cut _ _ => fun h _ => h.elim
  | _, .msg r1 r2 (s := s) _ P =>
    fun h (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan.Kits.noCut P h (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2))
  | _, .chal r1 r2 (s := s) _ P =>
    fun h (A : RAnn r1 × RAnn r2 × RoundSplits s) =>
      AXPlan.Kits.noCut P h (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2))

def AXPlan.Kits.app :
    {s t : Shape} → (P : XPlan s) → (Q : XPlan t) → (K : P.Kits) → (K' : Q.Kits) →
    (A : RoundSplits s) → (B : RoundSplits t) → (Z : AXPlan P A) → (W : AXPlan Q B) →
    AXPlan.Kits P K A Z → AXPlan.Kits Q K' B W →
    AXPlan.Kits (XPlan.app P Q) (XPlan.Kits.app P Q K K') (RoundSplits.app A B) (AXPlan.app P Q A B Z W)
  | _, _, .nil, _ => fun _ _ _ _ _ _ _ y => y
  | _, _, .keep r P, Q =>
    fun K K' (A : RAnn r × RoundSplits _) B Z W x y => AXPlan.Kits.app P Q K K' A.2 B Z W x y
  | _, _, .cut (r := r) (s := s) c P, Q =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) K' (A : RAnn r × RoundSplits s) B
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) W
          (x : AKit Z.1.ann1 K.1.pt × AKit Z.1.ann2 K.2.1.pt ×
            AXPlan.Kits P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2) y =>
      (x.1, x.2.1,
        AXPlan.Kits.app P Q K.2.2 K' (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) B Z.2 W x.2.2 y)
  | _, _, .msg r1 r2 (s := s) _ P, Q => fun K K' (A : RAnn r1 × RAnn r2 × RoundSplits s) B Z W x y =>
      AXPlan.Kits.app P Q K K'
        (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) B Z W x y
  | _, _, .chal r1 r2 (s := s) _ P, Q => fun K K' (A : RAnn r1 × RAnn r2 × RoundSplits s) B Z W x y =>
      AXPlan.Kits.app P Q K K'
        (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) B Z W x y

def AXPlan.Kits.thenShared (k1 k : Kind) :
    {r : Round} → (p : RPlan r) → (x : p.Kits) → {s : Shape} → {X : XPlan (p.last :: s)} →
    {K : X.Kits} → {A : RoundSplits s} →
    {Z : AXPlan X (show RoundSplits (p.last :: s) from (RAnn.ofShared k p.last, A))} →
    AXPlan.Kits X K _ Z →
    AXPlan.Kits (p.thenX X) (RPlan.Kits.thenX p x K)
      (show RoundSplits (r :: s) from (RAnn.ofShared k r, A)) (AXPlan.thenShared k1 k p Z)
  | _, .keep _ => fun _ _ _ _ _ _ y => y
  | _, .cut c rest =>
    fun (x : RKit c.fst × RKit c.snd × rest.Kits) _ _ _ _ _ y =>
      (AKit.ofShared k1 x.1, AKit.ofShared k x.2.1, AXPlan.Kits.thenShared k1 k rest x.2.2 y)

end Iop
