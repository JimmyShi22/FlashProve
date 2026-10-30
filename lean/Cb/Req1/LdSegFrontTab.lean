-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontTab.lean: the front in the order of the table: what comes first (shift, lookup);
claims joined, then a sumcheck; then a sumcheck again for each map that is never sent; a last step.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Req1/LdSegFront.lean has the frame of a front (the first part of a segment's body) for any
blocks, and the two blocks of the table as lists of moves (`frIn`, `frPsc`). Here they are put in
the table's order, as one term (`B.prog`, for `B : LdFrontTab E Kc z`) whose types meet by
definition:
      pre ; frIn Z ; step ; frPsc (T 0) ; step ; frPsc (T 1) ; .. ; frPsc (T m) ; last step
Z: the first block's claims (the zerocheck: Z := Zc.toIn). T 0, .., T m: the m + 1 further
sumchecks, one for each map that is given by an inner sum or product (the inner index of a matrix
product; keys that are made so). No verifier message between two sumchecks.
`frIn Z` joins the claims of Z (values against targets) into one sum claim, by a linear combination
whose coefficients an evader (`Evader`, Cb/Gen/BatEvader.lean) gives from the verifier's seed, and
then runs the sumcheck `Z.T` on that claim. That the sum claim is this combination of the values is
the hypothesis `Z.Link`.

Main names:
  `LdFrontTab E Kc z`: the data: Z with what rides along (R0) and its reading of the entries (msg0);
    m, T, A0 i, msg i; g0, g i: the steps' maps of the explicit part; the entry stage a and "pre";
    the last step's map gz.
  `LdStepOK S A A' f`: what is asked of a step: four clauses at the base joints.
  `Spec.ldSegTab_hyp`: `B.prog.Hyp` from `B.OK`: `B.pre.Hyp`; `Link`, `Back`, the evader's law of Z;
    `VarsOK`, `DegX`, `DegY`, `ValInj` of each sumcheck; the four clauses of each step.
  `Spec.ldSegTab_zero`: for the zerocheck on a cube (Z := Zc.toIn): `Link`, `Back`, `VarsOK`,
    `ValInj` hold; the evader's law follows from that of the evader on the functions; "all claims"
    says: every function vanishes at every corner.
  `Spec.ldSegTab_kinds`: sub-protocols and steps only, beside pre's kinds.
  `Spec.ldSegTab_nums`: the number of rounds `B.prog.nAll` is pre's + 1 + (`B.Z.T.fmt.length` + 3) +
    the sum over i ≤ m of (`(B.T i).fmt.length` + 3); nothing more is withheld, in this sense:
    `B.prog.pBad` and `B.prog.pHid` are pre's. What pBad and pHid bound: `GoodB`, Ior/Masked.lean;
    `Nums`, Ior/Chain.lean.
  `Spec.ldSegTab_zk`: `B.prog.Zk base` from `B.OK`, `B.pre.Zk base`, and for each sumcheck: its link
    is a masked block, and its fact is fresh: after `B.pre` for `B.Z.T`, after `B.upTo i` for `B.T
    i` (i ≤ B.m).

Why: the stage z at which the front ends is a parameter: the front's oracle messages, further
oracles and further witness are z's (so that a caller's stage is met by definition).

Limits: at least one further sumcheck stands in this term. A segment may need none: a claim on a map
that is affine in the cells is closed by the step that sends the reads, a claim on a map that is
linear in sent entries is a row. That case is the frame of Cb/Req1/LdSegFront.lean with the one
block `frIn Z`.
What the head of Cb/Req1/LdSegFront.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFrontProofs
import Cb.Ld.LdZeroProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

/-- What is asked of a step that only maps the explicit part. -/
structure LdStepOK {E Kc : Type} [Field E] (S : Sig E) {St St' Wp : Type} {E₀ : ExtSpec}
    (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp)) (f : St → St') : Prop where
  fw   : ∀ st y w, A.rel st y w → A'.rel (f st) y w
  on   : ∀ st y, A.on (st, y) → A'.on (f st, y)
  core : ∀ w, A'.core w = A.core w
  bw   : ∀ st y w, A.on (st, y) → A'.relR (f st, y) w → A.relR (st, y) w

theorem LdStepOK.hyp {E Kc : Type} [Field E] [Fintype E] {S : Sig E} {St St' Wp : Type}
    {E₀ : ExtSpec} {A : Rels Kc St E₀ (S.Msg × Wp)} {A' : Rels Kc St' E₀ (S.Msg × Wp)}
    {f : St → St'} (h : LdStepOK S A A' f) : (ldStepF S A A' f).Hyp :=
  ldStepF_hyp S A A' f h.fw h.on h.core h.bw

/-- The front in the order of the table: the data. -/
structure LdFrontTab (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) : Type 1 where
  /-- the first block -/
  Z    : PscIn E
  R0   : Rels Kc Z.St0 z.E₀ (z.S.Msg × z.Wp)
  msg0 : z.S.Msg → Z.T.J → E
  /-- the further sumchecks: T 0, .., T m -/
  m    : ℕ
  T    : ℕ → PscOur E
  A0   : ∀ i, Rels Kc (T i).St z.E₀ (z.S.Msg × z.Wp)
  msg  : ∀ i, z.S.Msg → (T i).J → E
  /-- the steps -/
  g0   : Z.T.par.Out → E × (T 0).St
  g    : ∀ i, (T i).par.Out → E × (T (i + 1)).St
  /-- the entry stage, and what comes first -/
  a    : LdStage E Kc
  pre  : LdProg a (frInS Kc Z z.S z.E₀ z.Wp R0 msg0)
  /-- the last step -/
  gz   : (T m).par.Out → z.St

namespace LdFrontTab
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (B : LdFrontTab E Kc z)

/-- the stages of the sumcheck i -/
@[reducible] def s (i : ℕ) : LdStage E Kc :=
  frPscS Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i)
@[reducible] def t (i : ℕ) : LdStage E Kc :=
  frPscT Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i)
/-- the stage after the first block -/
@[reducible] def t0 : LdStage E Kc :=
  frPscT Kc B.Z.T z.S z.E₀ z.Wp (B.Z.ride B.R0) B.msg0

def step0 : LdMv B.t0 (B.s 0) := ldStepF z.S B.t0.A (B.s 0).A B.g0
def step (i : ℕ) : LdMv (B.t i) (B.s (i + 1)) :=
  ldStepF z.S (B.t i).A (B.s (i + 1)).A (B.g i)
def post : LdMv (B.t B.m) z := ldStepF z.S (B.t B.m).A z.A B.gz

/-- the sumchecks 0, .., k with the steps between them -/
def tw : (k : ℕ) → LdProg (B.s 0) (B.t k)
  | 0 => frPsc Kc (B.T 0) z.S z.E₀ z.Wp (B.A0 0) (B.msg 0)
  | k + 1 =>
    ((tw k).snoc (B.step k)).app
      (frPsc Kc (B.T (k + 1)) z.S z.E₀ z.Wp (B.A0 (k + 1)) (B.msg (k + 1)))

/-- what comes before the further sumchecks -/
def head : LdProg B.a (B.s 0) :=
  (B.pre.app (frIn Kc B.Z z.S z.E₀ z.Wp B.R0 B.msg0)).snoc B.step0

/-- The front. -/
def prog : LdProg B.a z := (B.head.app (B.tw B.m)).snoc B.post

structure PscOK (T : PscOur E) : Prop where
  vars : T.VarsOK
  degX : T.DegX
  degY : T.DegY
  inj  : T.ValInj

/-- What is asked. -/
structure OK : Prop where
  pre   : B.pre.Hyp
  link  : B.Z.Link
  back  : B.Z.Back
  ev    : B.Z.ev.OK
  psc0  : PscOK B.Z.T
  psc   : ∀ i ≤ B.m, PscOK (B.T i)
  step0 : LdStepOK z.S B.t0.A (B.s 0).A B.g0
  step  : ∀ i < B.m, LdStepOK z.S (B.t i).A (B.s (i + 1)).A (B.g i)
  post  : LdStepOK z.S (B.t B.m).A z.A B.gz

/-- what comes before the sumcheck i -/
def upTo : (i : ℕ) → LdProg B.a (B.s i)
  | 0 => B.head
  | i + 1 => (B.head.app (B.tw i)).snoc (B.step i)

end LdFrontTab

namespace Spec

def ldSegTab_hyp : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z),
    B.OK → B.prog.Hyp

/-- The zerocheck on a cube as the first block. -/
def ldSegTab_zero : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (Zc : ZeroCube E), Zc.toIn.Link ∧ Zc.toIn.Back ∧
    (Zc.co.OK → Zc.toIn.ev.OK) ∧ Zc.toIn.T.VarsOK ∧ Zc.toIn.T.ValInj ∧
    ∀ st m, Zc.toIn.AllHold st m ↔ Zc.ZeroHolds st m

def ldSegTab_kinds : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc)
      (B : LdFrontTab E Kc z) (k : LdTag → Prop),
    k .sub → k .step → B.pre.All k → B.prog.All k

def ldSegTab_nums : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z),
    B.prog.nAll =
      B.pre.nAll + (1 + (B.Z.T.fmt.length + 3)) +
        ∑ i ∈ Finset.range (B.m + 1), ((B.T i).fmt.length + 3) ∧
    B.prog.pBad = B.pre.pBad ∧
    B.prog.pHid = B.pre.pHid

/-- What zero knowledge asks, beside its hypotheses (`B.prog.Hyp`). -/
def ldSegTab_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (z : LdStage E Kc) (B : LdFrontTab E Kc z)
      (Rd0 : B.Z.T.J → Prop) (Rd : ∀ i, (B.T i).J → Prop) (base : MaskFact B.a.J.W → Prop),
    B.OK → B.pre.Zk base →
    (frPscL Kc B.Z.T z.S z.E₀ z.Wp (B.Z.ride B.R0) B.msg0).GoodM
      (frMask Kc B.Z.T z.S z.E₀ z.Wp (B.Z.ride B.R0) B.msg0 Rd0) →
    B.pre.After base (frFact Kc B.Z.T z.S z.E₀ z.Wp (B.Z.ride B.R0) B.msg0 Rd0) →
    (∀ i ≤ B.m,
      (frPscL Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i)).GoodM
        (frMask Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i) (Rd i))) →
    (∀ i ≤ B.m, (B.upTo i).After base (frFact Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i) (Rd i))) →
    B.prog.Zk base

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E] {z : LdStage E Kc} (B : LdFrontTab E Kc z)

namespace LdFrontTab

theorem tw_zero : B.tw 0 = frPsc Kc (B.T 0) z.S z.E₀ z.Wp (B.A0 0) (B.msg 0) := rfl
theorem tw_succ (k : ℕ) :
    B.tw (k + 1) =
      ((B.tw k).snoc (B.step k)).app
        (frPsc Kc (B.T (k + 1)) z.S z.E₀ z.Wp (B.A0 (k + 1)) (B.msg (k + 1))) := rfl

theorem psc_hyp (h : B.OK) (i : ℕ) (hi : i ≤ B.m) :
    (frPsc Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i)).Hyp :=
  ldSegFront_psc_hyp E Kc _ _ _ _ _ _ (h.psc i hi).vars (h.psc i hi).degX
    (h.psc i hi).degY (h.psc i hi).inj

theorem tw_hyp (h : B.OK) : ∀ k ≤ B.m, (B.tw k).Hyp
  | 0, hk => B.psc_hyp h 0 hk
  | k + 1, hk => by
      rw [tw_succ]
      exact (ldProg_app_hyp E Kc _ _ _ _ _).2
        ⟨(LdProg.hyp_snoc _ _).2 ⟨tw_hyp h k (Nat.le_of_succ_le hk), (h.step k hk).hyp⟩,
          B.psc_hyp h (k + 1) hk⟩

theorem head_hyp (h : B.OK) : B.head.Hyp :=
  (LdProg.hyp_snoc _ _).2
    ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2
        ⟨h.pre, ldSegFront_in_hyp E Kc _ _ _ _ _ _ h.link h.back h.ev h.psc0.vars h.psc0.degX
            h.psc0.degY h.psc0.inj⟩,
      h.step0.hyp⟩

theorem sub_all (k : LdTag → Prop) (hs : k .sub) {a b : LdStage E Kc}
    (p : LdProg a b) (h : p.All fun t => t = .sub) : p.All k :=
  LdProg.all_mono _ _ (fun _ ht => ht ▸ hs) p h

theorem tw_all (k : LdTag → Prop) (hs : k .sub) (hp : k .step) : ∀ j, (B.tw j).All k
  | 0 => sub_all k hs _ (ldSegFront_psc_nums E Kc _ _ _ _ _ _).2.2.2
  | j + 1 => by
      rw [tw_succ]
      exact (ldProg_app_all E Kc _ _ _ _ _ k).2
        ⟨(LdProg.all_snoc _ _ _).2 ⟨tw_all k hs hp j, hp⟩,
          sub_all k hs _ (ldSegFront_psc_nums E Kc _ _ _ _ _ _).2.2.2⟩

theorem tw_nums :
    ∀ k,
      (B.tw k).nAll = ∑ i ∈ Finset.range (k + 1), ((B.T i).fmt.length + 3) ∧
      (B.tw k).pBad = 0 ∧ (B.tw k).pHid = 0
  | 0 => by
      obtain ⟨a1, a2, a3, -⟩ := ldSegFront_psc_nums E Kc (B.T 0) z.S z.E₀ z.Wp (B.A0 0) (B.msg 0)
      rw [tw_zero, Finset.sum_range_one]
      exact ⟨a1, a2, a3⟩
  | k + 1 => by
      obtain ⟨a1, a2, a3⟩ := tw_nums k
      obtain ⟨b1, b2, b3, -⟩ :=
        ldSegFront_psc_nums E Kc (B.T (k + 1)) z.S z.E₀ z.Wp (B.A0 (k + 1)) (B.msg (k + 1))
      obtain ⟨c1, -, c3, c4⟩ := ldStepF_nums z.S (B.t k).A (B.s (k + 1)).A (B.g k)
      obtain ⟨d1, -, d3, d4⟩ := ldProg_app_nums E Kc _ _ _ ((B.tw k).snoc (B.step k))
        (frPsc Kc (B.T (k + 1)) z.S z.E₀ z.Wp (B.A0 (k + 1)) (B.msg (k + 1)))
      rw [tw_succ, d1, d3, d4, LdProg.nAll_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, a1, a2, a3, b1,
        b2, b3, show (B.step k).chain.nAll = 0 from c1, show (B.step k).chain.pBad = 0 from c3,
        show (B.step k).chain.pHid = 0 from c4, Finset.sum_range_succ _ (k + 1)]
      exact ⟨rfl, by simp, by simp⟩

theorem upTo_zero : B.upTo 0 = B.head := rfl
theorem upTo_succ (i : ℕ) : B.upTo (i + 1) = (B.head.app (B.tw i)).snoc (B.step i) := rfl

theorem tw_zk (Rd : ∀ i, (B.T i).J → Prop) (base : MaskFact B.a.J.W → Prop)
    (hM : ∀ i ≤ B.m,
      (frPscL Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i)).GoodM
        (frMask Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i) (Rd i)))
    (hF : ∀ i ≤ B.m,
      (B.upTo i).After base (frFact Kc (B.T i) z.S z.E₀ z.Wp (B.A0 i) (B.msg i) (Rd i))) :
    ∀ k ≤ B.m, (B.tw k).Zk (B.head.After base)
  | 0, hk => ldSegFront_psc_zk E Kc _ _ _ _ _ _ (Rd 0) _ (hM 0 hk) (hF 0 hk)
  | k + 1, hk => by
      rw [tw_succ]
      refine (ldProg_app_zk E Kc _ _ _ _ _ _).2
        ⟨(LdProg.zk_snoc _ _ _).2
            ⟨tw_zk Rd base hM hF k (Nat.le_of_succ_le hk), ldStepF_zk _ _ _ _ _⟩,
          ?_⟩
      refine ldSegFront_psc_zk E Kc _ _ _ _ _ _ (Rd (k + 1)) _ (hM (k + 1) hk) ?_
      have h := hF (k + 1) hk
      rw [upTo_succ, LdProg.after_snoc, ldProg_app_after] at h
      rw [LdProg.after_snoc]
      exact h

end LdFrontTab
end

theorem ldSegTab_hyp : Spec.ldSegTab_hyp := fun E Kc _ _ _ B h =>
  (LdProg.hyp_snoc _ _).2
    ⟨(ldProg_app_hyp E Kc _ _ _ _ _).2 ⟨B.head_hyp h, B.tw_hyp h B.m le_rfl⟩, h.post.hyp⟩

theorem ldSegTab_zero : Spec.ldSegTab_zero := fun E _ _ Zc =>
  ⟨ldZero_link E Zc, ldZero_back E Zc, ldZero_ok E Zc, (ldZero_vars E Zc).1,
    (ldZero_vars E Zc).2, ldZero_all E Zc⟩

theorem ldSegTab_kinds : Spec.ldSegTab_kinds := fun E Kc _ _ _ B k hs hp hpre =>
  (LdProg.all_snoc _ _ _).2
    ⟨(ldProg_app_all E Kc _ _ _ _ _ k).2
        ⟨(LdProg.all_snoc _ _ _).2
            ⟨(ldProg_app_all E Kc _ _ _ _ _ k).2
                ⟨hpre, LdFrontTab.sub_all k hs _ (ldSegFront_in_nums E Kc _ _ _ _ _ _).2.2.2⟩,
              hp⟩,
          B.tw_all k hs hp B.m⟩,
      hp⟩

theorem ldSegTab_nums : Spec.ldSegTab_nums := by
  intro E Kc _ _ z B
  obtain ⟨a1, a2, a3⟩ := B.tw_nums B.m
  obtain ⟨b1, b2, b3, -⟩ := ldSegFront_in_nums E Kc B.Z z.S z.E₀ z.Wp B.R0 B.msg0
  obtain ⟨c1, -, c3, c4⟩ := ldStepF_nums z.S B.t0.A (B.s 0).A B.g0
  obtain ⟨d1, -, d3, d4⟩ := ldStepF_nums z.S (B.t B.m).A z.A B.gz
  obtain ⟨e1, -, e3, e4⟩ := ldProg_app_nums E Kc _ _ _ B.head (B.tw B.m)
  obtain ⟨f1, -, f3, f4⟩ := ldProg_app_nums E Kc _ _ _ B.pre (frIn Kc B.Z z.S z.E₀ z.Wp B.R0 B.msg0)
  unfold LdFrontTab.prog
  rw [LdProg.nAll_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, e1, e3, e4, a1,
    a2, a3, show B.post.chain.nAll = 0 from d1,
    show B.post.chain.pBad = 0 from d3, show B.post.chain.pHid = 0 from d4]
  unfold LdFrontTab.head
  rw [LdProg.nAll_snoc, LdProg.pBad_snoc, LdProg.pHid_snoc, f1, f3, f4, b1, b2,
    b3, show B.step0.chain.nAll = 0 from c1,
    show B.step0.chain.pBad = 0 from c3, show B.step0.chain.pHid = 0 from c4]
  exact ⟨rfl, by simp, by simp⟩

theorem ldSegTab_zk : Spec.ldSegTab_zk := by
  intro E Kc _ _ z B Rd0 Rd base h hp hM0 hF0 hM hF
  refine (LdProg.zk_snoc _ _ _).2
    ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2 ⟨?_, B.tw_zk Rd base hM hF B.m le_rfl⟩,
      ldStepF_zk _ _ _ _ _⟩
  exact (LdProg.zk_snoc _ _ _).2
    ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2
        ⟨hp, ldSegFront_in_zk E Kc _ _ _ _ _ _ Rd0 _ h.link h.back h.ev hM0 hF0⟩,
      ldStepF_zk _ _ _ _ _⟩

end Cb
