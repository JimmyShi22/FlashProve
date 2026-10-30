-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbPairBatch.lean: the law of E2E/ClimbPair.lean for batch protocols: (Snd-B) in its late form
(`BatchInteractiveOracleProof.SndBL`) and round-by-round knowledge soundness with a witness map (`SndBKT`,
Ior/KnowWide.lean) go both ways along a pair with bits, with the same counts.

The way from the protocol with the bits to the one without is E2E/ClimbBatch.lean's. The way back is
the library's for `BatchInteractiveOracleProof.grind` (Iop/BatchGrindProofs.lean, sections 3 and 4), said along a
pair: the new state of a partial transcript is 1 if all its verifier messages so far pass and the
old state of the stripped transcript is 1. (By that file's head it is the state function of a
theorem of StarkWare's "ethSTARK Documentation", in the form for all rounds.)

Main names:
  `RBPair a a'`, `BPair A A'`: a pair with bits that fits the rounds' annotations.
  `BPair.toPair`, `BPair.toBEmb`, `BPair.toEmb_eq`.
  `Pair.stripPT`, `Pair.passPT`, `gst`: partial transcripts; the new state function.
  `jointLaw_down`, `BatchPair`, `BatchPair.sndBL_down`, `BatchPair.sndBKT_down`.
  `BatchPair.sndBKT_iff`: both ways.
  `BatchPair.loc`, `BatchPair.toEmb`, `BatchPair.comap`.

Limits: those of E2E/ClimbPair.lean. Of an annotation (`RAnn`) a pair ties the kind and the two
parts M0, Mj of a prover message through `split`; its fields P0, Pj, pl0, plj, plain, own are tied
by nothing.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.


-/
import E2E.ClimbPair
import E2E.ClimbBatch

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob

/-! ## 1. Pairs that fit the annotations -/

/-- One round: maps of the two parts of a prover message there and back, of verifier messages there
and back, the test, the same kind. -/
structure RBPair {r r' : Round} (a : RAnn r) (a' : RAnn r') where
  f0 : a.M0 → a'.M0
  fj : a.Mj → a'.Mj
  s0 : a'.M0 → a.M0
  sj : a'.Mj → a.Mj
  zero : r.Chal → r'.Chal
  old : r'.Chal → r.Chal
  pass : r'.Chal → Bool
  s0_f0 : ∀ m, s0 (f0 m) = m
  sj_fj : ∀ m, sj (fj m) = m
  old_zero : ∀ c, old (zero c) = c
  pass_zero : ∀ c, pass (zero c) = true
  zero_old : ∀ c', pass c' = true → zero (old c') = c'
  kind : a'.kind = a.kind

namespace RBPair
variable {r r' : Round} {a : RAnn r} {a' : RAnn r'} (u : RBPair a a')

theorem zero_injective : Function.Injective u.zero := fun c d h => by
  have h' := congrArg u.old h
  rwa [u.old_zero, u.old_zero] at h'

/-- The embedding's round. -/
def toREmb : REmb a a' := ⟨u.f0, u.fj, u.zero, u.zero_injective, u.kind⟩

/-- A whole prover message, stripped. -/
def stripMsg (m' : r'.Msg) : r.Msg := a.join (u.s0 (a'.split m').1) (u.sj (a'.split m').2)

theorem stripMsg_join (m0 : a'.M0) (mj : a'.Mj) :
    u.stripMsg (a'.join m0 mj) = a.join (u.s0 m0) (u.sj mj) := by
  unfold stripMsg RAnn.join
  rw [Equiv.apply_symm_apply]

theorem stripMsg_msg (m : r.Msg) : u.stripMsg (u.toREmb.msg m) = m := by
  have h : u.toREmb.msg m = a'.join (u.f0 (a.split m).1) (u.fj (a.split m).2) := rfl
  rw [h, stripMsg_join, u.s0_f0, u.sj_fj]
  exact a.split.symm_apply_apply m

/-- The plain pair's round. -/
def toRPair : RPair r r' :=
  ⟨u.toREmb.msg, u.stripMsg, u.zero, u.old, u.pass, u.stripMsg_msg, u.old_zero, u.pass_zero,
    u.zero_old⟩

theorem strip_join (m0 : a'.M0) (mj : a'.Mj) :
    u.toRPair.strip (a'.join m0 mj) = a.join (u.s0 m0) (u.sj mj) := u.stripMsg_join m0 mj

end RBPair

/-- A pair with bits that fits the annotations A of s and A' of t. -/
def BPair : {s t : Iop.Shape} → RoundSplits s → RoundSplits t → Type
  | [], [], _, _ => Unit
  | [], _ :: _, _, _ => Empty
  | _ :: _, [], _, _ => Empty
  | _ :: _, _ :: _, (a, A), (a', A') => RBPair a a' × BPair A A'

def BPair.toPair : {s t : Iop.Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → BPair A A' → Pair s t
  | [], [], _, _, _ => ()
  | [], _ :: _, _, _, q => Empty.elim q
  | _ :: _, [], _, _, q => Empty.elim q
  | _ :: _, _ :: _, (_, _), (_, _), (u, q) => (u.toRPair, BPair.toPair q)

def BPair.toBEmb : {s t : Iop.Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → BPair A A' → BEmb A A'
  | [], [], _, _, _ => ()
  | [], _ :: _, _, _, q => Empty.elim q
  | _ :: _, [], _, _, q => Empty.elim q
  | _ :: _, _ :: _, (_, _), (_, _), (u, q) => (u.toREmb, BPair.toBEmb q)

/-- The two embeddings of the lists of rounds are one. -/
theorem BPair.toEmb_eq : ∀ {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (q : BPair A A'),
    q.toBEmb.toEmb = q.toPair.toEmb
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, q => Empty.elim q
  | _ :: _, [], _, _, q => Empty.elim q
  | _ :: _, _ :: _, (_, _), (_, _), (u, q) => by
      show (u.toREmb.msg, _, q.toBEmb.toEmb) = (u.toREmb.msg, _, q.toPair.toEmb)
      rw [BPair.toEmb_eq q]
      rfl

theorem localTo_down :
    ∀ {n : ℕ} {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t},
      BPair A A' → RoundSplits.LocalTo n s A → RoundSplits.LocalTo n t A'
  | _, [], [], _, _, _, h => by cases ‹ℕ› <;> exact False.elim h
  | _, [], _ :: _, _, _, q, _ => Empty.elim q
  | _, _ :: _, [], _, _, q, _ => Empty.elim q
  | 0, _ :: _, _ :: _, (_, _), (_, _), (u, _), h => u.kind.trans h
  | _ + 1, _ :: _, _ :: _, (_, _), (_, _), (u, q), h => ⟨u.kind.trans h.1, localTo_down q h.2⟩

/-! ## 2. Partial transcripts; the new state function -/

def Pair.stripP : {s t : Iop.Shape} → Pair s t → AtP t → AtP s
  | [], [], _, τ => τ
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, _, .inl _ => .inl ()
  | _ :: _, _ :: _, (u, p), .inr (m, c, τ) => .inr (u.strip m, u.old c, Pair.stripP p τ)

def Pair.stripV : {s t : Iop.Shape} → Pair s t → AtV t → AtV s
  | [], [], _, τ => τ
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, _), .inl m => .inl (u.strip m)
  | _ :: _, _ :: _, (u, p), .inr (m, c, τ) => .inr (u.strip m, u.old c, Pair.stripV p τ)

/-- A partial transcript of t, stripped. -/
def Pair.stripPT {s t : Iop.Shape} (p : Pair s t) : PTr t → PTr s
  | .atP τ => .atP (p.stripP τ)
  | .atV τ => .atV (p.stripV τ)
  | .full τ => .full (p.strip τ)

def Pair.passP : {s t : Iop.Shape} → Pair s t → AtP t → Bool
  | [], [], _, _ => true
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, _, .inl _ => true
  | _ :: _, _ :: _, (u, p), .inr (_, c, τ) => u.pass c && Pair.passP p τ

def Pair.passV : {s t : Iop.Shape} → Pair s t → AtV t → Bool
  | [], [], _, _ => true
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, _, .inl _ => true
  | _ :: _, _ :: _, (u, p), .inr (_, c, τ) => u.pass c && Pair.passV p τ

/-- All verifier messages of a partial transcript of t pass. -/
def Pair.passPT {s t : Iop.Shape} (p : Pair s t) : PTr t → Bool
  | .atP τ => p.passP τ
  | .atV τ => p.passV τ
  | .full τ => p.passTr τ

theorem Pair.stripPT_empty : ∀ {s t : Iop.Shape} (p : Pair s t),
    p.stripPT (PTr.empty t) = PTr.empty s
  | [], [], _ => rfl
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (_, _) => rfl

theorem Pair.passPT_empty : ∀ {s t : Iop.Shape} (p : Pair s t), p.passPT (PTr.empty t) = true
  | [], [], _ => rfl
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (_, _) => rfl

theorem Pair.stripPT_cons {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t)
    (m : r'.Msg) (c : r'.Chal) :
    ∀ w : PTr t, Pair.stripPT (s := r :: s) (t := r' :: t) (u, p) (PTr.cons m c w) =
      PTr.cons (u.strip m) (u.old c) (p.stripPT w)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem Pair.passPT_cons {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t)
    (m : r'.Msg) (c : r'.Chal) :
    ∀ w : PTr t, Pair.passPT (s := r :: s) (t := r' :: t) (u, p) (PTr.cons m c w) =
      (u.pass c && p.passPT w)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

/-- The new state function: the flag, all verifier messages so far pass, and the old state of the
stripped transcript is 1. -/
def gst {s t : Iop.Shape} (p : Pair s t) (fl : Bool) (S : PTr s → Bool) : PTr t → Bool :=
  fun w => fl && (p.passPT w && S (p.stripPT w))

theorem gst_empty {s t : Iop.Shape} (p : Pair s t) (fl : Bool) (S : PTr s → Bool) :
    gst p fl S (PTr.empty t) = (fl && S (PTr.empty s)) := by
  unfold gst
  rw [Pair.passPT_empty, Pair.stripPT_empty, Bool.true_and]

theorem gst_cons {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t) (fl : Bool)
    (S : PTr (r :: s) → Bool) (m : r'.Msg) (c : r'.Chal) (w : PTr t) :
    gst (s := r :: s) (t := r' :: t) (u, p) fl S (PTr.cons m c w) =
      gst p (fl && u.pass c) (fun v => S (PTr.cons (u.strip m) (u.old c) v)) w := by
  unfold gst
  rw [Pair.passPT_cons, Pair.stripPT_cons, Bool.and_assoc, Bool.and_assoc]

theorem proverLaw_down :
    ∀ {s t : Iop.Shape} (p : Pair s t) (fl : Bool) (S : PTr s → Bool),
      BatchH4.ProverLaw s S → BatchH4.ProverLaw t (gst p fl S)
  | [], [], _, _, _, _, τ, _, _ => Empty.elim τ
  | [], _ :: _, p, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, [], p, _, _, _, _, _, _ => Empty.elim p
  | _ :: _, _ :: _, (u, _), fl, S, h, .inl _, m, h0 => by
      cases fl
      · rfl
      · exact h (.inl ()) (u.strip m) h0
  | r :: s, r' :: t, (u, p), fl, S, h, .inr (m', c', τ), m, h0 => by
      have h0' : gst (s := r :: s) (t := r' :: t) (u, p) fl S (PTr.cons m' c' (.atP τ)) = false :=
        h0
      rw [gst_cons] at h0'
      have h1 := proverLaw_down p (fl && u.pass c')
        (fun v => S (PTr.cons (u.strip m') (u.old c') v)) (h.tail _ _) τ m h0'
      rw [← gst_cons] at h1
      exact h1

theorem Pair.idx_stripP : ∀ {s t : Iop.Shape} (p : Pair s t) (τ : AtP t), (p.stripP τ).idx = τ.idx
  | [], [], _, τ => Empty.elim τ
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (_, _), .inl _ => rfl
  | _ :: _, _ :: _, (_, p), .inr (_, _, τ) => congrArg (· + 1) (Pair.idx_stripP p τ)

/-! ## 3. The law on the verifier messages of a batch -/

theorem gst_step {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t) (fl : Bool)
    (S : PTr (r :: s) → Bool) (m : r'.Msg) (c : r'.Chal)
    (h : gst (s := r :: s) (t := r' :: t) (u, p) fl S (PTr.cons m c (PTr.empty t)) = true) :
    fl = true ∧ u.pass c = true ∧ S (PTr.cons (u.strip m) (u.old c) (PTr.empty s)) = true := by
  rw [gst_cons, gst_empty, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem gst_atV {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t)
    (S : PTr (r :: s) → Bool) (m : r'.Msg) :
    gst (s := r :: s) (t := r' :: t) (u, p) true S (.atV (Sum.inl m)) =
      S (.atV (Sum.inl (u.strip m))) := rfl

/-- The condition on the verifier message of one round, with the same count e. -/
theorem round_down {N : ℕ} {r r' : Round} {s t : Iop.Shape} (u : RPair r r') (p : Pair s t)
    (e : ℕ) (St : Fin N → Option (PTr (r :: s) → Bool)) (fl : Fin N → Bool)
    (Jn' : Fin N → r'.Msg) (Jn : Fin N → r.Msg) (sj : ∀ j, u.strip (Jn' j) = Jn j) :
    ∀ k : Iop.Kind,
    (match k with
      | .lo =>
        ∀ j S, St j = some S → S (.atV (Sum.inl (Jn j))) = false →
          cnt (fun c : r.Chal => S (PTr.cons (Jn j) c (PTr.empty s)) = true) ≤ e
      | .sh =>
        cnt (fun c : r.Chal =>
            ∃ j S,
              St j = some S ∧
              S (.atV (Sum.inl (Jn j))) = false ∧
              S (PTr.cons (Jn j) c (PTr.empty s)) = true) ≤ e) →
    (match k with
      | .lo =>
        ∀ j S, (St j).map (gst (s := r :: s) (t := r' :: t) (u, p) (fl j)) = some S →
          S (.atV (Sum.inl (Jn' j))) = false →
          cnt (fun c : r'.Chal => S (PTr.cons (Jn' j) c (PTr.empty t)) = true) ≤ e
      | .sh => cnt (fun c : r'.Chal =>
          ∃ j S,
            (St j).map (gst (s := r :: s) (t := r' :: t) (u, p) (fl j)) = some S ∧
            S (.atV (Sum.inl (Jn' j))) = false ∧
            S (PTr.cons (Jn' j) c (PTr.empty t)) = true) ≤ e)
  | .sh => fun hround => by
      refine le_trans
        (cnt_mono (Q := fun c : r'.Chal =>
              u.pass c = true ∧
              ∃ j S,
                St j = some S ∧
                S (.atV (Sum.inl (Jn j))) = false ∧
                S (PTr.cons (Jn j) (u.old c) (PTr.empty s)) = true) ?_)
        ((u.cnt_pass_le _).trans hround)
      rintro c ⟨j, S', hS', h0, h1⟩
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      obtain ⟨hf, hp, h1'⟩ := gst_step u p (fl j) S _ c h1
      rw [hf, gst_atV] at h0
      rw [sj] at h0 h1'
      exact ⟨hp, j, S, hS, h0, h1'⟩
  | .lo => fun hround j S' hS' h0 => by
      obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
      cases hf : fl j
      · exact (le_of_eq (cnt_false fun c hc => Bool.false_ne_true hc)).trans (Nat.zero_le e)
      · rw [hf, gst_atV, sj] at h0
        refine le_trans
          (cnt_mono (Q := fun c : r'.Chal =>
                u.pass c = true ∧ S (PTr.cons (Jn j) (u.old c) (PTr.empty s)) = true)
            fun c hc => ?_)
          ((u.cnt_pass_le _).trans (hround j S hS h0))
        obtain ⟨_, hp, h1'⟩ := gst_step u p true S _ c hc
        rw [sj] at h1'
        exact ⟨hp, h1'⟩

/-- **The law on verifier messages**, from s to t, with the same counts. -/
theorem jointLaw_down {N : ℕ} :
    ∀ {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (q : BPair A A') (ε : Err s)
        (St : Fin N → Option (PTr s → Bool)) (fl : Fin N → Bool),
      JointLaw N s A ε St →
      JointLaw N t A' (q.toPair.down ε) (fun j => (St j).map (gst q.toPair (fl j)))
  | [], [], _, _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, q, _, _, _, _ => Empty.elim q
  | _ :: _, [], _, _, q, _, _, _, _ => Empty.elim q
  | r :: s, r' :: t, (a, A), (a', A'), (u, q), (e, ε), St, fl, h => by
      show JointLaw N (r' :: t) (a', A') (e, q.toPair.down ε) _
      intro (m0 : a'.M0) (m : Fin N → a'.Mj)
      obtain ⟨hround, hrest⟩ := h (u.s0 m0) (fun j => u.sj (m j))
      rw [← u.kind] at hround
      refine ⟨round_down u.toRPair q.toPair e St fl (fun j => a'.join m0 (m j))
          (fun j => a.join (u.s0 m0) (u.sj (m j))) (fun j => u.strip_join m0 (m j)) a'.kind hround,
        fun v' => ?_⟩
      obtain ⟨v, hv⟩ := all_of_kind u.kind.symm u.toRPair.old N v'
      have ih := jointLaw_down q ε _ (fun j => fl j && u.toRPair.pass (a'.kind.slot v' j))
        (hrest v)
      refine cast (congrArg (JointLaw N t A' (q.toPair.down ε)) ?_) ih
      funext j
      beta_reduce
      refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
      congr 1
      funext S w
      show gst q.toPair (fl j && u.toRPair.pass (a'.kind.slot v' j))
          (fun z => S (PTr.cons (a.join (u.s0 m0) (u.sj (m j))) (a.kind.slot v j) z)) w =
        gst (s := r :: s) (t := r' :: t) (u.toRPair, q.toPair) (fl j) S
          (PTr.cons (a'.join m0 (m j)) (a'.kind.slot v' j) w)
      rw [gst_cons, hv, u.strip_join]

/-! ## 4. Batch protocols -/

variable {X : Type} {E : ExtSpec}

/-- A pair with bits that fits the annotations of Q₀ and Q, and Q's local verifier accepts a
transcript exactly if all its verifier messages pass and Q₀'s accepts the stripped transcript. -/
structure BatchPair (Q₀ Q : BatchInteractiveOracleProof X E) where
  pair : BPair Q₀.ann Q.ann
  acc : ∀ (x : X) (y : E.Str) (τ' : Tr Q.loc.shape),
    Q.loc.accept x y τ' = (pair.toPair.passTr τ' && Q₀.loc.accept x y (pair.toPair.strip τ'))

/-- The local protocols. -/
def BatchPair.loc {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) : ProtoPair Q₀.loc Q.loc :=
  ⟨S.pair.toPair, S.acc⟩

/-- The embedding of Q₀ in Q. -/
def BatchPair.toEmb {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) : BatchEmb Q₀ Q :=
  ⟨S.pair.toBEmb, fun x y τ =>
    (congrArg (fun e => Q.loc.accept x y (Emb.tr e τ)) S.pair.toEmb_eq).trans
      (S.loc.toEmb.acc x y τ)⟩

theorem full_down {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) (St : PTr Q₀.loc.shape → Bool)
    (x : X) (y : E.Str)
    (h3 : ∀ τ : Tr Q₀.loc.shape, St (.full τ) = false → Q₀.loc.accept x y τ = false)
    (τ' : Tr Q.loc.shape) (hτ : gst S.pair.toPair true St (.full τ') = false) :
    Q.loc.accept x y τ' = false := by
  rw [S.acc]
  have hτ' : (S.pair.toPair.passTr τ' && St (.full (S.pair.toPair.strip τ'))) = false := hτ
  cases hp : S.pair.toPair.passTr τ'
  · rfl
  · rw [hp, Bool.true_and] at hτ'
    rw [Bool.true_and]
    exact h3 _ hτ'

/-- **(Snd-B), late form, from Q₀ to Q.** -/
theorem BatchPair.sndBL_down {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) {N : ℕ}
    {early : X → X} {late : Option ℕ} {L : X → E.Str → Prop} {ε : Err Q₀.loc.shape}
    (h : Q₀.SndBL N early late L ε) : Q.SndBL N early late L (S.pair.toPair.down ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  refine ⟨fun n hn => ⟨(h0 n hn).1, localTo_down S.pair (h0 n hn).2⟩,
    fun y x => gst S.pair.toPair true (State y x),
    fun y x hL => ?_,
    fun y x => proverLaw_down S.pair.toPair true (State y x) (h2 y x),
    fun y x τ hL hn hτ => ?_,
    fun y x τ hL hτ => full_down S (State y _) x y (fun τ₀ => h3 y x τ₀ hL) τ hτ,
    fun y x => ?_⟩
  · show gst S.pair.toPair true (State y (early x)) (PTr.empty Q.loc.shape) = false
    rw [gst_empty, Bool.true_and]
    exact h1 y x hL
  · show (true && (S.pair.toPair.passP τ && State y x (.atP (S.pair.toPair.stripP τ)))) = false
    have hτ' : (true && (S.pair.toPair.passP τ &&
        State y (early x) (.atP (S.pair.toPair.stripP τ)))) = false := hτ
    cases hp : S.pair.toPair.passP τ
    · rfl
    · rw [hp, Bool.true_and, Bool.true_and] at hτ'
      rw [Bool.true_and, Bool.true_and]
      exact hsw y x (S.pair.toPair.stripP τ) hL (by rw [Pair.idx_stripP]; exact hn) hτ'
  · refine cast (congrArg (JointLaw N Q.loc.shape Q.ann (S.pair.toPair.down ε)) ?_)
      (jointLaw_down S.pair ε _ (fun _ => true) (h4 y x))
    funext j
    cases x j <;> rfl

/-- The guarded protocols (Ior/KnowWide.lean): the larger goal is the smaller goal at the stripped
transcript. -/
def BatchPair.guardP {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q)
    (ok : X → E.Str → Tr Q₀.loc.shape → Prop) :
    BatchPair (Q₀.guardP ok) (Q.guardP fun x y τ' => ok x y (S.pair.toPair.strip τ')) :=
  ⟨S.pair, fun x y τ' => by
    classical
    show (Q.loc.accept x y τ' && !decide (ok x y (S.pair.toPair.strip τ'))) =
      (S.pair.toPair.passTr τ' &&
        (Q₀.loc.accept x y (S.pair.toPair.strip τ') && !decide (ok x y (S.pair.toPair.strip τ'))))
    rw [S.acc x y τ', Bool.and_assoc]⟩

/-- **Round-by-round knowledge soundness of a batch, from Q₀ to Q**: the witness map reads the
stripped transcript. -/
theorem BatchPair.sndBKT_down {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) {Wn : Type} {N : ℕ}
    {early : X → X} {late : Option ℕ} {R : X → E.Str → Wn → Prop}
    {wit : X → E.Str → Tr Q₀.loc.shape → Wn} {ε : Err Q₀.loc.shape}
    (h : Q₀.SndBKT N early late R wit ε) :
    Q.SndBKT N early late R (fun x y τ' => wit x y (S.pair.toPair.strip τ'))
      (S.pair.toPair.down ε) :=
  (S.guardP fun x y τ => R x y (wit x y τ)).sndBL_down h

/-- From Q to Q₀, in the pair's own terms. -/
theorem BatchPair.sndBKT_up {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) {Wn : Type} {N : ℕ}
    {early : X → X} {late : Option ℕ} {R : X → E.Str → Wn → Prop}
    {wit : X → E.Str → Tr Q.loc.shape → Wn} {ε : Err Q.loc.shape}
    (h : Q.SndBKT N early late R wit ε) :
    Q₀.SndBKT N early late R (fun x y τ => wit x y (S.pair.toPair.toEmb.tr τ))
      (S.pair.toPair.toEmb.err ε) :=
  S.toEmb.sndBKT_at S.pair.toPair.toEmb S.pair.toEmb_eq h

/-- **Both ways**: Q₀ has round-by-round knowledge soundness with the witness map wit and the counts
ε if and only if Q has it, for the same relation, with wit at the stripped transcript and the same
counts. -/
theorem BatchPair.sndBKT_iff {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) {Wn : Type} (N : ℕ)
    (early : X → X) (late : Option ℕ) (R : X → E.Str → Wn → Prop)
    (wit : X → E.Str → Tr Q₀.loc.shape → Wn) (ε : Err Q₀.loc.shape) :
    Q₀.SndBKT N early late R wit ε ↔
      Q.SndBKT N early late R (fun x y τ' => wit x y (S.pair.toPair.strip τ'))
        (S.pair.toPair.down ε) := by
  refine ⟨S.sndBKT_down, fun h => ?_⟩
  have hw : (fun (x : X) (y : E.Str) (τ : Tr Q₀.loc.shape) =>
      wit x y (S.pair.toPair.strip (S.pair.toPair.toEmb.tr τ))) = wit := by
    funext x y τ
    rw [Pair.strip_tr]
  exact (congrArg₂ (fun w e => Q₀.SndBKT N early late R w e) hw
    (S.pair.toPair.err_down ε)).mp (S.sndBKT_up h)

/-- The instance read through a function, on both sides. -/
def BatchPair.comap {X' : Type} {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchPair Q₀ Q) (f : X' → X) :
    BatchPair (Q₀.comap f) (Q.comap f) :=
  ⟨S.pair, fun x y τ' => S.acc (f x) y τ'⟩

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.jointLaw_down
#print axioms AtPublicFiles.Climb.BatchPair.sndBL_down
#print axioms AtPublicFiles.Climb.BatchPair.sndBKT_down
#print axioms AtPublicFiles.Climb.BatchPair.sndBKT_iff
