-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbBatch.lean: the law of E2E/ClimbEmb.lean for batch protocols: (Snd-B) in its late form
(`BatchInteractiveOracleProof.SndBL`), its form with a goal (`SndBP`) and round-by-round knowledge soundness with a
witness map (`SndBKT`, Ior/KnowWide.lean) go from the larger protocol to the embedded one, with the
same counts.

These three are written with a state function on partial transcripts and a law on the verifier
messages of a whole batch (`JointLaw`, Iop/Batch.lean), not with `Doomed`. The new state of a
partial transcript is the old state of its image.

Main names:
  `REmb a a'`, `BEmb A A'`: an embedding that fits the rounds' annotations: maps of the shared part
    and of a request's own part of a prover message, a one-to-one map of verifier messages, the
    same kind (shared or local).
  `BEmb.toEmb`: the embedding of the lists of rounds behind it.
  `Emb.atP`, `Emb.atV`, `Emb.ptr`: the image of a partial transcript.
  `jointLaw_of_emb`: the law on verifier messages.
  `BatchEmb Q₀ Q`; `BatchEmb.sndBL`, `BatchEmb.sndBP`, `BatchEmb.sndBKT`: the three laws.
  `BatchEmb.comap`: the instance read through a function, on both sides.
  `BEmb.timesShared`: multiplying the shared rounds' counts commutes with copying the list.

The witness map. The smaller protocol's witness map is the larger one's at the image of the
transcript: `fun x y τ => wit x y (emb.tr τ)`.

Limits: those of E2E/ClimbEmb.lean.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.

-/
import E2E.ClimbEmb
import Ior.KnowWide
import Iop.BatchSound
import Iop.BatchPullProofs
import Hiop.RecKit

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open scoped ENNReal

/-! ## 1. Partial transcripts -/

/-- The image of a partial transcript that waits for the prover. -/
def Emb.atP : {s t : Iop.Shape} → Emb s t → AtP s → AtP t
  | [], [], _, τ => τ
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | _ :: _, _ :: _, _, .inl _ => .inl ()
  | _ :: _, _ :: _, (f, c, e), .inr (m, x, τ) => .inr (f m, c.1 x, Emb.atP e τ)

/-- The image of a partial transcript that waits for the verifier. -/
def Emb.atV : {s t : Iop.Shape} → Emb s t → AtV s → AtV t
  | [], [], _, τ => τ
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | _ :: _, _ :: _, (f, _, _), .inl m => .inl (f m)
  | _ :: _, _ :: _, (f, c, e), .inr (m, x, τ) => .inr (f m, c.1 x, Emb.atV e τ)

/-- The image of a partial transcript. -/
def Emb.ptr {s t : Iop.Shape} (e : Emb s t) : PTr s → PTr t
  | .atP τ => .atP (e.atP τ)
  | .atV τ => .atV (e.atV τ)
  | .full τ => .full (e.tr τ)

theorem Emb.ptr_empty : ∀ {s t : Iop.Shape} (e : Emb s t), e.ptr (PTr.empty s) = PTr.empty t
  | [], [], _ => rfl
  | [], _ :: _, e => Empty.elim e
  | _ :: _, [], e => Empty.elim e
  | _ :: _, _ :: _, (_, _, _) => rfl

theorem Emb.ptr_cons {r r' : Round} {s t : Iop.Shape} (f : r.Msg → r'.Msg)
    (c : {f : r.Chal → r'.Chal // Function.Injective f}) (e : Emb s t) (m : r.Msg) (x : r.Chal) :
    ∀ p : PTr s, Emb.ptr (s := r :: s) (t := r' :: t) (f, c, e) (PTr.cons m x p) =
      PTr.cons (f m) (c.1 x) (e.ptr p)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem Emb.idx_atP : ∀ {s t : Iop.Shape} (e : Emb s t) (τ : AtP s), (e.atP τ).idx = τ.idx
  | [], [], _, τ => Empty.elim τ
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | _ :: _, _ :: _, (_, _, _), .inl _ => rfl
  | _ :: _, _ :: _, (_, _, e), .inr (_, _, τ) => congrArg (· + 1) (Emb.idx_atP e τ)

/-- "A prover message never changes 0 to 1" is kept. -/
theorem proverLaw_of_emb :
    ∀ {s t : Iop.Shape} (e : Emb s t) (S : PTr t → Bool),
      BatchH4.ProverLaw t S → BatchH4.ProverLaw s (fun p => S (e.ptr p))
  | [], [], _, _, _, τ, _, _ => Empty.elim τ
  | [], _ :: _, e, _, _, _, _, _ => Empty.elim e
  | _ :: _, [], e, _, _, _, _, _ => Empty.elim e
  | _ :: _, _ :: _, (f, _, _), _, h, .inl _, m, h0 => h (.inl ()) (f m) h0
  | _ :: _, _ :: _, (f, c, e), S, h, .inr (m', x', τ), m, h0 =>
    proverLaw_of_emb e (fun u => S (PTr.cons (f m') (c.1 x') u)) (h.tail (f m') (c.1 x')) τ m h0

/-! ## 2. Embeddings that fit the annotations -/

/-- One round: maps of the two parts of a prover message, a one-to-one map of verifier messages, the
same kind. -/
structure REmb {r r' : Round} (a : RAnn r) (a' : RAnn r') where
  f0 : a.M0 → a'.M0
  fj : a.Mj → a'.Mj
  ch : r.Chal → r'.Chal
  inj : Function.Injective ch
  kind : a'.kind = a.kind

/-- The map of whole prover messages. -/
def REmb.msg {r r' : Round} {a : RAnn r} {a' : RAnn r'} (u : REmb a a') (m : r.Msg) : r'.Msg :=
  a'.join (u.f0 (a.split m).1) (u.fj (a.split m).2)

theorem REmb.msg_join {r r' : Round} {a : RAnn r} {a' : RAnn r'} (u : REmb a a') (m0 : a.M0)
    (mj : a.Mj) : u.msg (a.join m0 mj) = a'.join (u.f0 m0) (u.fj mj) := by
  unfold REmb.msg RAnn.join
  rw [Equiv.apply_symm_apply]

/-- An embedding that fits the annotations A of s and A' of t. -/
def BEmb : {s t : Iop.Shape} → RoundSplits s → RoundSplits t → Type
  | [], [], _, _ => Unit
  | [], _ :: _, _, _ => Empty
  | _ :: _, [], _, _ => Empty
  | _ :: _, _ :: _, (a, A), (a', A') => REmb a a' × BEmb A A'

/-- The embedding of the lists of rounds. -/
def BEmb.toEmb : {s t : Iop.Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → BEmb A A' → Emb s t
  | [], [], _, _, _ => ()
  | [], _ :: _, _, _, e => Empty.elim e
  | _ :: _, [], _, _, e => Empty.elim e
  | _ :: _, _ :: _, (_, _), (_, _), (u, e) => (u.msg, ⟨u.ch, u.inj⟩, BEmb.toEmb e)

/-- Two in a row. -/
def BEmb.app : {s t s' t' : Iop.Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → {B : RoundSplits s'} →
    {B' : RoundSplits t'} → BEmb A A' → BEmb B B' → BEmb (RoundSplits.app A B) (RoundSplits.app A' B')
  | [], [], _, _, _, _, _, _, _, e' => e'
  | [], _ :: _, _, _, _, _, _, _, e, _ => Empty.elim e
  | _ :: _, [], _, _, _, _, _, _, e, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (_, _), (_, _), _, _, (u, e), e' => (u, BEmb.app e e')

theorem BEmb.toEmb_app : ∀ {s t s' t' : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} {B : RoundSplits s'}
    {B' : RoundSplits t'} (e : BEmb A A') (e' : BEmb B B'),
      (BEmb.app e e').toEmb = Emb.app e.toEmb e'.toEmb
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _, _, e, _ => Empty.elim e
  | _ :: _, [], _, _, _, _, _, _, e, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (_, _), (_, _), _, _, (u, e), e' => by
      show (u.msg, _, (BEmb.app e e').toEmb) = (u.msg, _, Emb.app e.toEmb e'.toEmb)
      rw [BEmb.toEmb_app e e']

theorem localTo_of_emb :
    ∀ {n : ℕ} {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t},
      BEmb A A' → RoundSplits.LocalTo n t A' → RoundSplits.LocalTo n s A
  | _, [], [], _, _, _, h => by cases ‹ℕ› <;> exact False.elim h
  | _, [], _ :: _, _, _, e, _ => Empty.elim e
  | _, _ :: _, [], _, _, e, _ => Empty.elim e
  | 0, _ :: _, _ :: _, (_, _), (_, _), (u, _), h => u.kind.symm.trans h
  | _ + 1, _ :: _, _ :: _, (_, _), (_, _), (u, e), h =>
    ⟨u.kind.symm.trans h.1, localTo_of_emb e h.2⟩

/-- Multiplying the counts of the shared rounds by N, then copying the list, is copying it and then
multiplying. -/
theorem BEmb.timesShared (N : ℕ) :
    ∀ {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (e : BEmb A A') (ε : Err t),
      e.toEmb.err (Err.timesShared N A' ε) = Err.timesShared N A (e.toEmb.err ε)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, e, _ => Empty.elim e
  | _ :: _, [], _, _, e, _ => Empty.elim e
  | _ :: _, _ :: _, (a, A), (a', A'), (u, e), (n, ε) => by
      show ((match a'.kind with | .lo => n | .sh => N * n),
          e.toEmb.err (Err.timesShared N A' ε)) =
        ((match a.kind with | .lo => n | .sh => N * n), Err.timesShared N A (e.toEmb.err ε))
      rw [u.kind, BEmb.timesShared N e ε]

/-! ## 3. The law on the verifier messages of a batch -/

/-- A verifier message of a whole batch, carried along a map, where the two kinds are equal. -/
theorem all_of_kind {k k' : Iop.Kind} (hk : k' = k) {C C' : Type} (ch : C → C') (N : ℕ)
    (v : k.All N C) : ∃ v' : k'.All N C', ∀ j : Fin N, k'.slot v' j = ch (k.slot v j) := by
  subst hk
  exact ⟨Iop.Kind.mapAll ch _ v, fun j => BatchPull.slot_mapAll ch j _ v⟩

/-- The condition on the verifier message of one round, with the same count n. Jn j, Jn' j: the
prover messages in the transcripts of request j, smaller and larger (`sj`: Jn' j is the image of
Jn j). -/
theorem round_of_emb {N : ℕ} {r r' : Round} {s t : Iop.Shape} (f : r.Msg → r'.Msg)
    (c : {f : r.Chal → r'.Chal // Function.Injective f}) (e : Emb s t) (n : ℕ)
    (St' : Fin N → Option (PTr (r' :: t) → Bool)) (Jn : Fin N → r.Msg) (Jn' : Fin N → r'.Msg)
    (sj : ∀ j, f (Jn j) = Jn' j) : ∀ k : Iop.Kind,
    (match k with
      | .lo =>
        ∀ j S, St' j = some S → S (.atV (Sum.inl (Jn' j))) = false →
          cnt (fun x : r'.Chal => S (PTr.cons (Jn' j) x (PTr.empty t)) = true) ≤ n
      | .sh =>
        cnt (fun x : r'.Chal =>
            ∃ j S,
              St' j = some S ∧
              S (.atV (Sum.inl (Jn' j))) = false ∧
              S (PTr.cons (Jn' j) x (PTr.empty t)) = true) ≤ n) →
    (match k with
      | .lo =>
        ∀ j S,
          (St' j).map (fun S' p => S' (Emb.ptr (s := r :: s) (t := r' :: t) (f, c, e) p)) =
            some S →
          S (.atV (Sum.inl (Jn j))) = false →
          cnt (fun x : r.Chal => S (PTr.cons (Jn j) x (PTr.empty s)) = true) ≤ n
      | .sh =>
        cnt (fun x : r.Chal =>
            ∃ j S,
              (St' j).map (fun S' p => S' (Emb.ptr (s := r :: s) (t := r' :: t) (f, c, e) p)) =
                some S ∧
              S (.atV (Sum.inl (Jn j))) = false ∧
              S (PTr.cons (Jn j) x (PTr.empty s)) = true) ≤ n)
  | .sh => fun hround => by
      refine le_trans (cnt_le_of_injective (α := r.Chal) (β := r'.Chal) c.1 c.2 ?_) hround
      rintro x ⟨j, S, hS, h0, h1⟩
      obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.1 hS
      have h0' : S' (.atV (Sum.inl (f (Jn j)))) = false := h0
      have h1' : S' (Emb.ptr (s := r :: s) (t := r' :: t) (f, c, e)
          (PTr.cons (Jn j) x (PTr.empty s))) = true := h1
      rw [Emb.ptr_cons, Emb.ptr_empty, sj] at h1'
      rw [sj] at h0'
      exact ⟨j, S', hS', h0', h1'⟩
  | .lo => fun hround j S hS h0 => by
      obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.1 hS
      have h0' : S' (.atV (Sum.inl (f (Jn j)))) = false := h0
      rw [sj] at h0'
      refine le_trans (cnt_le_of_injective (α := r.Chal) (β := r'.Chal) c.1 c.2 ?_)
        (hround j S' hS' h0')
      intro x h1
      have h1' : S' (Emb.ptr (s := r :: s) (t := r' :: t) (f, c, e)
          (PTr.cons (Jn j) x (PTr.empty s))) = true := h1
      rw [Emb.ptr_cons, Emb.ptr_empty, sj] at h1'
      exact h1'

/-- **The law on verifier messages** goes to the embedded list of rounds, with the same counts; the
new state of a partial transcript is the old state of its image. -/
theorem jointLaw_of_emb {N : ℕ} :
    ∀ {s t : Iop.Shape} {A : RoundSplits s} {A' : RoundSplits t} (e : BEmb A A') (ε : Err t)
        (St' : Fin N → Option (PTr t → Bool)),
      JointLaw N t A' ε St' →
      JointLaw N s A (e.toEmb.err ε) (fun j => (St' j).map fun S' p => S' (e.toEmb.ptr p))
  | [], [], _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, e, _, _, _ => Empty.elim e
  | _ :: _, [], _, _, e, _, _, _ => Empty.elim e
  | r :: s, r' :: t, (a, A), (a', A'), (u, e), (n, ε), St', h => by
      show JointLaw N (r :: s) (a, A) (n, e.toEmb.err ε) _
      intro (m0 : a.M0) (m : Fin N → a.Mj)
      obtain ⟨hround, hrest⟩ := h (u.f0 m0) (fun j => u.fj (m j))
      rw [u.kind] at hround
      refine ⟨round_of_emb u.msg ⟨u.ch, u.inj⟩ e.toEmb n St' (fun j => a.join m0 (m j))
          (fun j => a'.join (u.f0 m0) (u.fj (m j))) (fun j => u.msg_join m0 (m j)) a.kind hround,
        fun v => ?_⟩
      obtain ⟨v', hv'⟩ := all_of_kind u.kind u.ch N v
      have ih := jointLaw_of_emb e ε _ (hrest v')
      refine cast (congrArg (JointLaw N s A (e.toEmb.err ε)) ?_) ih
      funext j
      beta_reduce
      refine (Option.map_map _ _ _).trans (Eq.trans ?_ (Option.map_map _ _ _).symm)
      congr 1
      funext S p
      show S (PTr.cons (a'.join (u.f0 m0) (u.fj (m j))) (a'.kind.slot v' j) (e.toEmb.ptr p)) =
        S (Emb.ptr (s := r :: s) (t := r' :: t) (u.msg, ⟨u.ch, u.inj⟩, e.toEmb)
          (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) p))
      rw [Emb.ptr_cons, u.msg_join, hv']

/-! ## 4. Batch protocols -/

variable {X : Type} {E : ExtSpec}

/-- The batch protocol Q₀ embedded in Q: an embedding that fits the two annotations, along which the
two local verifiers decide alike. -/
structure BatchEmb (Q₀ Q : BatchInteractiveOracleProof X E) where
  emb : BEmb Q₀.ann Q.ann
  acc : ∀ (x : X) (y : E.Str) (τ : Tr Q₀.loc.shape),
    Q.loc.accept x y (emb.toEmb.tr τ) = Q₀.loc.accept x y τ

/-- The local protocols. -/
def BatchEmb.loc {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q) : ProtoEmb Q₀.loc Q.loc :=
  ⟨S.emb.toEmb, S.acc⟩

/-- **(Snd-B), late form**: the same language, the same early and late parts, the same counts. -/
theorem BatchEmb.sndBL {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q) {N : ℕ} {early : X → X}
    {late : Option ℕ} {L : X → E.Str → Prop} {ε : Err Q.loc.shape}
    (h : Q.SndBL N early late L ε) : Q₀.SndBL N early late L (S.emb.toEmb.err ε) := by
  obtain ⟨h0, State, h1, h2, hsw, h3, h4⟩ := h
  refine ⟨fun n hn => ⟨(h0 n hn).1, localTo_of_emb S.emb (h0 n hn).2⟩,
    fun y x p => State y x (S.emb.toEmb.ptr p),
    fun y x hL => ?_,
    fun y x => proverLaw_of_emb S.emb.toEmb (State y x) (h2 y x),
    fun y x τ hL hn hτ => ?_,
    fun y x τ hL hτ => ?_,
    fun y x => ?_⟩
  · show State y (early x) (S.emb.toEmb.ptr (PTr.empty Q₀.loc.shape)) = false
    rw [Emb.ptr_empty]
    exact h1 y x hL
  · exact hsw y x (S.emb.toEmb.atP τ) hL (by rw [Emb.idx_atP]; exact hn) hτ
  · exact (S.acc x y τ).symm.trans (h3 y x (S.emb.toEmb.tr τ) hL hτ)
  · refine cast (congrArg (JointLaw N Q₀.loc.shape Q₀.ann (S.emb.toEmb.err ε)) ?_)
      (jointLaw_of_emb S.emb ε _ (h4 y x))
    funext j
    cases x j <;> rfl

/-- The guarded protocols (Ior/KnowWide.lean): the smaller goal is the larger goal at the image. -/
def BatchEmb.guardP {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q)
    (ok : X → E.Str → Tr Q.loc.shape → Prop) :
    BatchEmb (Q₀.guardP fun x y τ => ok x y (S.emb.toEmb.tr τ)) (Q.guardP ok) :=
  ⟨S.emb, fun x y τ => by
    classical
    show (Q.loc.accept x y (S.emb.toEmb.tr τ) && !decide (ok x y (S.emb.toEmb.tr τ))) =
      (Q₀.loc.accept x y τ && !decide (ok x y (S.emb.toEmb.tr τ)))
    rw [S.acc x y τ]⟩

/-- **(Snd-B) with a goal.** -/
theorem BatchEmb.sndBP {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q) {N : ℕ} {early : X → X}
    {late : Option ℕ} {ok : X → E.Str → Tr Q.loc.shape → Prop} {ε : Err Q.loc.shape}
    (h : Q.SndBP N early late ok ε) :
    Q₀.SndBP N early late (fun x y τ => ok x y (S.emb.toEmb.tr τ)) (S.emb.toEmb.err ε) :=
  (S.guardP ok).sndBL h

/-- **Round-by-round knowledge soundness of a batch**: the same relation, the same counts; the
witness map reads the image of the transcript. -/
theorem BatchEmb.sndBKT {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q) {Wn : Type} {N : ℕ}
    {early : X → X} {late : Option ℕ} {R : X → E.Str → Wn → Prop}
    {wit : X → E.Str → Tr Q.loc.shape → Wn} {ε : Err Q.loc.shape}
    (h : Q.SndBKT N early late R wit ε) :
    Q₀.SndBKT N early late R (fun x y τ => wit x y (S.emb.toEmb.tr τ)) (S.emb.toEmb.err ε) :=
  S.sndBP (ok := fun x y τ => R x y (wit x y τ)) h

/-- The same, where the embedding of the lists of rounds is known under another name e₀. -/
theorem BatchEmb.sndBKT_at {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q)
    (e₀ : Emb Q₀.loc.shape Q.loc.shape) (he : S.emb.toEmb = e₀) {Wn : Type} {N : ℕ}
    {early : X → X} {late : Option ℕ} {R : X → E.Str → Wn → Prop}
    {wit : X → E.Str → Tr Q.loc.shape → Wn} {ε : Err Q.loc.shape}
    (h : Q.SndBKT N early late R wit ε) :
    Q₀.SndBKT N early late R (fun x y τ => wit x y (e₀.tr τ)) (e₀.err ε) := by
  subst he
  exact S.sndBKT h

/-- The instance read through a function, on both sides. -/
def BatchEmb.comap {X' : Type} {Q₀ Q : BatchInteractiveOracleProof X E} (S : BatchEmb Q₀ Q) (f : X' → X) :
    BatchEmb (Q₀.comap f) (Q.comap f) :=
  ⟨S.emb, fun x y τ => S.acc (f x) y τ⟩

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.jointLaw_of_emb
#print axioms AtPublicFiles.Climb.BatchEmb.sndBL
#print axioms AtPublicFiles.Climb.BatchEmb.sndBKT
#print axioms AtPublicFiles.Climb.BEmb.timesShared
