-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbPair.lean: two lists of rounds of which the second is the first with further verifier
messages, all of which are to be rejected, said as a pair of maps; round-by-round soundness goes
both ways along it, with the same counts.

A pair with bits between s and t (`Pair s t`): the two lists have the same length, and round by
round there are
  fill : a prover message of s as one of t;      strip : back, with strip (fill m) = m;
  zero : a verifier message of s as one of t;    old : back, with old (zero c) = c;
  pass : a test on the verifier messages of t, passed by every zero c, and passed by c' only if
         c' = zero (old c').
So the verifier messages of t that pass are those of s, one for one. These laws say no more than
that: HOW MANY further verifier messages t has is not part of a pair (that a round of t has 2^b
times the verifier messages of s's is `Emb.Bits`, E2E/ClimbEmb.lean, asked apart), and of t's prover
messages only that each is read back as one of s's. Proof of work (grinding) is the case in view: in
a round with b > 0 bits t's prover message is s's with a nonce, t's verifier message is s's with b
further bits, and pass says that the bits are 0 (Iop/Grind.lean). There the maps are nonce and bits
to the letter: `rpGrind` (E2E/ClimbPairGrind.lean), `rpZ` (E2E/ClimbChain.lean). The name "pair with
bits" is after that case. The list t need not be written as `Shape.grind` of s.

`ProtoPair P₀ P`: such a pair between the lists of rounds of two protocols, with
  P.accept x y τ' = (all rounds of τ' pass) && P₀.accept x y (strip τ')   at EVERY transcript τ'.
In words: P has further verifier messages, after each of which it rejects, and further content in
its prover messages, which it ignores; on the rest it decides as P₀.

The law (`ProtoPair.sound_iff`): P₀ is round-by-round sound with the counts ε if and only if P is,
for the same language, with the same counts. The way from P to P₀ is E2E/ClimbEmb.lean's; the way
from P₀ to P is the library's `Doomed.grind` (Iop/GrindProofs.lean) said along a pair: a verifier
message that fails the test dooms the prover for good, and those that pass are as many as s's.
(`Doomed.grind` proves the library's `InteractiveOracleProof.Sound.grind`, for which Iop/Grind.lean's head cites a
theorem of StarkWare's "ethSTARK Documentation".)

Main names:
  `RPair`, `Pair`; `Pair.toEmb`, `Pair.strip`, `Pair.passTr`, `Pair.down`.
  `Pair.strip_tr`, `Pair.pass_tr`: an image passes, and stripped it is the transcript.
  `Pair.err_down`, `Pair.down_err`: copying a list of counts there and back, both ways.
  `doomed_down`; `ProtoPair`, `ProtoPair.toEmb`, `ProtoPair.sound_down`, `ProtoPair.sound_iff`,
  `ProtoPair.sound_iff'`; `ProtoPair.accepts_iff`: P₀ accepts some transcript if and only if P does.
  `Pair.cons`, `Pair.app` and how `strip` and `passTr` go through them.

Limits. Acceptance alone: a pair ties the prover messages, the verifier messages and `accept`. It
ties nothing else: not the oracles' positions, alphabets and answers (`Pos`, `Sym`, `rd`), not
`reads`, `extReads`, `blinded`, not the cut of a prover message into oracle and plain part. By type
P may send in the clear what P₀ sends as an oracle. So nothing follows on queries, completeness or
zero knowledge. A count is a number of verifier messages: as a fraction it is larger in s
than in t. If ONE count of a list is at least the number of its round's verifier messages in s,
soundness with that list holds of every P₀, and so, by the equivalence, of every P that is some P₀
with the bits added (at most that many verifier messages of t's round pass).

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.


-/
import E2E.ClimbEmb
import Iop.Compose

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob

/-! ## 1. The pair -/

/-- One round. -/
structure RPair (r r' : Round) where
  fill : r.Msg → r'.Msg
  strip : r'.Msg → r.Msg
  zero : r.Chal → r'.Chal
  old : r'.Chal → r.Chal
  pass : r'.Chal → Bool
  strip_fill : ∀ m, strip (fill m) = m
  old_zero : ∀ c, old (zero c) = c
  pass_zero : ∀ c, pass (zero c) = true
  zero_old : ∀ c', pass c' = true → zero (old c') = c'

theorem RPair.zero_injective {r r' : Round} (u : RPair r r') : Function.Injective u.zero :=
  fun c d h => by
    have h' := congrArg u.old h
    rwa [u.old_zero, u.old_zero] at h'

/-- The verifier messages that pass are at most as many as their old parts. -/
theorem RPair.cnt_pass_le {r r' : Round} (u : RPair r r') (P : r.Chal → Prop) :
    cnt (fun c' : r'.Chal => u.pass c' = true ∧ P (u.old c')) ≤ cnt P :=
  Nat.card_le_card_of_injective
    (fun x : {c' : r'.Chal // u.pass c' = true ∧ P (u.old c')} =>
      (⟨u.old x.1, x.2.2⟩ : {c : r.Chal // P c}))
    (fun a b hab => Subtype.ext (by
      have h := congrArg (fun z : {c : r.Chal // P c} => u.zero z.1) hab
      have ha := u.zero_old a.1 a.2.1
      have hb := u.zero_old b.1 b.2.1
      exact ha.symm.trans (h.trans hb)))

/-- The round kept as it is: no bit. -/
def RPair.refl (r : Round) : RPair r r :=
  ⟨id, id, id, id, fun _ => true, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- A pair with bits between two lists of rounds. -/
def Pair : Iop.Shape → Iop.Shape → Type
  | [], [] => Unit
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty
  | r :: s, r' :: t => RPair r r' × Pair s t

/-- The embedding in it. -/
def Pair.toEmb : {s t : Iop.Shape} → Pair s t → Emb s t
  | [], [], _ => ()
  | [], _ :: _, p => Empty.elim p
  | _ :: _, [], p => Empty.elim p
  | _ :: _, _ :: _, (u, p) => (u.fill, ⟨u.zero, u.zero_injective⟩, Pair.toEmb p)

/-- A transcript of t, stripped. -/
def Pair.strip : {s t : Iop.Shape} → Pair s t → Tr t → Tr s
  | [], [], _, _ => ()
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (m, c, τ) => (u.strip m, u.old c, Pair.strip p τ)

/-- All verifier messages of a transcript of t pass. -/
def Pair.passTr : {s t : Iop.Shape} → Pair s t → Tr t → Bool
  | [], [], _, _ => true
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (_, c, τ) => u.pass c && Pair.passTr p τ

/-- A list of counts of s as a list of t: the same numbers. -/
def Pair.down : {s t : Iop.Shape} → Pair s t → Err s → Err t
  | [], [], _, _ => ()
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (_, p), (n, ε) => (n, Pair.down p ε)

theorem Pair.strip_tr : ∀ {s t : Iop.Shape} (p : Pair s t) (τ : Tr s), p.strip (p.toEmb.tr τ) = τ
  | [], [], _, () => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (m, c, τ) => by
      show (u.strip (u.fill m), u.old (u.zero c), p.strip (p.toEmb.tr τ)) = (m, c, τ)
      rw [u.strip_fill, u.old_zero, Pair.strip_tr p τ]

theorem Pair.pass_tr : ∀ {s t : Iop.Shape} (p : Pair s t) (τ : Tr s), p.passTr (p.toEmb.tr τ) = true
  | [], [], _, _ => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (u, p), (m, c, τ) => by
      show (u.pass (u.zero c) && p.passTr (p.toEmb.tr τ)) = true
      rw [u.pass_zero, Pair.pass_tr p τ, Bool.and_true]

theorem Pair.err_down : ∀ {s t : Iop.Shape} (p : Pair s t) (ε : Err s), p.toEmb.err (p.down ε) = ε
  | [], [], _, () => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (_, p), (n, ε) => congrArg (Prod.mk n) (Pair.err_down p ε)

theorem Pair.down_err : ∀ {s t : Iop.Shape} (p : Pair s t) (ε : Err t), p.down (p.toEmb.err ε) = ε
  | [], [], _, () => rfl
  | [], _ :: _, p, _ => Empty.elim p
  | _ :: _, [], p, _ => Empty.elim p
  | _ :: _, _ :: _, (_, p), (n, ε) => congrArg (Prod.mk n) (Pair.down_err p ε)

/-! ## 2. The law from s to t -/

/-- **The law for `Doomed`, from s to t.** If the prover of s is doomed towards `bad`, the prover of
t is doomed, with the same counts, towards every goal that holds where a verifier message fails the
test and where `bad` holds of the stripped transcript. -/
theorem doomed_down :
    ∀ {s t : Iop.Shape} (p : Pair s t) (ε : Err s) {bad : Tr s → Prop} {bad' : Tr t → Prop},
      (∀ τ' : Tr t, p.passTr τ' = false ∨ bad (p.strip τ') → bad' τ') →
      Doomed s ε bad → Doomed t (p.down ε) bad'
  | [], [], _, _, _, _, h, hd => h () (Or.inr hd)
  | [], _ :: _, p, _, _, _, _, _ => Empty.elim p
  | _ :: _, [], p, _, _, _, _, _ => Empty.elim p
  | r :: s, r' :: t, (u, p), (_, ε), bad, bad', h, hd => fun m' => by
      refine le_trans
        (cnt_mono (Q := fun c' : r'.Chal =>
              u.pass c' = true ∧ ¬ Doomed s ε (fun τ => bad (u.strip m', u.old c', τ)))
          fun c' hc => ?_)
        ((u.cnt_pass_le _).trans (hd (u.strip m')))
      by_cases hp : u.pass c' = true
      · refine ⟨hp, fun hd' => hc (doomed_down p ε (fun τ' hτ => h (m', c', τ') ?_) hd')⟩
        rcases hτ with hτ | hτ
        · left
          show (u.pass c' && p.passTr τ') = false
          rw [hτ, Bool.and_false]
        · exact Or.inr hτ
      · refine absurd (Doomed.of_forall _ _ fun τ' => h (m', c', τ') (Or.inl ?_)) hc
        show (u.pass c' && p.passTr τ') = false
        rw [(Bool.not_eq_true _).mp hp, Bool.false_and]

variable {X : Type} {E : ExtSpec}

/-- A pair with bits between the lists of rounds of P₀ and P, and P accepts a transcript exactly if
all its verifier messages pass and P₀ accepts the stripped transcript. -/
structure ProtoPair (P₀ P : InteractiveOracleProof X E) where
  pair : Pair P₀.shape P.shape
  acc : ∀ (x : X) (y : E.Str) (τ' : Tr P.shape),
    P.accept x y τ' = (pair.passTr τ' && P₀.accept x y (pair.strip τ'))

/-- The embedding of P₀ in P. -/
def ProtoPair.toEmb {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P) : ProtoEmb P₀ P :=
  ⟨S.pair.toEmb, fun x y τ => by
    rw [S.acc, S.pair.pass_tr, S.pair.strip_tr, Bool.true_and]⟩

/-- From P₀ to P. -/
theorem ProtoPair.sound_down {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P) {L : X → E.Str → Prop}
    {ε : Err P₀.shape} (h : P₀.Sound L ε) : P.Sound L (S.pair.down ε) :=
  fun x y hxy => doomed_down S.pair ε (fun τ' hτ => by
    rw [S.acc]
    rcases hτ with hτ | hτ
    · rw [hτ, Bool.false_and]
    · rw [hτ, Bool.and_false]) (h x y hxy)

/-- **Both ways, from a list of P₀**: P₀ is round-by-round sound with the counts ε if and only if P
is, for the same language, with the same counts. -/
theorem ProtoPair.sound_iff {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P) (L : X → E.Str → Prop)
    (ε : Err P₀.shape) : P₀.Sound L ε ↔ P.Sound L (S.pair.down ε) :=
  ⟨S.sound_down, fun h =>
    (congrArg (P₀.Sound L) (S.pair.err_down ε)).mp (S.toEmb.sound h)⟩

/-- **Both ways, from a list of P.** -/
theorem ProtoPair.sound_iff' {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P) (L : X → E.Str → Prop)
    (ε : Err P.shape) : P.Sound L ε ↔ P₀.Sound L (S.pair.toEmb.err ε) :=
  ⟨S.toEmb.sound, fun h => (congrArg (P.Sound L) (S.pair.down_err ε)).mp (S.sound_down h)⟩

/-- P₀ accepts some transcript at (x, y) if and only if P does. -/
theorem ProtoPair.accepts_iff {P₀ P : InteractiveOracleProof X E} (S : ProtoPair P₀ P) (x : X) (y : E.Str) :
    (∃ τ, P₀.accept x y τ = true) ↔ ∃ τ', P.accept x y τ' = true :=
  ⟨fun h => h.elim fun τ hτ => ⟨S.pair.toEmb.tr τ, (S.toEmb.acc x y τ).trans hτ⟩,
    fun h => h.elim fun τ' hτ => ⟨S.pair.strip τ', by
      rw [S.acc, Bool.and_eq_true] at hτ
      exact hτ.2⟩⟩

/-! ## 3. Putting pairs together -/

/-- One more round in front, kept as it is. -/
def Pair.cons (r : Round) {s t : Iop.Shape} (p : Pair s t) : Pair (r :: s) (r :: t) :=
  (RPair.refl r, p)

/-- Two pairs in a row. -/
def Pair.app : {s t s' t' : Iop.Shape} → Pair s t → Pair s' t' → Pair (s ++ s') (t ++ t')
  | [], [], _, _, _, p' => p'
  | [], _ :: _, _, _, p, _ => Empty.elim p
  | _ :: _, [], _, _, p, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (u, p), p' => (u, Pair.app p p')

theorem Pair.cons_strip_1 (r : Round) {s t : Iop.Shape} (p : Pair s t) (σ : Tr (r :: t)) :
    ((Pair.cons r p).strip σ).1 = σ.1 := by
  obtain ⟨m, c, σ⟩ := σ
  rfl

theorem Pair.cons_strip_22 (r : Round) {s t : Iop.Shape} (p : Pair s t) (σ : Tr (r :: t)) :
    ((Pair.cons r p).strip σ).2.2 = p.strip σ.2.2 := by
  obtain ⟨m, c, σ⟩ := σ
  rfl

theorem Pair.cons_pass (r : Round) {s t : Iop.Shape} (p : Pair s t) (σ : Tr (r :: t)) :
    (Pair.cons r p).passTr σ = p.passTr σ.2.2 := by
  obtain ⟨m, c, σ⟩ := σ
  rfl

theorem Pair.fst_strip :
    ∀ {s t s' t' : Iop.Shape} (p : Pair s t) (p' : Pair s' t') (τ : Tr (t ++ t')),
      Tr.fst ((Pair.app p p').strip τ) = p.strip (Tr.fst τ)
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, p, _, _ => Empty.elim p
  | _ :: _, [], _, _, p, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (u, p), p', (m, c, τ) =>
    congrArg (fun v => (u.strip m, u.old c, v)) (Pair.fst_strip p p' τ)

theorem Pair.snd_strip :
    ∀ {s t s' t' : Iop.Shape} (p : Pair s t) (p' : Pair s' t') (τ : Tr (t ++ t')),
      Tr.snd (s := s) ((Pair.app p p').strip τ) = p'.strip (Tr.snd (s := t) τ)
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, p, _, _ => Empty.elim p
  | _ :: _, [], _, _, p, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (_, p), p', (_, _, τ) => Pair.snd_strip p p' τ

theorem Pair.app_pass :
    ∀ {s t s' t' : Iop.Shape} (p : Pair s t) (p' : Pair s' t') (τ : Tr (t ++ t')),
      (Pair.app p p').passTr τ = (p.passTr (Tr.fst τ) && p'.passTr (Tr.snd (s := t) τ))
  | [], [], _, _, _, _, _ => (Bool.true_and _).symm
  | [], _ :: _, _, _, p, _, _ => Empty.elim p
  | _ :: _, [], _, _, p, _, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (u, p), p', (_, c, τ) => by
      show (u.pass c && (Pair.app p p').passTr τ) =
        ((u.pass c && p.passTr (Tr.fst τ)) && p'.passTr (Tr.snd τ))
      rw [Pair.app_pass p p' τ, Bool.and_assoc]

theorem Pair.toEmb_cons (r : Round) {s t : Iop.Shape} (p : Pair s t) :
    (Pair.cons r p).toEmb = ((id, ⟨id, Function.injective_id⟩, p.toEmb) : Emb (r :: s) (r :: t)) :=
  rfl

theorem Pair.toEmb_app :
    ∀ {s t s' t' : Iop.Shape} (p : Pair s t) (p' : Pair s' t'),
      (Pair.app p p').toEmb = Emb.app p.toEmb p'.toEmb
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, p, _ => Empty.elim p
  | _ :: _, [], _, _, p, _ => Empty.elim p
  | _ :: _, _ :: _, _, _, (u, p), p' => by
      show (u.fill, _, (Pair.app p p').toEmb) = (u.fill, _, Emb.app p.toEmb p'.toEmb)
      rw [Pair.toEmb_app p p']

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.doomed_down
#print axioms AtPublicFiles.Climb.ProtoPair.sound_iff
#print axioms AtPublicFiles.Climb.ProtoPair.sound_iff'
#print axioms AtPublicFiles.Climb.ProtoPair.accepts_iff
