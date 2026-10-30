-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbEmb.lean: a list of rounds embedded in another, and round-by-round soundness along it.

An embedding of s in t (`Emb s t`): the two lists have the same length, and round by round there
is a map of prover messages and a one-to-one map of verifier messages. So s is t with fewer verifier
messages, and every prover message of s is read as one of t.

The law (`doomed_of_emb`, `ProtoEmb.sound`): if the larger protocol is round-by-round sound with
the counts ε, and the smaller verifier decides on a transcript as the larger one does on its image,
then the smaller protocol is round-by-round sound with THE SAME COUNTS. A count is the list's number
for a round: a bound on how many of the round's verifier messages lead out of a doomed state. As a
fraction of the round's verifier messages it grows by the factor
(messages of the larger round) / (messages of the smaller round).

Why. Proof of work is modelled as further bits of a verifier message that must all be 0
(Iop/Grind.lean, whose head cites StarkWare's "ethSTARK Documentation" for the construction, with
the place in it). The protocol without proof of work is embedded in the one with it (bits 0, a
fixed nonce). The library's law `InteractiveOracleProof.Sound.grind` goes from no proof of work to proof of work;
this file has the way back, for every pair of protocols so related, whether or not the larger one is
written as `InteractiveOracleProof.grind` of the smaller.

Main names:
  `Emb s t`, `Emb.tr`, `Emb.err`: the embedding; a transcript's image; the list of counts, copied.
  `Emb.app`, `Emb.refl`: two lists in a row; a list in itself.
  `cnt_le_of_injective`: a count along a one-to-one map.
  `doomed_of_emb`: the law for `Doomed`.
  `ProtoEmb P₀ P`, `ProtoEmb.sound`: the law for `InteractiveOracleProof.Sound`.
  `Emb.Bits e g`: round by round the larger round has 2^b times the verifier messages of the
    smaller, b the round's number in g.
  `below_iff_belowG`: under `Emb.Bits e g`, "every count of ε is at most c as a fraction of the
    larger round" says the same as "every count is at most c * 2^b as a fraction of the smaller".
  `below_of_allLe`: if every b is at most w, the fractions of the smaller rounds are at most
    c * 2^w.

Limits. Soundness alone: nothing on an honest prover, on reads, on hiding.
One way alone: from P to P₀. `ProtoEmb` does not ask that P reject off the image, and every P has a
`ProtoEmb` from the protocol that decides as P does on images. That P₀ is "P without proof of work"
is read off P₀'s definition, or said by E2E/ClimbPair.lean's `ProtoPair`, which goes both ways.
If ONE count of a list is as large as its round, soundness with that list holds of every protocol. A
count e with |C| ≤ e < |C'| (C, C' the round's verifier messages in s and t) may have content in t
and has none in s. Under `Emb.Bits e g` a bound c on t's fractions leaves content in s where
c * 2^b < 1 in every round.

What "without proof of work" means at the IOP as written in Lean is a reading of this folder's
writers and an open question: E2E/ClimbFiles.lean's head.



-/
import Iop.Grind
import Iop.GBitsLe

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open scoped ENNReal

/-! ## 1. The embedding -/

/-- An embedding of the list of rounds s in the list t: round by round a map of prover messages and
a one-to-one map of verifier messages. Lists of different lengths have none. -/
def Emb : Iop.Shape → Iop.Shape → Type
  | [], [] => Unit
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty
  | r :: s, r' :: t =>
    (r.Msg → r'.Msg) × {f : r.Chal → r'.Chal // Function.Injective f} × Emb s t

/-- The image of a full transcript. -/
def Emb.tr : {s t : Iop.Shape} → Emb s t → Tr s → Tr t
  | [], [], _, _ => ()
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | _ :: _, _ :: _, (f, c, e), (m, x, τ) => (f m, c.1 x, Emb.tr e τ)

/-- The list of counts of the larger list of rounds, as a list of the smaller: the same numbers. -/
def Emb.err : {s t : Iop.Shape} → Emb s t → Err t → Err s
  | [], [], _, _ => ()
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | _ :: _, _ :: _, (_, _, e), (n, ε) => (n, Emb.err e ε)

/-- A list of rounds in itself. -/
def Emb.refl : (s : Iop.Shape) → Emb s s
  | [] => ()
  | _ :: s => (id, ⟨id, Function.injective_id⟩, Emb.refl s)

/-- Two embeddings in a row. -/
def Emb.app : {s t s' t' : Iop.Shape} → Emb s t → Emb s' t' → Emb (s ++ s') (t ++ t')
  | [], [], _, _, _, e' => e'
  | [], _ :: _, _, _, e, _ => Empty.elim e
  | _ :: _, [], _, _, e, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (f, c, e), e' => (f, c, Emb.app e e')

theorem Emb.tr_refl : ∀ (s : Iop.Shape) (τ : Tr s), (Emb.refl s).tr τ = τ
  | [], () => rfl
  | _ :: s, (m, x, τ) => congrArg (fun u => (m, x, u)) (Emb.tr_refl s τ)

theorem Emb.err_refl : ∀ (s : Iop.Shape) (ε : Err s), (Emb.refl s).err ε = ε
  | [], () => rfl
  | _ :: s, (n, ε) => congrArg (Prod.mk n) (Emb.err_refl s ε)

/-- The image of two transcripts in a row. -/
theorem Emb.tr_app :
    ∀ {s t s' t' : Iop.Shape} (e : Emb s t) (e' : Emb s' t') (a : Tr s) (b : Tr s'),
      (Emb.app e e').tr (Tr.app a b) = Tr.app (e.tr a) (e'.tr b)
  | [], [], _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, e, _, _, _ => Empty.elim e
  | _ :: _, [], _, _, e, _, _, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (f, c, e), e', (m, x, a), b =>
    congrArg (fun u => (f m, c.1 x, u)) (Emb.tr_app e e' a b)

/-- The first part of an image is the image of the first part. -/
theorem Emb.fst_tr :
    ∀ {s t s' t' : Iop.Shape} (e : Emb s t) (e' : Emb s' t') (τ : Tr (s ++ s')),
      Tr.fst ((Emb.app e e').tr τ) = e.tr (Tr.fst τ)
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, e, _, _ => Empty.elim e
  | _ :: _, [], _, _, e, _, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (f, c, e), e', (m, x, τ) =>
    congrArg (fun u => (f m, c.1 x, u)) (Emb.fst_tr e e' τ)

/-- The second part of an image is the image of the second part. -/
theorem Emb.snd_tr :
    ∀ {s t s' t' : Iop.Shape} (e : Emb s t) (e' : Emb s' t') (τ : Tr (s ++ s')),
      Tr.snd (s := t) ((Emb.app e e').tr τ) = e'.tr (Tr.snd (s := s) τ)
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, e, _, _ => Empty.elim e
  | _ :: _, [], _, _, e, _, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (_, _, e), e', (_, _, τ) => Emb.snd_tr e e' τ

/-! ## 2. The law -/

/-- Along a one-to-one map a count does not fall. -/
theorem cnt_le_of_injective {α β : Type} [Finite α] [Finite β] (f : α → β)
    (hf : Function.Injective f) {P : α → Prop} {Q : β → Prop} (h : ∀ a, P a → Q (f a)) :
    cnt P ≤ cnt Q :=
  Nat.card_le_card_of_injective (fun x : {a // P a} => (⟨f x.1, h x.1 x.2⟩ : {b // Q b}))
    (fun _ _ hab => Subtype.ext (hf (congrArg (fun y : {b // Q b} => y.1) hab)))

/-- **The law for `Doomed`.** If the prover of the larger list of rounds is doomed towards `bad'`
with the counts ε, the prover of the smaller list is doomed, with the same counts, towards every
goal that holds of a transcript whose image is in `bad'`. In a round: to a prover message take its
image; the verifier messages after which the smaller prover is not doomed go one-to-one to verifier
messages after which the larger prover is not doomed. -/
theorem doomed_of_emb :
    ∀ {s t : Iop.Shape} (e : Emb s t) (ε : Err t) {bad : Tr s → Prop} {bad' : Tr t → Prop},
      (∀ τ : Tr s, bad' (e.tr τ) → bad τ) → Doomed t ε bad' → Doomed s (e.err ε) bad
  | [], [], _, _, _, _, h, hd => h () hd
  | [], _ :: _, e, _, _, _, _, _ => Empty.elim e
  | _ :: _, [], e, _, _, _, _, _ => Empty.elim e
  | r :: s, r' :: t, (f, c, e), (_, ε), bad, bad', h, hd => fun m =>
    le_trans
      (cnt_le_of_injective (α := r.Chal) (β := r'.Chal) c.1 c.2
        (P := fun x : r.Chal => ¬ Doomed s (e.err ε) (fun τ => bad (m, x, τ)))
        (Q := fun x' : r'.Chal => ¬ Doomed t ε (fun τ' => bad' (f m, x', τ')))
        (fun x hx hd' => hx (doomed_of_emb e ε (fun τ hτ => h (m, x, τ) hτ) hd')))
      (hd (f m))

variable {X : Type} {E : ExtSpec}

/-- The protocol P₀ embedded in the protocol P: an embedding of the lists of rounds along which the
two verifiers decide alike. Reads and the marks of blinded oracles are not compared: soundness does
not read them. -/
structure ProtoEmb (P₀ P : InteractiveOracleProof X E) where
  emb : Emb P₀.shape P.shape
  acc : ∀ (x : X) (y : E.Str) (τ : Tr P₀.shape), P.accept x y (emb.tr τ) = P₀.accept x y τ

/-- **The law for round-by-round soundness**: the same language, the same counts. -/
theorem ProtoEmb.sound {P₀ P : InteractiveOracleProof X E} (S : ProtoEmb P₀ P) {L : X → E.Str → Prop}
    {ε : Err P.shape} (h : P.Sound L ε) : P₀.Sound L (S.emb.err ε) :=
  fun x y hxy => doomed_of_emb S.emb ε (fun τ hτ => (S.acc x y τ).symm.trans hτ) (h x y hxy)

/-- A protocol in itself. With it `ProtoEmb.sound` gives back its premise (`Emb.err_refl`). -/
def ProtoEmb.refl (P : InteractiveOracleProof X E) : ProtoEmb P P :=
  ⟨Emb.refl P.shape, fun x y τ => congrArg (P.accept x y) (Emb.tr_refl P.shape τ)⟩

/-! ## 3. Counts as fractions -/

/-- Round by round the larger round has 2^b times as many verifier messages as the smaller, b the
round's number in the list g. -/
def Emb.Bits : {s t : Iop.Shape} → Emb s t → GBits s → Prop
  | [], [], _, _ => True
  | [], _ :: _, e, _ => Empty.elim e
  | _ :: _, [], e, _ => Empty.elim e
  | r :: _, r' :: _, (_, _, e), (b, g) =>
    Fintype.card r'.Chal = Fintype.card r.Chal * 2 ^ b ∧ Emb.Bits e g

theorem Emb.Bits.app :
    ∀ {s t s' t' : Iop.Shape} {e : Emb s t} {e' : Emb s' t'} {g : GBits s} {g' : GBits s'},
      e.Bits g → e'.Bits g' → (Emb.app e e').Bits (GBits.app g g')
  | [], [], _, _, _, _, _, _, _, h' => h'
  | [], _ :: _, _, _, e, _, _, _, _, _ => Empty.elim e
  | _ :: _, [], _, _, e, _, _, _, _, _ => Empty.elim e
  | _ :: _, _ :: _, _, _, (_, _, _), _, (_, _), _, h, h' => ⟨h.1, Emb.Bits.app h.2 h'⟩

/-- **The bound, both ways.** Every count of ε is at most c times the number of verifier messages of
its larger round, if and only if it is at most c * 2^b times that of its smaller round. -/
theorem below_iff_belowG :
    ∀ {s t : Iop.Shape} (e : Emb s t) (g : GBits s) (ε : Err t) (c : ℝ≥0∞),
      e.Bits g → (Err.Below ε c ↔ Err.BelowG g (e.err ε) c)
  | [], [], _, _, _, _, _ => Iff.rfl
  | [], _ :: _, e, _, _, _, _ => Empty.elim e
  | _ :: _, [], e, _, _, _, _ => Empty.elim e
  | r :: _, r' :: _, (_, _, e), (b, g), (n, ε), c, h => by
      show ((n : ℝ≥0∞) ≤ c * (Fintype.card r'.Chal : ℝ≥0∞) ∧ Err.Below ε c) ↔
        ((n : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) ∧
          Err.BelowG g (e.err ε) c)
      rw [h.1, below_iff_belowG e g ε c h.2, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        mul_comm (Fintype.card r.Chal : ℝ≥0∞)]

/-- Where every round has at most w bits, a list that is below c with the bits counted is below
c * 2^w without them. -/
theorem below_of_allLe :
    ∀ {s : Iop.Shape} (g : GBits s) (ε : Err s) (c : ℝ≥0∞) (w : ℕ),
      g.AllLe w → Err.BelowG g ε c → Err.Below ε (c * 2 ^ w)
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, (_, g), (_, ε), c, w, hA, hB =>
    ⟨hB.1.trans (by
      rw [← mul_assoc]
      exact mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_right₀ one_le_two hA.1)) le_rfl),
      below_of_allLe g ε c w hA.2 hB.2⟩

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.doomed_of_emb
#print axioms AtPublicFiles.Climb.ProtoEmb.sound
#print axioms AtPublicFiles.Climb.below_iff_belowG
#print axioms AtPublicFiles.Climb.below_of_allLe
