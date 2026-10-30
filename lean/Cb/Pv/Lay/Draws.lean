-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Draws.lean: the rounds of a layers' sub-proof that open a sumcheck: several claims are
combined into one under drawn coefficients, with or without scalars sent in the same round.

A sumcheck of the sub-proof starts from one claim. Where several claims are open, the verifier first
draws coefficients: the powers of one element, or the equality weights of a point. In some of these
rounds the prover's message is empty. In others it holds scalars: values that the prover sends
masked, each under a mask entry of its own. Such a scalar splits an identity between two forms in
the entries, lhs i = rhs i, into two claims under one new name: lhs i + mask i = sent i, which goes
into the combination, and sent i - mask i = rhs i, which rides on.

Main names:
  `comb`, `comb_knowAt`: a round with an empty message. From "what rides, and val i = tg i for all
    i" to "what rides, and the combination of the val i is the combination of the tg i", for any
    zero-evader of the library (Cb/Gen/BatEvader.lean). The error is the evader's.
  `sendRound`, `send`: a round in which scalars with indices in a type ι are sent and then an
    element of D is drawn.
  `send_knowAt`: its knowledge soundness, at letters: from Φ to Θ, if for every tuple of entries of
    which Φ is false and every message at most err draws make Θ true.
The round at the value described above stands where it is used: Cb/Pv/Lay/Squares.lean.

Limits: nothing is said on the honest prover, on completeness or on zero knowledge. The errors are
counts of bad draws, out of the set that is drawn from: the evader's seeds; D. In `send_knowAt` the
bound on the bad draws is a premise: whoever uses the round pays it.

-/
import Cb.G6.Join
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

variable {E : Type} [Field E]

/-! ### A round with an empty message -/

section Comb
variable {J I St : Type} [Fintype I] {Ex : ExtSpec} {M Wp Kc : Type}
  (ev : Evader E I) (A0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
  (val : St → (J → E) → I → E) (tg : St → I → E)

/-- all claims -/
@[reducible] def combIn : Rels Kc St Ex (M × Wp) :=
  ⟨fun st y w => A0.rel st y w ∧ ∀ i, val st (msg w.1) i = tg st i,
    fun a w => A0.relR a w ∧ ∀ i, val a.1 (msg w.1) i = tg a.1 i, A0.on, A0.core⟩

/-- the combined claim -/
@[reducible] def combOut : Rels Kc (St × ev.D) Ex (M × Wp) :=
  ⟨fun x y w => A0.rel x.1 y w ∧ ∑ i, ev.ze x.2 i * val x.1 (msg w.1) i =
      ∑ i, ev.ze x.2 i * tg x.1 i,
    fun a w => A0.relR (a.1.1, a.2) w ∧
      ∑ i, ev.ze a.1.2 i * val a.1.1 (msg w.1) i = ∑ i, ev.ze a.1.2 i * tg a.1.1 i,
    fun a => A0.on (a.1.1, a.2), A0.core⟩

/-- the round -/
def comb (St : Type) (Ex : ExtSpec) : IOR St Ex (St × ev.D) Ex := IOR.draw ev.D
    (fun st β => (st, β)) Ex

theorem comb_knowAt (hev : ev.OK) :
    KnowAt (comb ev St Ex) (combIn A0 msg val tg) (combOut ev A0 msg val tg) (fun _ _ _ wp => wp)
      (Nums.draw Kc ev.D (fun (st : St) β => (st, β)) Ex ev.err).err :=
  knowAt_draw _ _ _ ev.err (fun _ _ _ h => h) fun st y m _ => by
    classical
    by_cases hA : ∀ i, val st (msg m) i = tg st i
    · exact le_trans (le_of_eq (cnt_false fun β h => by
        obtain ⟨wp, h1, h2⟩ := h
        exact h2 ⟨h1.1, hA⟩)) (Nat.zero_le _)
    · refine le_trans (cnt_mono fun β h => ?_)
        (hev (fun i => val st (msg m) i - tg st i) fun h0 => hA
            fun i => sub_eq_zero.1 (congrFun h0 i))
      obtain ⟨wp, h1, -⟩ := h
      have h2 : ∑ i, ev.ze β i * val st (msg m) i = ∑ i, ev.ze β i * tg st i := h1.2
      simp only [mul_sub, sum_sub_distrib]
      rw [h2, sub_self]

omit [Field E] [Fintype I] in
theorem comb_errs :
    TWhole.errList (Nums.draw Kc ev.D (fun (st : St) β => (st, β)) Ex ev.err).err = [ev.err] := rfl

end Comb

/-! ### A round with scalars -/

section Send
variable (E) (ι : Type) (D : Type) [Fintype D] [Nonempty D]

/-- scalars with indices in ι, in the clear; then a draw from D -/
@[reducible] def sendRound : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim, Plain := ι → E,
    Chal := D, dOrc := (), dPlain := 0 }

def sendRound_point : (sendRound E ι D).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

variable {E ι D}

def sent (τ : Tr [sendRound E ι D]) : ι → E := τ.1.2
def drawnS (τ : Tr [sendRound E ι D]) : D := τ.2.1

variable (E ι D) (X : Type) (Ex : ExtSpec)

/-- The reduction: it puts out ((the statement, the sent scalars), the draw) and rejects nothing. -/
def send : IOR X Ex ((X × (ι → E)) × D) Ex where
  shape := [sendRound E ι D]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ τ => some ((x, sent τ), drawnS τ)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

variable {E ι D X Ex} {Kc J M Wp : Type} (A0 : Rels Kc X Ex (M × Wp)) (msg : M → J → E)

@[reducible] def sendIn (Φ : X → (J → E) → Prop) : Rels Kc X Ex (M × Wp) :=
  ⟨fun x y w => A0.rel x y w ∧ Φ x (msg w.1), fun a w => A0.relR a w ∧ Φ a.1
      (msg w.1), A0.on, A0.core⟩

@[reducible] def sendOut (Θ : (X × (ι → E)) × D → (J → E) → Prop) :
    Rels Kc ((X × (ι → E)) × D) Ex (M × Wp) :=
  ⟨fun b y w => A0.rel b.1.1 y w ∧ Θ b (msg w.1), fun a w => A0.relR (a.1.1.1, a.2) w
      ∧ Θ a.1 (msg w.1),
    fun a => A0.on (a.1.1.1, a.2), A0.core⟩

theorem send_knowAt (Φ : X → (J → E) → Prop) (Θ : (X × (ι → E)) × D → (J → E) → Prop) (err : ℕ)
    (hb : ∀ x m, ¬ Φ x m → ∀ s, cnt (fun β => Θ ((x, s), β) m) ≤ err) :
    KnowAt (send E ι D X Ex) (sendIn A0 msg Φ) (sendOut A0 msg Θ) (fun _ _ _ wp => wp)
      ((err, ()) : ℕ × Unit) where
  point := ⟨(sendRound_point E ι D, ())⟩
  isLocal :=
    { out := fun x y y' τ τ' h1 h2 _ _ => by
        have e1 : sent τ = sent τ' := congrArg (fun p : Plains [sendRound E ι D] => (show (ι → E) ×
            Unit from p).1) h2
        have e2 : drawnS τ = drawnS τ' := congrArg (fun r : Rho [sendRound E ι D] =>
            (show D × Unit from r).1) h1
        show some ((x, sent τ), drawnS τ) = some ((x, sent τ'), drawnS τ')
        rw [e1, e2]
      imp := fun y y' _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
  onOut := fun a τ b hA hb' => by
    obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
    have e : b = (((a.1, sent τ), drawnS τ), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact hA
  know := fun m a _ mm => by
    classical
    by_cases hΦ : Φ a.1 (msg m)
    · refine le_trans (le_of_eq (cnt_false fun β hβ => hβ fun b wp hb' hB => ?_)) (Nat.zero_le _)
      obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
      have e : b = (((a.1, mm.2), β), a.2) := Prod.ext (Option.some.inj h1).symm h2
      rw [e] at hB
      exact ⟨hB.1, hΦ⟩
    · refine le_trans (cnt_mono fun β hβ => ?_) (hb a.1 (msg m) hΦ mm.2)
      by_contra hn
      refine hβ fun b wp hb' hB => ?_
      obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
      have e : b = (((a.1, mm.2), β), a.2) := Prod.ext (Option.some.inj h1).symm h2
      rw [e] at hB
      exact absurd hB.2 hn

end Send

end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.comb_knowAt
#print axioms Cb.Pv.Lay.send_knowAt
