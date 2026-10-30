-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnCoin.lean: THE COEFFICIENT DRAWN IN THE SUMCHECK OF THE TERMS, AS THE CHAIN READS
IT OFF ITS LAST STATEMENT, IS NOT 0 WHERE K4's HEARING RETURNS. Statements and proofs.

K4's text refuses where the three words of that coefficient are 0 (`hearTerms`). The chain's end
asks that its READING is not 0 (`LayVO.epsOK`, Cb/Pv/Lay/OwnTest.lean). The two meet where the words
are below the prime.

  `gl_ne_of_word`: a word triple below the prime that is not three zeros does not read 0.
  `SmallTape t`: every word that a round of the tape drew is below the prime. `SmallTape.drop`,
    `small_eps`, `small_paired`: it goes over to what is left of a tape; the first word that the
    tape's first round drew is below the prime; the tape of a view's rounds has it if all drawn
    elements of these rounds have.
  `k4_coin`: under `SmallTape t0`, the terms' call on its named tape (`own_calls6`, OwnRecs.lean),
    `isZeroE tT.p.eps = false` and `TailH.Claims`: `(T.ch4.back ((k4Tail W P hp t0 nz a).z7
    x)).2.eps ≠ 0`.

NO NEW ARGUMENT: `eps3_z7` (OnBytes/Desc/First/P1/TailBack.lean), `tscIn_heard` (P1/Heard.lean),
`OnBytes.Slice.isZeroE_iff`.

Limits. `SmallTape` and `TailH.Claims` are premises. One direction. Nothing on soundness.

-/
import Johnson.Road.K4.OwnJoint
import OnBytes.Desc.First.P1.TailBack
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att
open OnBytes OnBytes.K.Kc OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Tsc)
open OnBytes.Model.Layer (Pub HPlan2)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR tapeEps tscIn_heard eps3_z7)

variable {M X : Type}

theorem gl_ne_of_word {w : E} (hk : okE w = true) (hz : isZeroE w = false) : gl.val w ≠ 0 := by
  intro h0
  have h1 : isZeroE w = true := (isZeroE_iff w hk).2 h0
  rw [hz] at h1
  exact Bool.noConfusion h1

/-- Every word that a round of the tape drew is below the prime. -/
def SmallTape (t : Tape) : Prop := ∀ r ∈ t, ∀ w ∈ r.drawn, okE w = true

theorem SmallTape.drop {t : Tape} (h : SmallTape t) (a : ℕ) : SmallTape (t.drop a) :=
  fun r hr => h r (List.mem_of_mem_drop hr)

theorem small_eps {t : Tape} (h : SmallTape t) : okE (tapeEps t) = true := by
  cases t with
  | nil => rfl
  | cons r u =>
    show okE (r.drawn.headD zeroE) = true
    cases hd : r.drawn with
    | nil => rfl
    | cons w l => exact h r List.mem_cons_self w (by rw [hd]; exact List.mem_cons_self)

theorem small_paired : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    (∀ r ∈ rs, ∀ x ∈ r.drawn.elems, okE (E.ofTriple x) = true) → SmallTape (paired rs es)
  | [], _, _ => fun _ hr => absurd hr List.not_mem_nil
  | r :: rs, [], h => fun q hq w hw => by
    rcases List.mem_cons.1 hq with rfl | hq
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      exact h r List.mem_cons_self x hx
    · exact small_paired rs [] (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) q hq w hw
  | r :: rs, e :: es, h => fun q hq w hw => by
    rcases List.mem_cons.1 hq with rfl | hq
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      exact h r List.mem_cons_self x hx
    · exact small_paired rs es (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) q hq w hw

/-- **The coefficient of the terms' sumcheck, as the chain reads it, is not 0.** -/
theorem k4_coin {T : LayTail GE M X} {R : TailR} (W : TailM T R) {P : Pub} {hp : HPlan2}
    {t0 v : Tape} (hs : SmallTape t0) {Z : Array E} {n : ℕ} {F G : Fork} {tT : Tsc}
    (c3 : Fl.tscIn Z P.y.h.lt n 1 F
      ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) = some (tT, G, v))
    (hz : isZeroE tT.p.eps = false) (nz : NzT T (ksOf P hp) (t0.drop 1)) (a : Adds7 T) (x : X)
    (hc : (k4Tail W P hp t0 nz a).Claims x) :
    (T.ch4.back ((k4Tail W P hp t0 nz a).z7 x)).2.eps ≠ 0 := by
  rw [eps3_z7 gl T _ x hc]
  have e : tT.p.eps = tapeEps ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) :=
    (tscIn_heard c3).2.2.2.2.2.2.2.2.1
  have hsm : SmallTape ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3)) :=
    ((((((hs.drop 1).drop 1).drop 1).drop _).drop 1).drop 1).drop _
  show gl.val (tapeEps ((((ksOf P hp).tcP (t0.drop 1)).drop 1).drop (P.y.h.lt + 3))) ≠ 0
  rw [e] at hz
  exact gl_ne_of_word (small_eps hsm) hz

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gl_ne_of_word
#print axioms OnBytes.Road.K4.small_paired
#print axioms OnBytes.Road.K4.k4_coin
