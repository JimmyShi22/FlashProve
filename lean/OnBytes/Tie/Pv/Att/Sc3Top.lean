-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/Sc3Top.lean: the port's routines for a sumcheck of products, where they succeed,
have heard a transcript of the typed block, and their record is the block's output on that
transcript, read.

sc3In receives the messages of a sumcheck of products, and sc3Row makes its row from the weights
that the caller has computed at the point of the challenges (OnBytes/Model/AttentionSums.lean).
Neither routine nor the typed block of Cb/Pv/Att/Sc3.lean tests a value received or drawn, so the
tie between them is an equality of outputs.

Main names:
  `sc3Num`: the number of an end value: A_b has 2 b, B_b has 2 b + 1. `sc3Vals`: the end values,
    read, under their names.
  `sc3Row_ok`: sc3Row leaves the context as it was; there is one weight for each pair of maps; its
    row is the record's row form at `sc3Flat` on what the state shows under the slots from sEnd on;
    it puts the coefficients of the hiding polynomial under their slots.
  `sc3_block_out`: the typed block's verifier, on the transcript that is made from what the port has
    heard, with n further scalars in its first message, puts out `plainOut`
    (OnBytes/Tie/Pv/Att/Tr.lean).
  `sc3_tie`: if sc3In succeeds from a state whose arrays on slots have their length, and sc3Row
    succeeds right behind it, then for every reading, all parameters T with these numbers of
    variables and of pairs, and every state st: the rounds heard are those of the block's listener
    (`Parts`, from the context behind the further scalars); the record's start, target, first slot
    and sEnd are named; the row is the record's row form at a summand s0; the record is as `PscAt`
    (OnBytes/Tie/Pv/Psc/PscTie.lean) asks; and if the reading of beta is not 0: the port's rounds
    are read as the transcript made from them (`ReadsAs`); `plainOut` on what was heard has eps, the
    last value, the point and the end values of the port's record, read; and if T's weights at st
    and at the output's point are the readings of the caller's, the typed summand at the output's
    point and values is the reading of s0.

Limits: one direction: from the routines' success. That the reading of beta is not 0 is a premise,
and so is that the caller's weights are the typed weights at the point. The further scalars that a
caller receives before sc3In are the caller's. `sc3_tie` says nothing of the state that the routines
leave: OnBytes/Tie/Pv/Att/TiesFull.lean states the tie with that state.
-/
import OnBytes.Tie.Pv.Att.ScdTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att
open OnBytes.Psc (Weight hearMany)

theorem sc3Row_ok (o1 o : Attention.Sc3) (W : Array E) (F G : Fork) (c c' : Ctx)
    (h : sc3Row o1 W F c = .ok ((o, G), c')) (hs : Sized F) :
    c' = c ∧ W.size = o1.nb ∧
      o.rowU = o1.p.rowForm (sc3Flat W (shownAt F o1.sEnd) o1.nb 0 zeroE) {} ∧
      o.p = { o1.p with rowMade := true } ∧ o.r = o1.r ∧ o.sEnd = o1.sEnd ∧ o.nb = o1.nb ∧
      Filled F G o1.p.first (List.replicate o1.p.walk.1.length zeroE) (subE zeroE oneE) := by
  unfold sc3Row at h
  obtain ⟨_, F0, c0, h0, k0⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨m1, m2⟩ := (lift_ok _ _ _ _ _ _).1 h0
  obtain ⟨m3, m4⟩ := (mustAs_ok _ _ _ _ _).1 m1
  rw [m2, m4] at k0
  obtain ⟨s0, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 k0
  obtain ⟨s1, s2, s3⟩ := sc3Shown_flat o1 W _ _ _ _ _ _ _ _ h1
  rw [s1, s2, s3] at k1
  obtain ⟨⟨row, p'⟩, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
  obtain ⟨a1, a2, a3, a4⟩ := pscRow_filled o1.p p' _ {} row F F2 c c2 h2 hs
  rw [e1, e2, e3]
  exact ⟨a1, by simpa using m3, a2, a3, rfl, rfl, rfl, a4⟩

section Top
variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- the number of an end value -/
def sc3Num {nb : ℕ} (a : Fin nb × Bool) : Nat := 2 * a.1.1 + if a.2 then 1 else 0

/-- the end values, read, under their names -/
def sc3Vals (nb : ℕ) (v : List E) : Fin nb × Bool → K := fun a => ρ.val (v.getD (sc3Num a) zeroE)

theorem sc3Num_lt {nb : ℕ} (a : Fin nb × Bool) : sc3Num a < 2 * nb := by
  have := a.1.2
  unfold sc3Num
  split_ifs <;> omega

theorem sc3_block_out (T : Cb.Pv.Att.Sc3 K) (st : T.St) (target mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0)
    (vals : Fin T.nb × Bool → K) (n : ℕ) {X : Type} (cl : X → (Fin n → K) → K × T.St)
    (Ex : ExtSpec) (x : X) (y : Ex.Str) (r : Fin n → K) (hcl : cl x r = (ρ.val target, st)) :
    (rideNR T.plain.our.par n T.plain.fix cl Ex).out x y
        (((), (r, ρ.val mu)), ρ.val eps, plainTr ρ T.plain rs sentY beta hβ vals) =
      some ((x, r), plainOut ρ T.plain st target mu eps rs sentY beta hβ vals) := by
  show ((shortR T.plain.our.par T.plain.fix Ex).out (cl x r) y _).map _ = _
  rw [short_out T.plain.our.par T.plain.fix Ex (sc3_fix T), hcl]
  rfl

theorem sc3_tie (T : Cb.Pv.Att.Sc3 K) (C : Aff) (W : Array E) (o1 o : Attention.Sc3)
    (F F2 G : Fork) (c c2 c' : Ctx) (h1 : sc3In T.nv T.nb C F c = .ok ((o1, F2), c2))
    (h2 : sc3Row o1 W F2 c2 = .ok ((o, G), c')) (hz : Sized F) (st : T.St) :
    ∃ (τ mu : E) (rs : List (List E × E)) (sentY : List E) (beta : E) (v : List E) (s0 : E),
      F.publicPart C = some τ ∧
      Parts c c c' [] mu o.p.eps (List.replicate T.nv (Weight.plain 4)) rs 2 sentY beta v ∧
      v.length = 2 * T.nb ∧ W.size = T.nb ∧ o.r.toList = rs.map (·.2) ∧
      o.p.start = C ∧ o.p.target = τ ∧ o.p.first = F.next ∧
      o.sEnd = F.next + (1 + 3 * T.nv) + 2 ∧
      o.rowU = o.p.rowForm s0 {} ∧
      PscAt o.p (plainWs (List.ofFn T.plain.deg) T.plain.DY) (rs ++ [(sentY, beta)]) mu ∧
      rs.map (·.1.length) = List.ofFn T.plain.deg ∧ sentY.length = T.plain.DY ∧
      ∀ hβ : ρ.val beta ≠ 0,
        ReadsAs ρ (rs ++ [(sentY, beta)]) T.plain.our.par.fmt [pRoundV K T.plain.our.par.A]
          (plainTr ρ T.plain rs sentY beta hβ (sc3Vals ρ T.nb v)) ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).eps =
          ρ.val o.p.eps ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).fin =
          ρ.val o.p.claim ∧
        (∀ i : Fin T.nv, ldPartIni T.nv (fun _ => 3) (pDummy K 2)
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt i =
            ρ.val (o.r.getD i.1 zeroE)) ∧
        ldPartLast T.nv (fun _ => 3) (pDummy K 2)
          (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt =
            ρ.val beta ∧
        (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).vals =
          sc3Vals ρ T.nb v ∧
        ((∀ b : Fin T.nb, T.W st b
            (ldPartIni T.nv (fun _ => 3) (pDummy K 2)
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt) =
            ρ.val (W.getD b.1 zeroE)) →
          T.plain.S st
            (ldPartIni T.nv (fun _ => 3) (pDummy K 2)
              (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt)
            (plainOut ρ T.plain st τ mu o.p.eps rs sentY beta hβ (sc3Vals ρ T.nb v)).vals =
          ρ.val s0) := by
  obtain ⟨τ, mu, rs, sentY, beta, v, a1, a2, a3, a4, a5, a6, a7, _, a9, a11, a12⟩ :=
    sc3In_seam _ _ _ o1 F F2 c c2 h1 hz
  obtain ⟨b1, b0, b2, b3, b4, b5, _, _⟩ := sc3Row_ok o1 o W F2 G c2 c' h2 a12.sized
  have hε : o.p.eps = o1.p.eps := by rw [b3]
  have hcl : o.p.claim = o1.p.claim := by rw [b3]
  have hdeg : List.ofFn T.plain.deg = List.replicate T.nv 3 := List.ofFn_const _ _
  have hl : rs.map (·.1.length) = List.ofFn T.plain.deg := by rw [hdeg]; exact a5
  have hat := ended_pscAt a3
  have hws : plainWs (List.ofFn T.plain.deg) T.plain.DY =
      List.replicate T.nv (Weight.plain 4) ++ [Weight.atZero (2 + 1)] := by
    unfold plainWs
    rw [hdeg, List.map_replicate]
    rfl
  have hsh : ∀ j, j < 2 * T.nb → shownAt F2 o1.sEnd j = v.getD j zeroE := fun j hj => by
    unfold shownAt
    rw [a12.shown _ (by rw [a7]; exact hj)]
    rfl
  refine ⟨τ, mu, rs, sentY, beta, v, sc3Flat W (shownAt F2 o1.sEnd) o1.nb 0 zeroE, a1, ?_, a7,
    by rw [b0, a9], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl, a6, ?_⟩
  · rw [hε, b1]
    exact a2
  · rw [b4]
    exact a4
  · rw [b3]
    exact a3.start
  · rw [b3]
    exact a3.target
  · rw [b3]
    exact a3.first
  · rw [b5]
    exact a11
  · rw [b2, b3]
    rfl
  · rw [hws, b3]
    exact ⟨hat.vars, hat.r, hat.claim⟩
  · intro hβ
    refine ⟨plain_reads ρ T.plain rs sentY beta hβ _ hl a6, rfl, ?_, ?_,
      plain_last ρ T.plain st _ _ _ rs sentY beta hβ _,
      plain_vals ρ T.plain st _ _ _ rs sentY beta hβ _, ?_⟩
    · rw [plain_fin ρ T.plain st _ _ _ rs sentY beta hβ _ (sc3_ok T).one hl a6, hws, hcl, a3.claim,
        hε]
    · intro i
      rw [b4, toList_getD o1.r _ a4, snd_getD]
      exact plain_ini ρ T.plain st _ _ _ rs sentY beta hβ _ i
    · intro hW
      rw [plain_vals, a9, sc3Flat_read]
      show ∑ b : Fin T.nb, T.W st b _ * sc3Vals ρ T.nb v (b, false) * sc3Vals ρ T.nb v (b, true) = _
      refine Finset.sum_congr rfl fun b _ => ?_
      have hb := b.2
      rw [hW b, hsh (2 * b.1) (by omega), hsh (2 * b.1 + 1) (by omega)]
      rfl

end Top

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.sc3Row_ok
#print axioms OnBytes.Tie.Pv.Att.sc3_block_out
#print axioms OnBytes.Tie.Pv.Att.sc3_tie
