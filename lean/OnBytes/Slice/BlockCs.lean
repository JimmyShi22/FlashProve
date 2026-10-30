-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlockCs.lean: the two rounds of a code switch are taken off the written proximity
test.

Where the block is in the test. A fold leaves one linear claim on three folded rows of the old
tree's tables. In the first round of the switch the prover sends a new tree, and the verifier draws
the seed of its sample. In the second round the prover sends the sample's answer, and the verifier
draws one element and positions of the old tree. The verifier tests nothing. It moves its claim to
the tables that the new tree commits to.

What is proved. If the claim before the switch has no witness, then the prover has lost in the two
rounds and what follows, provided that it has lost in what follows whenever the claim after the
switch has no witness. "Has lost" is the library's `Doomed` (Iop/Rbr.lean): whatever the prover
sends, in each round at most the stated count of verifier messages lets it recover, and at the end
the goal holds. "No witness" is meant in the relaxed relations of OnBytes/Slice/Stage.lean: no
message with tails has an encoding within e positions of the word (e' after the switch) and meets
the claim. The step is the library's theorem on its code switch (`Cb.ldSwitch_know`) with the
parameters of OnBytes/Slice/CsData.lean, carried to the written rounds (OnBytes/Slice/Peel.lean).

The block is stated twice.
 `cs_block_sem`  for any target, vector and word before the switch. The rounds' values are read in
                 the field. The claim after the switch is `csNext`, the library's output with its
                 form written as a vector. `csNext_fst` and `csNext_snd` give it entry by entry
                 (OnBytes/Slice/CsSim.lean).
 `cs_block`      with the format's own functions: the claim before is what a fold hands on, the
                 rounds are read as the format's decision reads them, and the claim after is the
                 row that `csStep` (Fmt/M1Cs.lean) computes. It follows from the first statement and
                 `cs_sim` (OnBytes/Slice/CsSim.lean).

What is asked: the sizes of the two stages fit (`CsFit`); the two rounds send and draw what a switch
sends and draws (`CsRounds`); the old code has the library's laws; at most L pairs of a message and
tails of the new code lie within e' positions of any word; the goal `bad` holds of every transcript
in which a round's test of work fails. In `cs_block` also: the point that the fold hands on has as
many coordinates as the old stage has row variables; a column that is shown is the old tree's; the
goal holds of every transcript at which `csStep` gives no row.

The error counts (`csErr`) are the library's, each times the number in the law of the format's
sampler.

Not claimed. Nothing on the size of L or of the error counts. Nothing on the new word: the switch
does not read it, and the map from the first round's message to a word is arbitrary. Nothing on an
honest prover.
-/
import OnBytes.Slice.CsSim
import OnBytes.Slice.RoundsMaps
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

variable {s s' : Sg}

/-- What the two rounds of a switch send and draw. The first sends no field element and draws the
seed of the new tree's sample: a point and a factor other than 0. The second sends one element, the
answer, and draws one element and the positions of the old tree. Nothing is said of the tree that
the first round sends. -/
structure CsRounds (s s' : Sg) (dS dC : PQ.RD) : Prop where
  seed : SendsDraws dS 0 (s'.st.na + 1) 0 0
  nz : IsNZ (Fmt.dsOf dS.entry dS.kind) s'.st.na
  cs : SendsDraws dC 1 1 s.t s.C.a

/-- The typed values of the second round as the library's verifier message: the positions, then the
element. -/
def gCs (a t : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) : (Fin t → Fin (2 ^ a)) × GE :=
  (gPos a t ds v, gOne ds v)

/-- The typed values of the second round are determined by that message. -/
theorem gCs_inj {dC : PQ.RD} {a t : ℕ} (h : SendsDraws dC 1 1 t a) :
    Function.Injective (gCs a t (Fmt.dsOf dC.entry dC.kind)) := fun v w hvw => by
  have h1 : (gMix 1 a t _ v).1 = (gMix 1 a t _ w).1 := funext fun i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (Prod.ext_iff.1 hvw).2
  have h2 : (gMix 1 a t _ v).2 = (gMix 1 a t _ w).2 := (Prod.ext_iff.1 hvw).1
  exact h.gMix_inj (Prod.ext h1 h2)

/-- The error counts of the two written rounds: the library's, each times the number in the law
of the format's sampler. -/
def csErr (hf : CsFit s s') (e L : ℕ) (dS dC : PQ.RD) :
    Err (PQ.uL (ckP .two) [dS, dC]) :=
  ((csSw hf).W.err1 L * (bsRound .two dS.entry dS.kind).w,
    ((csSw hf).W.err2 e L * (bsRound .two dC.entry dC.kind).w, ()))

/-- The two rounds of a code switch are taken off, for any claim on the three folded rows. No
function of the format on claims is in this statement: the rounds' values are read in the field, and
the claim after the switch is `csNext`. -/
theorem cs_block_sem (hf : CsFit s s') (e e' L : ℕ) (hlaws : s.cMid.Laws)
    (hlist : s'.cIn.ListAt e' L) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (t : Shape) (εt : Err t)
    (τ₀ : GE) (v : s.cMid.J → GE) (y : s.cMid.Word) (fW : (wRound dS).Msg → s'.cIn.Word)
    (hno : ∀ w, ¬ s.RMid e ((τ₀, v), y) w)
    (bad : Tr (wRound dS :: wRound dC :: t) → Prop)
    (hpS : ∀ m c τ, GChal.pass (b := dS.entry.work) c = false → bad (m, c, τ))
    (hpC : ∀ m1 c1 m c τ, GChal.pass (b := dC.entry.work) c = false → bad (m1, c1, m, c, τ))
    (H : ∀ m1 c1 m2 c2,
      (∀ w, ¬ s'.RIn e' (csNext hf τ₀ v y (gSeed s'.st.na _ (valsOf dS c1))
        ((ansOf dC m2).getD 0 0) (gCs s.C.a s.t _ (valsOf dC c2)), fW m1) w) →
      Doomed t εt fun b => bad (m1, c1, m2, c2, b)) :
    Doomed (wRound dS :: wRound dC :: t) (Err.app (csErr hf e L dS dC) εt) bad := by
  -- The library's theorem on its code switch, with the parameters of the two stages.
  have hK := ldSwitch_know GE s.Ps s'.Ps (s.cMid.J → GE) (csSw hf) e e' L hlaws hlist
    (csSample_ok hf) (ok_powers_comap _ _ (csRowNo_inj s))
  -- The image of a written transcript of the two rounds.
  have htr := two_tr (r₁' := s'.cIn.sendRound Unit (csSw hf).Zo.D ())
    (r₂' := Blocks.plainRound ((csSw hf).Zo.S → GE) ((Fin s.t → s.Ps) × GE) fun _ => 0)
    (fun m => (fW m, ())) (chalTo dS (gSeed s'.st.na _))
    (fun m => ((), fun _ => (ansOf dC m).getD 0 0)) (chalTo dC (gCs s.C.a s.t _))
  -- The written rounds are carried to the library's, and the block is taken off.
  refine peel (s := [wRound dS, wRound dC]) (t := t) (ldSwitch (csSw hf)).red hK
    ((τ₀, v), y) trivial hno
    (two (r₁' := s'.cIn.sendRound Unit (csSw hf).Zo.D ())
      (r₂' := Blocks.plainRound ((csSw hf).Zo.S → GE) ((Fin s.t → s.Ps) × GE) fun _ => 0)
      (fun m => (fW m, ())) (chalTo dS (gSeed s'.st.na _))
      (fun m => ((), fun _ => (ansOf dC m).getD 0 0)) (chalTo dC (gCs s.C.a s.t _)))
    (((bsRound .two dS.entry dS.kind).w, ((bsRound .two dC.entry dC.kind).w, ())) : ℕ × ℕ × Unit)
    (two_fib _ _ _ _ _ _
      (chalTo_fib dS _ (gSeed_inj _ _ hr.seed.plain hr.seed.els hr.seed.poss hr.nz) hr.seed.logN)
      (chalTo_fib dC _ (gCs_inj hr.cs) hr.cs.logN)) εt bad ?_ ?_
  · -- A transcript without an image has failed a test of work.
    rintro ⟨m1, c1, m2, c2, ⟨⟩⟩ hτ0
    have hτ := (htr m1 c1 m2 c2).symm.trans hτ0
    cases h1 : chalTo dS (gSeed s'.st.na _) c1 with
    | none => exact doomed_of_all _ _ _ fun b => hpS m1 c1 _ (chalTo_none dS _ c1 h1)
    | some ρo =>
      cases h2 : chalTo dC (gCs s.C.a s.t _) c2 with
      | none => exact doomed_of_all _ _ _ fun b => hpC m1 c1 m2 c2 b (chalTo_none dC _ c2 h2)
      | some c =>
        rw [h1, h2] at hτ
        cases hτ
  · -- A transcript with an image: the library's output statement is `csNext` by definition.
    rintro ⟨m1, c1, m2, c2, ⟨⟩⟩ τ' hτ0 hno'
    have hτ := (htr m1 c1 m2 c2).symm.trans hτ0
    cases h1 : chalTo dS (gSeed s'.st.na _) c1 with
    | none =>
      rw [h1] at hτ
      cases hτ
    | some ρo =>
      cases h2 : chalTo dC (gCs s.C.a s.t _) c2 with
      | none =>
        rw [h1, h2] at hτ
        cases hτ
      | some c =>
        rw [h1, h2] at hτ
        obtain rfl := Option.some.inj hτ
        obtain rfl := chalTo_some dS _ c1 ρo h1
        obtain rfl := chalTo_some dC _ c2 c h2
        exact H m1 c1 m2 c2 fun w hw => hno' _ w rfl hw

/-! ## What the format's decision reads of the two rounds, in the field -/

/-- The seed as the library reads it is the seed as the format's decision reads it. -/
theorem seed_read {dS : PQ.RD} {na : ℕ}
    (hz : IsNZ (Fmt.dsOf dS.entry dS.kind) na) (m : (wRound dS).Msg) (c : (wRound dS).Chal) :
    ∃ β : GEˣ, gSeed na _ (valsOf dS c) = (ptL na ((rvOf dS m c).els.take na), β) ∧
      β.val = toE ((rvOf dS m c).els.getD na Fmt.Fld.zeroE) := by
  refine ⟨unitOf ((elemsV _ (valsOf dS c)).getD na 0), Prod.ext (funext fun i => ?_) rfl, ?_⟩
  · show gVec na _ (valsOf dS c) i = lst ((rvOf dS m c).els.take na) i.val
    rw [gVec_rvOf dS m c na, lst_take na _ _ i.isLt]
    rfl
  · rw [unitOf_val (elemsV_nz _ na hz _)]
    exact congrFun (gVec_rvOf dS m c (na + 1)) (Fin.last na)

/-- The second round likewise. -/
theorem cs_read {dC : PQ.RD} {a t : ℕ} (h : SendsDraws dC 1 1 t a) (m : (wRound dC).Msg)
    (c : (wRound dC).Chal) :
    ∃ alpha theta xs, rvOf dC m c = ⟨[alpha], [theta], xs⟩ ∧ xs.length = t ∧
      (ansOf dC m).getD 0 0 = toE alpha ∧ (gCs a t _ (valsOf dC c)).2 = toE theta ∧
      ∀ i, ((gCs a t _ (valsOf dC c)).1 i).val = xs.getD i.val 0 := by
  obtain ⟨alpha, ha⟩ := List.length_eq_one_iff.1 (h.sent_length m c)
  obtain ⟨theta, ht⟩ := List.length_eq_one_iff.1 (h.els_length m c)
  refine ⟨alpha, theta, (rvOf dC m c).poss, ?_, h.poss_length m c, ?_, ?_, fun i => ?_⟩
  · rw [← ha, ← ht]
  · rw [← rvOf_sent dC m c, ha]
    rfl
  · exact gOne_of_els dC m c ht
  · exact h.gPos_val m c i

/-- The two rounds of a code switch are taken off, with the format's own functions. -/
theorem cs_block (hf : CsFit s s') (e e' L : ℕ) (hlaws : s.cMid.Laws) (hlist : s'.cIn.ListAt e' L)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (t : Shape) (εt : Err t)
    (R : Fmt.M1.SRow) (hg : R.g.length = s.h + s.g)
    (col : ℕ → Fmt.M1.Col) (cols : ℕ → Option Fmt.M1.Col)
    (hcols : ∀ x c, cols x = some c → c = col x)
    (fW : (wRound dS).Msg → s'.cIn.Word)
    (hno : ∀ w, ¬ s.RMid e (stmMid s R, wordMid s col (ptL _ R.g)) w)
    (bad : Tr (PQ.uL (ckP .two) [dS, dC] ++ t) → Prop)
    (hp : ∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b))
    (H : ∀ (τ : Tr (PQ.uL (ckP .two) [dS, dC])) z beta rs3 alpha theta xs G',
      Fmt.M1.seedOf s'.st.na (rsOf _ τ) = some (z, beta, rs3) →
      Fmt.M1.nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []) →
      Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs
        theta cols = some G' →
      (∀ w, ¬ s'.RIn e' (stmIn s' G', fW τ.1) w) →
      Doomed t εt fun b => bad (Tr.app τ b))
    (H0 : ∀ (τ : Tr (PQ.uL (ckP .two) [dS, dC])) z beta rs3 alpha theta xs,
      Fmt.M1.seedOf s'.st.na (rsOf _ τ) = some (z, beta, rs3) →
      Fmt.M1.nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []) →
      Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az z beta alpha) xs
        theta cols = none → ∀ b, bad (Tr.app τ b)) :
    Doomed _ (Err.app (csErr hf e L dS dC) εt) bad := by
  refine cs_block_sem hf e e' L hlaws hlist dS dC hr t εt (toE R.t) (vecMid s R)
    (wordMid s col (ptL _ R.g)) fW hno bad ?_ ?_ ?_
  · -- A failed test of work in the first round, then in the second.
    intro m c τ h
    obtain ⟨m2, c2, b⟩ := τ
    exact hp (m, c, m2, c2, ()) b (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and])
  · intro m1 c1 m c b h
    exact hp (m1, c1, m, c, ()) b
      (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false])
  · -- The format's decision reads both rounds without refusing.
    intro m1 c1 m2 c2 hno'
    obtain ⟨β, hseed, hβ⟩ := seed_read hr.nz m1 c1
    obtain ⟨alpha, theta, xs, hrv, hxs, hans, hth, hQ⟩ := cs_read hr.cs m2 c2
    have hS : Fmt.M1.seedOf s'.st.na (rsOf [dS, dC] (m1, c1, m2, c2, ())) =
        some ((rvOf dS m1 c1).els.take s'.st.na,
          (rvOf dS m1 c1).els.getD s'.st.na Fmt.Fld.zeroE, [rvOf dC m2 c2]) := by
      show Fmt.M1.seedOf s'.st.na (rvOf dS m1 c1 :: [rvOf dC m2 c2]) = _
      unfold Fmt.M1.seedOf
      rw [hr.seed.next m1 c1]
    have hC : Fmt.M1.nextN 1 1 s.t [rvOf dC m2 c2] = some (⟨[alpha], [theta], xs⟩, []) := by
      rw [hr.cs.next m2 c2, hrv]
    have hzl : ((rvOf dS m1 c1).els.take s'.st.na).length = s'.st.na := by
      rw [List.length_take, hr.seed.els_length m1 c1]
      omega
    -- Either a drawn position has no column, or the new row is the claim after the switch.
    cases hcs : Fmt.M1.csStep .two s.st s'.st R (Fmt.M1.sampleRow .two s'.st.Am s'.st.Az
        ((rvOf dS m1 c1).els.take s'.st.na) ((rvOf dS m1 c1).els.getD s'.st.na Fmt.Fld.zeroE)
        alpha) xs theta cols with
    | none => exact doomed_of_all _ _ _ fun b => H0 (m1, c1, m2, c2, ()) _ _ _ _ _ _ hS hC hcs b
    | some G' =>
      refine H (m1, c1, m2, c2, ()) _ _ _ _ _ _ G' hS hC hcs fun w hw => hno' w ?_
      have hnext := cs_sim hf R hg col cols hcols _ _ alpha theta xs hzl hxs β hβ
        (gCs s.C.a s.t _ (valsOf dC c2)).1 hQ G' hcs
      rw [← hth, ← hans, ← hseed] at hnext
      rw [show (gCs s.C.a s.t _ (valsOf dC c2)) = ((gCs s.C.a s.t _ (valsOf dC c2)).1,
        (gCs s.C.a s.t _ (valsOf dC c2)).2) from rfl, hnext]
      exact hw

end OnBytes.Slice

#print axioms OnBytes.Slice.cs_block_sem
#print axioms OnBytes.Slice.cs_block
