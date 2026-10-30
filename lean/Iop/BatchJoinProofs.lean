-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchJoinProofs.lean: lemmas on two consecutive rounds of a protocol with slots that are merged
into one, by (J1) or (J2) (Iop/BatchJoin.lean). Iop/BatchRecutProofs.lean uses them. As
Iop/JoinProofs.lean, whose lemma `eq_zero_of_below` is used, and after Iop/BatchSplitProofs.lean.
The lemmas are in the namespace `Iop.BatchJoin`. (Words of this library: lean/GLOSSARY.md.)

The soundness property `SndB` (Snd-B). The state of a prefix of a transcript of the merged protocol
is the state of the old prefix to which `unMsgP` or `unChalP` maps it.
 (J2) The joint count over pairs (c1, c2): `roundLaw_two`.
 (J1) The condition on the challenge c2 is the old one. That the merged prover message does not
      change 0 to 1 needs that the one value u of the first challenge does not: this is the old
      condition on challenges with the error 0. So the condition on prover messages is carried
      together with the condition on challenges through the induction on the plan (`joint_recut`,
      Iop/BatchRecutProofs.lean).

Notation: `SwitchLaw n s S0 S1 : Prop` (Iop/BatchSplitProofs.lean): if the state S0 is 0 before the
prover message of round n, so is the state S1; `PTr s : Type` (Iop/State.lean): partial transcripts:
at the prover (`atP`), at the verifier (`atV`), or full (`full`); `u : r1.Chal`: a value of the
challenge of r1; in `XPlan.OK` (Iop/Recut.lean), at `.msg _ _ u X`: `∀ c, c = u`.
-/
import Iop.BatchJoin
import Iop.JoinProofs
import Iop.BatchSound
import Iop.BatchSplitProofs

namespace Iop
open Prob
open scoped ENNReal

namespace BatchJoin

/-! ## 1. Kinds -/

section Kinds
variable {C C1 C2 : Type} {N : ℕ}

theorem slot_constAll (j : Fin N) : ∀ (k : Kind) (c : C), k.slot (Kind.constAll N k c) j = c
  | .sh, _ => rfl
  | .lo, _ => rfl

theorem slot_sndAll (j : Fin N) :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (v : k1.All N (C1 × C2)),
      k2.slot (Kind.sndAll k1 k2 h v) j = (k1.slot v j).2
  | .sh, .sh, _, _ => rfl
  | .lo, .lo, _, _ => rfl

theorem sndSh_shOf :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (c : C1 × C2), Kind.sndSh k1 k2 h (k1.shOf c) = k2.shOf c.2
  | .sh, .sh, _, _ => rfl
  | .lo, .lo, _, _ => rfl

theorem sndLo_loOf :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (c : C1 × C2), Kind.sndLo k1 k2 h (k1.loOf c) = k2.loOf c.2
  | .sh, .sh, _, _ => rfl
  | .lo, .lo, _, _ => rfl

theorem pairAll_fst_snd :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (v : k1.All N (C1 × C2)),
      Kind.pairAll k1 k2 h (k1.mapAll Prod.fst v) (Kind.sndAll k1 k2 h v) = v
  | .sh, .sh, _, _ => rfl
  | .lo, .lo, _, _ => rfl

theorem fst_pairAll :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (a : k1.All N C1) (b : k2.All N C2),
      k1.mapAll Prod.fst (Kind.pairAll k1 k2 h a b) = a
  | .sh, .sh, _, _, _ => rfl
  | .lo, .lo, _, _, _ => rfl

theorem snd_pairAll :
    ∀ (k1 k2 : Kind) (h : k2 = k1) (a : k1.All N C1) (b : k2.All N C2),
      Kind.sndAll k1 k2 h (Kind.pairAll k1 k2 h a b) = b
  | .sh, .sh, _, _, _ => rfl
  | .lo, .lo, _, _, _ => rfl

theorem eq_constAll {u : C} (hu : ∀ c, c = u) :
    ∀ (k : Kind) (v : k.All N C), Kind.constAll N k u = v
  | .sh, v => (hu v).symm
  | .lo, v => funext fun j => (hu (v j)).symm

end Kinds

/-! ## 2. Challenges -/

section Heads
variable {r1 r2 : Round} {s : Shape} (a1 : RAnn r1) (a2 : RAnn r2) (A : RoundSplits s)

/-! A round merged by (J1) has the challenges and the kind of the second round. So `BRho.slot`,
`Rho.lo` and `Rho.sh` give the same on the challenges of a list of rounds that begins with the
merged round as on those of the list that begins with the second round; for a variable this is seen
after it is destructured. -/

theorem slot_msg {N : ℕ} (j : Fin N) :
    ∀ x : BRho N (r1.joinMsg r2 :: s) (a1.joinMsg a2, A),
      BRho.slot j (s := r2 :: s) (A := (a2, A)) x =
        BRho.slot j (s := r1.joinMsg r2 :: s) (A := (a1.joinMsg a2, A)) x := by
  rintro ⟨_, _⟩
  rfl

theorem lo_msg :
    ∀ x : Rho (r1.joinMsg r2 :: s),
      Rho.lo (s := r2 :: s) (a2, A) x = Rho.lo (s := r1.joinMsg r2 :: s) (a1.joinMsg a2, A) x := by
  rintro ⟨_, _⟩
  rfl

theorem sh_msg :
    ∀ x : Rho (r1.joinMsg r2 :: s),
      Rho.sh (s := r2 :: s) (a2, A) x = Rho.sh (s := r1.joinMsg r2 :: s) (a1.joinMsg a2, A) x := by
  rintro ⟨_, _⟩
  rfl

variable {a1 a2}

theorem slot_chal {N : ℕ} (hk : a2.kind = a1.kind) (j : Fin N) :
    ∀ z : BRho N (r1.joinChal r2 :: s) (a1.joinChal r2, A),
      BRho.slot j (s := r1 :: r2 :: s) (A := (a1, a2, A))
          (a1.kind.mapAll Prod.fst z.1, Kind.sndAll a1.kind a2.kind hk z.1, z.2) =
        ((BRho.slot j z : Rho (r1.joinChal r2 :: s)).1.1,
          (BRho.slot j z : Rho (r1.joinChal r2 :: s)).1.2,
          (BRho.slot j z : Rho (r1.joinChal r2 :: s)).2) := by
  rintro ⟨v, z⟩
  exact Prod.ext (BatchPull.slot_mapAll Prod.fst j a1.kind v)
    (Prod.ext (slot_sndAll j a1.kind a2.kind hk v) rfl)

theorem lo_chal (hk : a2.kind = a1.kind) :
    ∀ x : Rho (r1.joinChal r2 :: s),
      (a1.kind.mapLo Prod.fst (Rho.lo (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).1,
          Kind.sndLo a1.kind a2.kind hk (Rho.lo (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).1,
          (Rho.lo (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).2) =
        Rho.lo (s := r1 :: r2 :: s) (a1, a2, A) (x.1.1, x.1.2, x.2) := by
  rintro ⟨c, z⟩
  exact Prod.ext (BatchPull.loOf_map Prod.fst a1.kind c)
    (Prod.ext (sndLo_loOf a1.kind a2.kind hk c) rfl)

theorem sh_chal (hk : a2.kind = a1.kind) :
    ∀ x : Rho (r1.joinChal r2 :: s),
      (a1.kind.mapSh Prod.fst (Rho.sh (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).1,
          Kind.sndSh a1.kind a2.kind hk (Rho.sh (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).1,
          (Rho.sh (s := r1.joinChal r2 :: s) (a1.joinChal r2, A) x).2) =
        Rho.sh (s := r1 :: r2 :: s) (a1, a2, A) (x.1.1, x.1.2, x.2) := by
  rintro ⟨c, z⟩
  exact Prod.ext (BatchPull.shOf_map Prod.fst a1.kind c)
    (Prod.ext (sndSh_shOf a1.kind a2.kind hk c) rfl)

end Heads


/-! ## 3. Annotations -/

theorem coherent_msg {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2}
    (h1 : a1.Coherent) (h2 : a2.Coherent) : (a1.joinMsg a2).Coherent where
  plain_join := fun m0 mj => by
    show (((a1.plain (a1.join m0.1 mj.1).2).1, (a2.plain (a2.join m0.2 mj.2).2).1),
        ((a1.plain (a1.join m0.1 mj.1).2).2, (a2.plain (a2.join m0.2 mj.2).2).2)) = _
    rw [h1.plain_join, h2.plain_join]
  rd_shared := fun m0 mj mj' p hp => match p, hp with
    | .inl p, hp => h1.rd_shared m0.1 mj.1 mj'.1 p hp
    | .inr p, hp => h2.rd_shared m0.2 mj.2 mj'.2 p hp
  rd_own := fun m0 m0' mj p hp => match p, hp with
    | .inl p, hp => h1.rd_own m0.1 m0'.1 mj.1 p hp
    | .inr p, hp => h2.rd_own m0.2 m0'.2 mj.2 p hp

/-! ## 4. Prefixes -/

section
variable {r1 r2 : Round} {s : Shape}

/-- A prefix that begins with a round merged by (J1), with the two rounds again. -/
def unMsgP (u : r1.Chal) : PTr (r1.joinMsg r2 :: s) → PTr (r1 :: r2 :: s)
  | .atP (.inl _) => .atP (.inl ())
  | .atP (.inr z) => .atP (.inr (Round.msgFst z.1, u, .inr (Round.msgSnd z.1, z.2.1, z.2.2)))
  | .atV (.inl m) => .atV (.inr (Round.msgFst m, u, .inl (Round.msgSnd m)))
  | .atV (.inr z) => .atV (.inr (Round.msgFst z.1, u, .inr (Round.msgSnd z.1, z.2.1, z.2.2)))
  | .full z => .full (Tr.unMsg u z)

/-- A prefix that begins with a round merged by (J2), with the two rounds again. -/
def unChalP : PTr (r1.joinChal r2 :: s) → PTr (r1 :: r2 :: s)
  | .atP (.inl _) => .atP (.inl ())
  | .atP (.inr z) => .atP (.inr (z.1, z.2.1.1, .inr (r2.dMsg, z.2.1.2, z.2.2)))
  | .atV (.inl m) => .atV (.inl m)
  | .atV (.inr z) => .atV (.inr (z.1, z.2.1.1, .inr (r2.dMsg, z.2.1.2, z.2.2)))
  | .full z => .full (Tr.unChal z)

theorem unMsgP_cons (u : r1.Chal) (m : (r1.joinMsg r2).Msg) (c : r2.Chal) :
    ∀ t : PTr s, unMsgP u (PTr.cons (r := r1.joinMsg r2) m c t) =
      PTr.cons (Round.msgFst m) u (PTr.cons (Round.msgSnd m) c t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

theorem unChalP_cons (m : r1.Msg) (c : r1.Chal × r2.Chal) :
    ∀ t : PTr s,
      unChalP (PTr.cons (r := r1.joinChal r2) m c t) = PTr.cons m c.1 (PTr.cons r2.dMsg c.2 t)
  | .atP _ => rfl
  | .atV _ => rfl
  | .full _ => rfl

end



/-! ## 5. The soundness property `SndB` (Snd-B) -/

open BatchH4 (ProverLaw)
open BatchSplit (RoundLaw SwitchLaw)

theorem not_of_cnt_le_zero {C : Type} [Finite C] {P : C → Prop} (h : cnt P ≤ 0) (c : C) :
    ¬ P c := fun hc => by
  haveI : Nonempty {a : C // P a} := ⟨⟨c, hc⟩⟩
  exact absurd h (Nat.not_le.2 (Nat.card_pos (α := {a : C // P a})))

/-- The condition of a round (`RoundLaw`) for state functions composed with maps `f j` is the
condition for the state functions themselves, at the images of the prefixes. -/
theorem roundLaw_map {N : ℕ} {T T' C : Type} [Finite C] (f : Fin N → T' → T) (k : Kind) (e : ℕ)
    (St : Fin N → Option (T → Bool)) (x0 : Fin N → T') (x1 : Fin N → C → T') :
    RoundLaw k e (fun j => (St j).map fun S t => S (f j t)) x0 x1 ↔
    RoundLaw k e St (fun j => f j (x0 j)) (fun j c => f j (x1 j c)) := by
  cases k with
  | lo =>
      constructor
      · intro h j S hS h0
        exact h j (fun t => S (f j t)) (by show (St j).map _ = _; rw [hS]; rfl) h0
      · intro h j S' hS' h0
        obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
        exact h j S hS h0
  | sh =>
      constructor
      · intro h
        refine le_trans (cnt_mono ?_) h
        rintro c ⟨j, S, hS, h0, h1⟩
        exact ⟨j, fun t => S (f j t), by show (St j).map _ = _; rw [hS]; rfl, h0, h1⟩
      · intro h
        refine le_trans (cnt_mono ?_) h
        rintro c ⟨j, S', hS', h0, h1⟩
        obtain ⟨S, hS, rfl⟩ := Option.map_eq_some_iff.1 hS'
        exact ⟨j, S, hS, h0, h1⟩

theorem roundLaw_mono {N : ℕ} {T C : Type} [Finite C] {k : Kind} {e e' : ℕ}
    {St : Fin N → Option (T → Bool)} {x0 : Fin N → T} {x1 : Fin N → C → T}
    (he : e ≤ e') (h : RoundLaw k e St x0 x1) : RoundLaw k e' St x0 x1 := by
  cases k with
  | lo => exact fun j S hS h0 => (h j S hS h0).trans he
  | sh => exact le_trans h he

/-- With the error 0 no challenge changes a state from 0 to 1. -/
theorem roundLaw_noFlip {N : ℕ} {T C : Type} [Finite C] {k : Kind} {St : Fin N → Option (T → Bool)}
    {x0 : Fin N → T} {x1 : Fin N → C → T} (h : RoundLaw k 0 St x0 x1) {j : Fin N} {S : T → Bool}
    (hS : St j = some S) (h0 : S (x0 j) = false) (c : C) : S (x1 j c) = false := by
  cases k with
  | lo => exact (Bool.not_eq_true _).mp (not_of_cnt_le_zero (h j S hS h0) c)
  | sh => exact (Bool.not_eq_true _).mp fun h1 => not_of_cnt_le_zero h c ⟨j, S, hS, h0, h1⟩

/-- Two rounds of the same kind, with one prover message between: x0 before the first challenge, x1
after it, y0 after the prover message, x2 after the second challenge. If both satisfy `RoundLaw` and
the message never changes 0 to 1, the pair satisfies it with e1 |C2| + |C1| e2. -/
theorem roundLaw_two {N : ℕ} {T C1 C2 : Type} [Fintype C1] [Fintype C2] (k1 k2 : Kind)
    (hk : k2 = k1) (e1 e2 : ℕ) (St : Fin N → Option (T → Bool)) (x0 : Fin N → T)
    (x1 y0 : Fin N → C1 → T) (x2 : Fin N → C1 → C2 → T) (h1 : RoundLaw k1 e1 St x0 x1)
    (hp : ∀ j S c1, St j = some S → S (x1 j c1) = false → S (y0 j c1) = false)
    (h2 : ∀ v : k1.All N C1,
      RoundLaw k2 e2 St (fun j => y0 j (k1.slot v j)) (fun j c2 => x2 j (k1.slot v j) c2)) :
    RoundLaw k1 (e1 * Fintype.card C2 + Fintype.card C1 * e2) St x0
      (fun j (c : C1 × C2) => x2 j c.1 c.2) := by
  subst hk
  cases k2 with
  | lo =>
      intro j S hS h0
      exact cnt_two_rounds_le (fun x : C1 × C2 => S (x2 j x.1 x.2) = true)
        (fun c1 => S (x1 j c1) = true) e1 e2 (h1 j S hS h0)
        fun c1 hc => h2 (fun _ => c1) j S hS (hp j S c1 hS ((Bool.not_eq_true _).mp hc))
  | sh =>
      refine cnt_two_rounds_le
        (fun x : C1 × C2 => ∃ j S, St j = some S ∧ S (x0 j) = false ∧ S (x2 j x.1 x.2) = true)
        (fun c1 => ∃ j S, St j = some S ∧ S (x0 j) = false ∧ S (x1 j c1) = true) e1 e2 h1
        fun c1 hc => le_trans (cnt_mono ?_) (h2 c1)
      rintro c2 ⟨j, S, hS, h0, h2'⟩
      exact ⟨j, S, hS,
        hp j S c1 hS ((Bool.not_eq_true _).mp fun h1' => hc ⟨j, S, hS, h0, h1'⟩), h2'⟩


theorem join_split {r : Round} (a : RAnn r) (m : r.Msg) : a.join (a.split m).1 (a.split m).2 = m :=
  a.split.symm_apply_apply m

theorem proverLaw_chal {r1 r2 : Round} {s : Shape}
    (S : PTr (r1 :: r2 :: s) → Bool) (h : ProverLaw (r1 :: r2 :: s) S) :
    ProverLaw (r1.joinChal r2 :: s) (fun t => S (unChalP t))
  | .inl _, m, h0 => h (.inl ()) m h0
  | .inr (m1, c, τ), m, h0 => h (.inr (m1, c.1, .inr (r2.dMsg, c.2, τ))) m h0

theorem proverLaw_msg {r1 r2 : Round} {s : Shape} (u : r1.Chal)
    (S : PTr (r1 :: r2 :: s) → Bool) (h : ProverLaw (r1 :: r2 :: s) S)
    (hz : ∀ m1 : r1.Msg,
      S (.atV (.inl m1)) = false → S (PTr.cons m1 u (PTr.empty (r2 :: s))) = false) :
    ProverLaw (r1.joinMsg r2 :: s) (fun t => S (unMsgP u t))
  | .inl _, m, h0 =>
    h (.inr (Round.msgFst m, u, .inl ())) (Round.msgSnd m) (hz _ (h (.inl ()) (Round.msgFst m) h0))
  | .inr (m12, c, τ), m, h0 => h (.inr (Round.msgFst m12, u, .inr (Round.msgSnd m12, c, τ))) m h0

variable {X : Type} {E : ExtSpec}

/-! ## 5a. The late form `SndBL` of (Snd-B) (Iop/Batch.lean): `SwitchLaw`
(Iop/BatchSplitProofs.lean) after a merge; and `unitZero_of_below` -/

theorem switch_msg {r1 r2 : Round} {s : Shape} (u : r1.Chal) (n : ℕ) (hn : n ≠ 1)
    (S0 S1 : PTr (r1 :: r2 :: s) → Bool) (h : SwitchLaw n (r1 :: r2 :: s) S0 S1) :
    SwitchLaw (n - 1) (r1.joinMsg r2 :: s) (fun t => S0 (unMsgP u t)) (fun t => S1 (unMsgP u t))
  | .inl _, hi, h0 => h (.inl ()) (by have : (0 : ℕ) = n - 1 := hi; show 0 = n; omega) h0
  | .inr (m, c, τ), hi, h0 =>
      h (.inr (Round.msgFst m, u, .inr (Round.msgSnd m, c, τ)))
        (by have : τ.idx + 1 = n - 1 := hi; show τ.idx + 1 + 1 = n; omega) h0

theorem switch_chal {r1 r2 : Round} {s : Shape} (n : ℕ) (hn : n ≠ 1)
    (S0 S1 : PTr (r1 :: r2 :: s) → Bool) (h : SwitchLaw n (r1 :: r2 :: s) S0 S1) :
    SwitchLaw (n - 1) (r1.joinChal r2 :: s) (fun t => S0 (unChalP t)) (fun t => S1 (unChalP t))
  | .inl _, hi, h0 => h (.inl ()) (by have : (0 : ℕ) = n - 1 := hi; show 0 = n; omega) h0
  | .inr (m, c, τ), hi, h0 =>
      h (.inr (m, c.1, .inr (r2.dMsg, c.2, τ)))
        (by have : τ.idx + 1 = n - 1 := hi; show τ.idx + 1 + 1 = n; omega) h0




theorem unitZero_of_below : ∀ {s : Shape} {ε : Err s} {c : ℝ≥0∞}, c < 1 → Err.Below ε c → ε.UnitZero
  | [], _, _, _, _ => trivial
  | _ :: _, (_, _), _, hc, h => ⟨fun h1 => eq_zero_of_below hc h1 h.1, unitZero_of_below hc h.2⟩




variable {Wt : Type}







open BatchPull (slotOut output_eq)


end BatchJoin

/-! ## 6. The pattern `RoundSplits.Fmt` -/

namespace BatchJoin
open BatchSplit (fmtAt fmtFrom_cons)

theorem noShared_msg {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2}
    (h1 : a1.NoShared) (h2 : a2.NoShared) : (a1.joinMsg a2).NoShared :=
  ⟨fun p => match p with
    | .inl p => h1.1 p
    | .inr p =>
      h2.1 p, haveI := h1.2; haveI := h2.2; inferInstanceAs (Subsingleton (a1.M0 × a2.M0))⟩

theorem noSlot_msg {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2} (h1 : a1.NoSlot) (h2 : a2.NoSlot) :
    (a1.joinMsg a2).NoSlot :=
  ⟨fun p => match p with
    | .inl p => h1.1 p
    | .inr p =>
      h2.1 p, haveI := h1.2; haveI := h2.2; inferInstanceAs (Subsingleton (a1.Mj × a2.Mj))⟩

/-- The table of `FPhase.fitMsg` is right (format, phase: Iop/BatchFmt.lean): if both rounds have a
format and the merge fits, so has the merged round, with the same phase after it. (S1, L1, S2, L2:
the two rounds have no shared, no slot's component; S, L: the same for the merged round, which lacks
a component that both rounds lack (hS, hL).) -/
theorem fitMsg_table (k1 k2 : Kind) (ph : FPhase) {S1 L1 S2 L2 S L : Prop}
    (hS : S1 → S2 → S) (hL : L1 → L2 → L) (h1 : fmtAt k1 ph S1 L1)
    (h2 : fmtAt k2 (FPhase.after k1 ph) S2 L2) (hF : FPhase.fitMsg k1 k2 ph) :
    fmtAt k2 ph S L ∧ FPhase.after k2 (FPhase.after k1 ph) = FPhase.after k2 ph := by
  cases k1 <;> cases k2 <;> cases ph
    <;> simp_all [fmtAt, FPhase.fitMsg, FPhase.after, FPhase.afterLo]

theorem after_after (k : Kind) (ph : FPhase) :
    FPhase.after k (FPhase.after k ph) = FPhase.after k ph := by
  cases k <;> cases ph <;> rfl

end BatchJoin







end Iop
