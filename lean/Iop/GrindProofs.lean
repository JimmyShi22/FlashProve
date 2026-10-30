-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindProofs.lean: rounds with proof-of-work bits: the proofs of the statements of
Iop/Grind.lean, whose header says what the construction is and what the statements do and do not
say. (Words of this library: lean/GLOSSARY.md.)
`InteractiveOracleProof.grind` (Iop/Grind.lean) adds proof-of-work bits to the rounds of a protocol, along a list g
of numbers (`GBits`, Iop/GBits.lean): in a round with b > 0 such bits the plain part of the prover
message ends in a nonce, the challenge has b further uniform bits, and the verifier rejects unless
all of them are 0. "Old": without these bits; stripping drops them and the nonces. "Doomed":
`Doomed s ε bad` (Iop/Rbr.lean): the empty transcript is doomed with respect to `bad` (a property of
full transcripts, bad for the prover): whatever the prover sends, at most e values of the next
challenge lead to a transcript that is not doomed (e: the round's number in ε); at the end, `bad`
holds.
After the pattern of Iop/RecutProofs.lean.
-/
import Iop.Grind
import Iop.Compose
import Prob.Linear

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. One round -/

namespace GPlain
variable {W P : Type}

theorem old_mk : ∀ (b : ℕ) (p : P) (ν : W), old (mk b p ν) = p
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem mk_old_nonce [Inhabited W] : ∀ {b : ℕ} (p : GPlain W b P), mk b (old p) (nonce p) = p
  | 0, _ => rfl
  | _ + 1, (_, _) => rfl

/-- `mk` with the nonce read from `mk b p ν` is `mk b p ν` again (at b = 0 no nonce is stored). -/
theorem mk_nonce_mk [Inhabited W] : ∀ (b : ℕ) (p : P) (ν : W), mk b p (nonce (mk b p ν)) = mk b p ν
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem nonce_mk_succ [Inhabited W] (b : ℕ) (p : P) (ν : W) : nonce (mk (b + 1) p ν) = ν := rfl

end GPlain

namespace GChal
variable {C : Type}

theorem old_mk : ∀ (b : ℕ) (c : C) (z : Fin b → Bool), old (mk b c z) = c
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem test_mk : ∀ (b : ℕ) (c : C) (z : Fin b → Bool), test (mk b c z) = z
  | 0, _, _ => funext fun i => i.elim0
  | _ + 1, _, _ => rfl

theorem mk_old_test : ∀ {b : ℕ} (c : GChal b C), mk b (old c) (test c) = c
  | 0, _ => rfl
  | _ + 1, (_, _) => rfl

/-- A challenge of a round with b proof-of-work bits is an old challenge and b bits, for every b. -/
def equiv (b : ℕ) (C : Type) : GChal b C ≃ C × (Fin b → Bool) where
  toFun c := (old c, test c)
  invFun p := mk b p.1 p.2
  left_inv := mk_old_test
  right_inv p := Prod.ext (old_mk b p.1 p.2) (test_mk b p.1 p.2)

theorem pass_iff {b : ℕ} (c : GChal b C) : pass c = true ↔ ∀ i, test c i = false :=
  decide_eq_true_iff

theorem old_zero (b : ℕ) (c : C) : old (zero b c) = c := old_mk b c _

theorem pass_zero (b : ℕ) (c : C) : pass (zero b c) = true :=
  (pass_iff _).2 fun i => congrFun (test_mk b c fun _ => false) i

theorem zero_old {b : ℕ} {c : GChal b C} (h : pass c = true) : zero b (old c) = c := by
  have h1 : test c = fun _ => false := funext ((pass_iff c).1 h)
  have h2 := mk_old_test c
  rw [h1] at h2
  exact h2

theorem card_eq (b : ℕ) (C : Type) [Fintype C] :
    Fintype.card (GChal b C) = Fintype.card C * 2 ^ b := by
  rw [Fintype.card_congr (equiv b C), Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- Over each old challenge exactly one new one has all proof-of-work bits 0. -/
theorem cnt_pass (b : ℕ) [Fintype C] (P : C → Prop) :
    cnt (fun c : GChal b C => pass c = true ∧ P (old c)) = cnt P := by
  unfold cnt
  exact Nat.card_congr
    { toFun := fun x => ⟨old x.1, x.2.2⟩
      invFun := fun x => ⟨zero b x.1, pass_zero b x.1, by rw [old_zero]; exact x.2⟩
      left_inv := fun x => Subtype.ext (zero_old x.2.1)
      right_inv := fun x => Subtype.ext (old_zero b x.1) }

/-- The old challenge of a uniform new one is uniform (C nonempty). -/
theorem map_old_unif :
    ∀ (b : ℕ) (C : Type) [Fintype C] [Nonempty C], (unif (GChal b C)).map old = unif C
  | 0, _, _, _ => PMF.map_id _
  | b + 1, C, _, _ =>
    (congrArg (unif (C × (Fin (b + 1) → Bool))).map (funext fun ⟨_, _⟩ => rfl)).trans map_fst_unif

end GChal

variable {W : Type} [Inhabited W]

theorem Round.strip_fillMsg {r : Round} (b : ℕ) (m : r.Msg) (ν : W) :
    Round.stripMsg (Round.fillMsg b m ν) = m :=
  Prod.ext rfl (GPlain.old_mk b m.2 ν)

/-! ## 2. The maps between old and new rounds -/

theorem Shape.grind_length : ∀ (s : Shape) (g : GBits s), (s.grind W g).length = s.length
  | [], _ => rfl
  | _ :: s, (_, g) => congrArg (· + 1) (Shape.grind_length s g)

theorem Shape.grind_zero : ∀ s : Shape, s.grind W (GBits.zero s) = s
  | [] => rfl
  | r :: s => congrArg (r :: ·) (Shape.grind_zero s)

theorem Rho.strip_fill :
    ∀ {s : Shape} (g : GBits s) (ρ : Rho s), Rho.strip g (Rho.fill (W := W) g ρ) = ρ
  | [], _, () => rfl
  | _ :: _, (b, g), (c, ρ) => Prod.ext (GChal.old_zero b c) (Rho.strip_fill g ρ)

theorem Rho.pass_cons {r : Round} {s : Shape} (b : ℕ) (g : GBits s)
    (c : (r.grind W b).Chal) (ρ : Rho (s.grind W g)) :
    Rho.pass (s := r :: s) (b, g) (c, ρ) = (GChal.pass c && Rho.pass g ρ) := rfl

theorem Rho.pass_fill :
    ∀ {s : Shape} (g : GBits s) (ρ : Rho s), Rho.pass g (Rho.fill (W := W) g ρ) = true
  | [], _, _ => rfl
  | _ :: _, (b, g), (c, ρ) => by
      show (GChal.pass (GChal.zero b c) && Rho.pass g (Rho.fill (W := W) g ρ)) = true
      rw [GChal.pass_zero, Rho.pass_fill g ρ]
      rfl

theorem Rho.fill_strip :
    ∀ {s : Shape} (g : GBits s) (ρ : Rho (s.grind W g)),
      Rho.pass g ρ = true → Rho.fill g (Rho.strip g ρ) = ρ
  | [], _, (), _ => rfl
  | _ :: _, (_, g), (_, ρ), h =>
      have h' := (Bool.and_eq_true _ _).mp h
      Prod.ext (GChal.zero_old h'.1) (Rho.fill_strip g ρ h'.2)

theorem Tr.rho_strip :
    ∀ {s : Shape} (g : GBits s) (τ : Tr (s.grind W g)), (Tr.strip g τ).rho = Rho.strip g τ.rho
  | [], _, _ => rfl
  | _ :: _, (_, g), (_, c, τ) => congrArg (Prod.mk (GChal.old c)) (Tr.rho_strip g τ)

theorem Tr.plains_strip :
    ∀ {s : Shape} (g : GBits s) (τ : Tr (s.grind W g)),
      (Tr.strip g τ).plains = Plains.strip g τ.plains
  | [], _, _ => rfl
  | _ :: _, (_, g), (m, _, τ) => congrArg (Prod.mk (GPlain.old m.2)) (Tr.plains_strip g τ)

theorem Tr.read_strip :
    ∀ {s : Shape} (g : GBits s) (τ : Tr (s.grind W g)) (p : OPos (s.grind W g)),
      (Tr.strip g τ).read (OPos.stripE g p) = OSym.strip g p (τ.read p)
  | _ :: _, (_, _), (_, _, _), .inl _ => rfl
  | _ :: _, (_, g), (_, _, τ), .inr q => Tr.read_strip g τ q

theorem OSym.fill_strip :
    ∀ {s : Shape} (g : GBits s) (p : OPos (s.grind W g)) (a : OSym (s.grind W g) p),
      OSym.fill g p (OSym.strip g p a) = a
  | _ :: _, (_, _), .inl _, _ => rfl
  | _ :: _, (_, g), .inr q, a => OSym.fill_strip g q a

theorem OSym.strip_fill :
    ∀ {s : Shape} (g : GBits s) (p : OPos (s.grind W g)) (a : OSym s (OPos.stripE g p)),
      OSym.strip g p (OSym.fill g p a) = a
  | _ :: _, (_, _), .inl _, _ => rfl
  | _ :: _, (_, g), .inr q, a => OSym.strip_fill g q a

theorem Plains.fill_strip :
    ∀ {s : Shape} (g : GBits s) (pl : Plains (s.grind W g)),
      Plains.fill g (Plains.strip g pl) (Plains.nonces g pl) = pl
  | [], _, () => rfl
  | _ :: _, (_, g), (p, pl) => Prod.ext (GPlain.mk_old_nonce p) (Plains.fill_strip g pl)

theorem Plains.strip_fill :
    ∀ {s : Shape} (g : GBits s) (pl : Plains s) (ν : GNon W s),
      Plains.strip g (Plains.fill g pl ν) = pl
  | [], _, (), _ => rfl
  | _ :: _, (b, g), (p, pl), (ν, νs) => Prod.ext (GPlain.old_mk b p ν) (Plains.strip_fill g pl νs)


/-- Under the uniform distribution of the new verifier randomness the stripped randomness is
uniform. -/
theorem Rho.map_strip_unif :
    ∀ (s : Shape) (g : GBits s), (unif (Rho (s.grind W g))).map (Rho.strip g) = unif (Rho s)
  | [], _ => PMF.map_id _
  | r :: s, (b, g) =>
    map_unif_prodMap (Ω₁ := GChal b r.Chal) (Ω₂ := Rho (Shape.grind W s g)) (Y₁ := r.Chal)
      (Y₂ := Rho s) GChal.old (Rho.strip g) (GChal.map_old_unif b r.Chal) (Rho.map_strip_unif s g)

theorem prRho_strip {s : Shape} (g : GBits s) (S : Set (Rho s)) :
    prRho {ρ : Rho (s.grind W g) | Rho.strip g ρ ∈ S} = prRho S := by
  unfold prRho
  rw [← Rho.map_strip_unif (W := W) s g, pr_map]
  rfl

theorem grindUnif : Spec.grindUnif := fun _ _ _ g S => prRho_strip g S

/-! ## 3. Soundness -/

/-- If the prover is doomed towards `bad`, it is doomed in the protocol with proof-of-work bits,
with the same error counts, towards every goal that holds where such a bit is 1 and where `bad`
holds of the stripped transcript. In a round with b such bits: a challenge (c, z) with z ≠ 0 leads
to a prefix at which the prover is doomed for good; those with z = 0 are as many as the old
challenges. -/
theorem Doomed.grind :
    ∀ (s : Shape) (g : GBits s) (ε : Err s) {bad : Tr s → Prop} {bad' : Tr (s.grind W g) → Prop},
      (∀ τ, Rho.pass g τ.rho = false ∨ bad (Tr.strip g τ) → bad' τ) →
      Doomed s ε bad → Doomed (s.grind W g) (Err.grind g ε) bad'
  | [], _, _, _, _, h, hd => h () (Or.inr hd)
  | r :: s, (b, g), (e, ε), bad, bad', h, hd => fun m => by
      refine le_trans
        (cnt_mono (Q := fun c : GChal b r.Chal =>
              GChal.pass c = true ∧ ¬ Doomed s ε (fun τ => bad (Round.stripMsg m, GChal.old c, τ)))
          fun c hc => ?_)
        ((GChal.cnt_pass b _).le.trans (hd (Round.stripMsg m)))
      by_cases hp : GChal.pass c = true
      · refine ⟨hp, fun hd' => hc (Doomed.grind s g ε (fun τ hτ => h (m, c, τ) ?_) hd')⟩
        rcases hτ with hτ | hτ
        · left
          show (GChal.pass c && Rho.pass g τ.rho) = false
          rw [hτ, Bool.and_false]
        · exact Or.inr hτ
      · refine absurd (Doomed.of_forall _ _ fun τ => h (m, c, τ) (Or.inl ?_)) hc
        show (GChal.pass c && Rho.pass g τ.rho) = false
        rw [(Bool.not_eq_true _).mp hp, Bool.false_and]

variable {X : Type} {E : ExtSpec}

theorem InteractiveOracleProof.accept_grind (Q : InteractiveOracleProof X E) (g : GBits Q.shape) (x : X)
    (y : E.Str) (τ : Tr (Q.shape.grind W g)) :
    (Q.grind W g).accept x y τ = (Rho.pass g τ.rho && Q.accept x y (Tr.strip g τ)) := rfl

theorem InteractiveOracleProof.Sound.grind {Q : InteractiveOracleProof X E} {L : X → E.Str → Prop} {ε : Err Q.shape}
    (h : Q.Sound L ε) (g : GBits Q.shape) :
    (Q.grind W g).Sound L (Err.grind g ε) :=
  fun x y hxy => Doomed.grind Q.shape g ε (fun τ hτ => by
    rw [InteractiveOracleProof.accept_grind]
    rcases hτ with hτ | hτ
    · rw [hτ, Bool.false_and]
    · rw [hτ, Bool.and_false]) (h x y hxy)

theorem Err.below_grind_iff :
    ∀ {s : Shape} (g : GBits s) (ε : Err s) (c : ℝ≥0∞),
      Err.Below (Err.grind (W := W) g ε) c ↔ Err.BelowG g ε c
  | [], _, _, _ => Iff.rfl
  | r :: _, (b, g), (e, ε), c => by
      show ((e : ℝ≥0∞) ≤ c * (Fintype.card (GChal b r.Chal) : ℝ≥0∞) ∧
          Err.Below (Err.grind (W := W) g ε) c) ↔
        ((e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) ∧ Err.BelowG g ε c)
      rw [GChal.card_eq, Err.below_grind_iff g ε c, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, mul_comm (Fintype.card r.Chal : ℝ≥0∞)]

/-- The transformer never raises a bound: a bound on the old errors bounds the new ones, whatever
the numbers of proof-of-work bits. -/
theorem Err.BelowG.of_below :
    ∀ {s : Shape} (g : GBits s) {ε : Err s} {c : ℝ≥0∞}, Err.Below ε c → Err.BelowG g ε c
  | [], _, _, _, _ => trivial
  | _ :: _, (_, g), (_, _), _, h => by
      refine ⟨_root_.le_trans h.1 ?_, Err.BelowG.of_below g h.2⟩
      gcongr
      exact le_mul_of_one_le_left (_root_.zero_le _) (one_le_pow₀ (by norm_num))

/-! ## 4. Runs and acceptance -/

theorem Strat.strip_run_grind :
    ∀ {s : Shape} {β : Type} (g : GBits s) (σ : Strat s β)
        (n : NStrat W s g) (ρ : Rho (s.grind W g)),
      Tr.strip g ((Strat.grind g σ n).run ρ).1 = (σ.run (Rho.strip g ρ)).1
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (b, g), (m, k), (ν, n), (c, ρ) => by
      show (Round.stripMsg (Round.fillMsg b m ν),
          GChal.old c,
          Tr.strip g ((Strat.grind g (k (GChal.old c)) (n c)).run ρ).1) =
        (m, GChal.old c, ((k (GChal.old c)).run (Rho.strip g ρ)).1)
      rw [Round.strip_fillMsg, Strat.strip_run_grind g (k (GChal.old c)) (n c) ρ]

theorem Strat.snd_run_grind :
    ∀ {s : Shape} {β : Type} (g : GBits s) (σ : Strat s β)
        (n : NStrat W s g) (ρ : Rho (s.grind W g)),
      ((Strat.grind g σ n).run ρ).2 = (σ.run (Rho.strip g ρ)).2
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, g), (_, k), (_, n), (c, ρ) => Strat.snd_run_grind g (k (GChal.old c)) (n c) ρ

/-- With given nonces the plain parts of the run are the old ones with these nonces. -/
theorem Strat.plains_run_grind :
    ∀ {s : Shape} {β : Type} (g : GBits s) (σ : Strat s β) (ν : GNon W s) (ρ : Rho (s.grind W g)),
      ((Strat.grind g σ (NStrat.const g ν)).run ρ).1.plains =
        Plains.fill g (σ.run (Rho.strip g ρ)).1.plains ν
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (b, g), (m, k), (ν, νs), (c, ρ) =>
    congrArg (Prod.mk (GPlain.mk b m.2 ν)) (Strat.plains_run_grind g (k (GChal.old c)) νs ρ)

theorem InteractiveOracleProof.accept_run_grind (Q : InteractiveOracleProof X E) (g : GBits Q.shape) {β : Type} (σ : Strat Q.shape β)
    (n : NStrat W Q.shape g) (ρ : Rho (Q.shape.grind W g)) (x : X) (y : E.Str) :
    (Q.grind W g).accept x y ((Strat.grind g σ n).run ρ).1 =
      (Rho.pass g ρ && Q.accept x y (σ.run (Rho.strip g ρ)).1) := by
  rw [InteractiveOracleProof.accept_grind, Strat.rho_run, Strat.strip_run_grind]

variable {Q : InteractiveOracleProof X E} {Wt : Type}

theorem Honest.Acc.grind {H : Honest Q Wt} {valid : Wt → X → Prop} (h : H.Acc valid)
    (g : GBits Q.shape) (n : NStrat W Q.shape g) (w : Wt) (x : X) (c : H.Coin)
    (ρ : Rho (Q.shape.grind W g)) (hv : valid w x)
    (hρ : Rho.strip g ρ ∉ H.withheld w x) (hp : Rho.pass g ρ = true) :
    (Q.grind W g).accept x (H.ext w) ((Strat.grind g (H.strat w x c) n).run ρ).1 = true := by
  rw [InteractiveOracleProof.accept_run_grind, hp, h w x c _ hv hρ]
  rfl

theorem Honest.mem_withheld_grind (H : Honest Q Wt) (g : GBits Q.shape) (ν : GNon W Q.shape)
    (w : Wt) (x : X) (ρ : Rho (Q.shape.grind W g)) :
    ρ ∈ (H.grind g ν).withheld w x ↔ Rho.strip g ρ ∈ H.withheld w x := Iff.rfl

theorem Honest.prRho_withheld_grind
    (H : Honest Q Wt) (g : GBits Q.shape) (ν : GNon W Q.shape) (w : Wt) (x : X) :
    prRho ((H.grind g ν).withheld w x) = prRho (H.withheld w x) :=
  prRho_strip g (H.withheld w x)

/-! ## 5. Locality, views, the simulator -/

theorem InteractiveOracleProof.mem_reads_grind (g : GBits Q.shape) (x : X) (ρ : Rho (Q.shape.grind W g))
    (pl : Plains (Q.shape.grind W g)) (p : OPos (Q.shape.grind W g)) :
    p ∈ (Q.grind W g).reads x ρ pl ↔
    OPos.stripE g p ∈ Q.reads x (Rho.strip g ρ) (Plains.strip g pl) := by
  show p ∈ (Q.reads x (Rho.strip g ρ) (Plains.strip g pl)).map (OPos.stripE g).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

/-- The verifier reads as many positions as before. -/
theorem InteractiveOracleProof.card_reads_grind
    (g : GBits Q.shape) (x : X) (ρ : Rho (Q.shape.grind W g)) (pl : Plains (Q.shape.grind W g)) :
    ((Q.grind W g).reads x ρ pl).card = (Q.reads x (Rho.strip g ρ) (Plains.strip g pl)).card :=
  Finset.card_map _

theorem InteractiveOracleProof.IsLocal.grind (h : Q.IsLocal) (g : GBits Q.shape) : (Q.grind W g).IsLocal := by
  intro x y y' τ τ' hρ hpl hext hrd
  refine congrArg₂ (· && ·) (congrArg (Rho.pass g) hρ) ?_
  refine h x y y' (Tr.strip g τ) (Tr.strip g τ') ?_ ?_ ?_ ?_
  · rw [Tr.rho_strip, Tr.rho_strip]
    exact congrArg (Rho.strip g) hρ
  · rw [Tr.plains_strip, Tr.plains_strip]
    exact congrArg (Plains.strip g) hpl
  · intro p hp
    rw [Tr.rho_strip] at hp
    exact hext p hp
  · intro p hp
    rw [Tr.rho_strip, Tr.plains_strip] at hp
    obtain ⟨p', rfl⟩ := (OPos.stripE (W := W) g).surjective p
    rw [Tr.read_strip, Tr.read_strip]
    exact congrArg (OSym.strip g p') (hrd p' ((InteractiveOracleProof.mem_reads_grind g x _ _ p').2 hp))

theorem InteractiveOracleProof.extAns_grind (g : GBits Q.shape) (x : X) (ρ : Rho (Q.shape.grind W g)) (y : E.Str) :
    (Q.grind W g).extAns x ρ y = Q.extAns x (Rho.strip g ρ) y := rfl

theorem InteractiveOracleProof.dview_grind (g : GBits Q.shape) (x : X) (y : E.Str) (τ : Tr (Q.shape.grind W g)) :
    (Q.grind W g).dview x y τ =
      DView.fill g (Plains.nonces g τ.plains) (Q.dview x y (Tr.strip g τ)) := by
  have h1 : τ.plains = Plains.fill g (Tr.strip g τ).plains (Plains.nonces g τ.plains) := by
    rw [Tr.plains_strip, Plains.fill_strip]
  have h2 : (Q.grind W g).extAns x τ.rho y = Q.extAns x (Tr.strip g τ).rho y := by
    rw [Tr.rho_strip, InteractiveOracleProof.extAns_grind]
  have h3 : ((Q.grind W g).dview x y τ).orc =
      (DView.fill g (Plains.nonces g τ.plains) (Q.dview x y (Tr.strip g τ))).orc := by
    funext p
    have hiff : (p ∈ (Q.grind W g).reads x τ.rho τ.plains ∨ (Q.grind W g).blinded p = false) ↔
        (OPos.stripE g p ∈ Q.reads x (Tr.strip g τ).rho (Tr.strip g τ).plains ∨
          Q.blinded (OPos.stripE g p) = false) := by
      refine or_congr ?_ Iff.rfl
      rw [Tr.rho_strip, Tr.plains_strip]
      exact InteractiveOracleProof.mem_reads_grind g x τ.rho τ.plains p
    dsimp only [InteractiveOracleProof.dview, DView.fill]
    split_ifs with ha hb hb
    · exact congrArg some
        ((OSym.fill_strip g p (τ.read p)).symm.trans
          (congrArg (OSym.fill g p) (Tr.read_strip g τ p).symm))
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hb) ha
    · rfl
  show DView.mk τ.plains ((Q.grind W g).extAns x τ.rho y) ((Q.grind W g).dview x y τ).orc =
    DView.mk (Plains.fill g (Tr.strip g τ).plains (Plains.nonces g τ.plains))
      (Q.extAns x (Tr.strip g τ).rho y)
      (DView.fill g (Plains.nonces g τ.plains) (Q.dview x y (Tr.strip g τ))).orc
  rw [← h1, ← h2, ← h3]

/-- Only the plain parts of a filled view depend on the nonces. -/
theorem DView.fill_congr (g : GBits Q.shape) {ν ν' : GNon W Q.shape} (v : DView Q)
    (h : Plains.fill g v.plains ν = Plains.fill g v.plains ν') :
    DView.fill g ν v = DView.fill g ν' v := by
  show DView.mk (Q := Q.grind W g) (Plains.fill g v.plains ν) v.ext _ =
    DView.mk (Q := Q.grind W g) (Plains.fill g v.plains ν') v.ext _
  rw [h]

theorem InteractiveOracleProof.dview_run_grind (g : GBits Q.shape) (ν : GNon W Q.shape) {β : Type}
    (σ : Strat Q.shape β) (x : X) (y : E.Str) (ρ : Rho (Q.shape.grind W g)) :
    (Q.grind W g).dview x y ((Strat.grind g σ (NStrat.const g ν)).run ρ).1 =
      DView.fill g ν (Q.dview x y (σ.run (Rho.strip g ρ)).1) := by
  rw [InteractiveOracleProof.dview_grind, Strat.strip_run_grind]
  refine DView.fill_congr g _ ?_
  show Plains.fill g (σ.run (Rho.strip g ρ)).1.plains _ =
    Plains.fill g (σ.run (Rho.strip g ρ)).1.plains ν
  have h := Plains.fill_strip g ((Strat.grind g σ (NStrat.const g ν)).run ρ).1.plains
  rw [Strat.plains_run_grind, Plains.strip_fill] at h
  rw [Strat.plains_run_grind]
  exact h

theorem Honest.output_grind (H : Honest Q Wt) (g : GBits Q.shape) (ν : GNon W Q.shape) (w : Wt)
    (x : X) (ρ : Rho (Q.shape.grind W g)) :
    (H.grind g ν).output w x ρ =
      (H.output w x (Rho.strip g ρ)).map (Option.map (DView.fill g ν)) := by
  by_cases h : Rho.strip g ρ ∈ H.withheld w x
  · have e1 : (H.grind g ν).output w x ρ = PMF.pure none := if_pos h
    have e2 : H.output w x (Rho.strip g ρ) = PMF.pure none := if_pos h
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (H.grind g ν).output w x ρ =
        (unif H.Coin).map fun c =>
          some ((Q.grind W g).dview x (H.ext w)
                ((Strat.grind g (H.strat w x c) (NStrat.const g ν)).run ρ).1) := if_neg h
    have e2 : H.output w x (Rho.strip g ρ) =
        (unif H.Coin).map fun c =>
          some (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.strip g ρ)).1) := if_neg h
    rw [e1, e2, PMF.map_comp]
    congr 1
    funext c
    show some ((Q.grind W g).dview
          x (H.ext w) ((Strat.grind g (H.strat w x c) (NStrat.const g ν)).run ρ).1) =
      some (DView.fill g ν (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.strip g ρ)).1))
    rw [InteractiveOracleProof.dview_run_grind]

theorem grindSim : Spec.grindSim := fun _ _ _ _ _ _ H g ν Sim w x ρ => ⟨rfl, fun h => by
  rw [Honest.output_grind, h]
  rfl⟩

/-- If the old simulator is exact outside a set of probability at most z, so is `simGrind`, for the
prover that sends the nonces ν. -/
theorem simGrind_good {H : Honest Q Wt} (g : GBits Q.shape) (ν : GNon W Q.shape)
    (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) (w : Wt) (x : X)
    {z : ℝ≥0∞} (h : prRho {ρ | H.output w x ρ ≠ Sim x ρ (Q.extAns x ρ (H.ext w))} ≤ z) :
    prRho {ρ | (H.grind g ν).output w x ρ ≠
          simGrind g ν Sim x ρ ((Q.grind W g).extAns x ρ ((H.grind g ν).ext w))} ≤ z := by
  refine le_trans (pr_mono _ ?_) ((le_of_eq (prRho_strip g _)).trans h)
  intro ρ hρ heq
  exact hρ ((grindSim _ _ _ _ _ H g ν Sim w x ρ).2 heq)

/-- Honest-verifier zero knowledge in the exact form (`Honest.HVZK`) is preserved, with the same
number, for nonces ν given in advance. -/
theorem Honest.HVZK.grind {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    (g : GBits Q.shape) (ν : GNon W Q.shape) : (H.grind g ν).HVZK valid z :=
  let ⟨Sim, hS⟩ := h
  ⟨simGrind g ν Sim, fun w x hv => simGrind_good g ν Sim w x (hS w x hv)⟩

/-! ## 6. Oracles that are strings -/

/-- The oracle part of a round does not change. -/
def Round.IsPoint.grind {r : Round} (h : r.IsPoint) (b : ℕ) : (r.grind W b).IsPoint :=
  ⟨h.finPos, h.decPos, h.ofSyms, h.rd_ofSyms, h.ofSyms_rd, h.zero⟩

def Shape.IsPoint.grind : {s : Shape} → s.IsPoint → (g : GBits s) → (s.grind W g).IsPoint
  | [], _, _ => ()
  | _ :: _, (h, hs), (b, g) => (h.grind b, Shape.IsPoint.grind hs g)

end Iop
