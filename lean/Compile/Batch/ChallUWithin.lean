-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ChallUWithin.lean: lemmas on runs of programs with tokens (Rom/Defer.lean): a program
that makes a token; the state after a reveal; the invariant `Spec.InvD` of
Compile/Batch/ChallU.lean.

  `Makes`, `Makes.run`, `makes_Cp`  Every path of the program makes a token; a run of such a program
                                    lengthens the list of strings; the committer's program is one
                                    (the salt of the chain of Test).
  `revealSt_eq`  The state after a reveal is `afterReveal` of Compile/SpecDiscipline.lean, for some
                 table.
  `tidy_of_none`, `invD_table`  Under `InvD`, before the setup the state is orderly (`TidyO`);
                                `InvD` does not depend on the table.

Limits: this file does not prove that a run against a challenger keeps the rules and the counts, and
gives no bound between the two modes. Nothing on what the two modes show. (The two modes: R and I,
Rom/Defer.lean; in this file: the argument m.)
-/
import Compile.Batch.ChallUHopR
import Compile.Batch.DisciplineChainAll

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt run_bind vals_prefix)
open Compile.Life2.WorldsX (dummy gap)
open Compile.Disc
  (Rules nEv afterReveal releaseAll_fst markDue markDue_charged markDue_tail markDue_others)
open Disc Disc.VirtO HopD

namespace WithinD

/-! ## Generic in the family of oracles -/

section Generic
variable {S : OSpec} {sp : Split S} {α β : Type}

/-- every path of the program makes a token -/
def Makes : Step S sp α → Prop
  | .pure _ => False
  | .sample _ k => ∀ r, Makes (k r)
  | .plain _ _ k => ∀ r, Makes (k r)
  | .fresh _ _ => True
  | .marked _ _ _ _ _ _ => True
  | .reveal _ k => ∀ vs, Makes (k vs)

theorem Makes.bind_left {c : Step S sp α} (g : α → Step S sp β) (h : Makes c) :
    Makes (c.bind g) := by
  induction c with
  | pure a => exact h.elim
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih => exact fun r => ih r (h r)
  | fresh ℓ k _ => trivial
  | marked o t us pt inj k _ => trivial
  | reveal ts k ih => exact fun vs => ih vs (h vs)

theorem Makes.bind_right (c : Step S sp α) {g : α → Step S sp β} (h : ∀ a, Makes (g a)) :
    Makes (c.bind g) := by
  induction c with
  | pure a => exact h a
  | sample n k ih => exact fun r => ih r
  | plain o q k ih => exact fun r => ih r
  | fresh ℓ k _ => trivial
  | marked o t us pt inj k _ => trivial
  | reveal ts k ih => exact fun vs => ih vs

/-- A run of a program with `Makes` makes the list of strings longer. -/
theorem Makes.run (m : Bool) {c : Step S sp α} :
    ∀ (d : DSt S), Makes c → ∀ x ∈ (c.run m d).support, d.vals.length < x.2.vals.length := by
  induction c with
  | pure a => exact fun _ h => h.elim
  | sample n k ih =>
    intro d h x hx
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r d (h r) x hr
  | plain o q k ih =>
    intro d h x hx
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨pr, -, hr⟩ := hx
    have h1 := ih pr.1 _ (h pr.1) x hr
    exact h1
  | fresh ℓ k _ =>
    intro d _ x hx
    rw [Step.run, PMF.mem_support_bind_iff] at hx
    obtain ⟨u, -, hr⟩ := hx
    have := (vals_prefix m _ _ x hr).length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  | marked o t us pt inj k _ =>
    intro d _ x hx
    rw [Step.run] at hx
    cases m with
    | true =>
      simp only [if_true] at hx
      rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hr⟩ := hx
      have := (vals_prefix true _ _ x hr).length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
    | false =>
      simp only [Bool.false_eq_true, if_false] at hx
      rw [PMF.mem_support_bind_iff] at hx
      obtain ⟨pr, -, hr⟩ := hx
      have := (vals_prefix false _ _ x hr).length_le
      simp only [List.length_append, List.length_singleton] at this
      omega
  | reveal ts k ih =>
    intro d h x hx
    rw [run_reveal] at hx
    have h1 := ih _ _ (h _) x hx
    exact h1

/-- the state after a reveal is `afterReveal` of Compile/SpecDiscipline.lean, at `releaseAll`'s
table -/
theorem revealSt_eq (m : Bool) (d : DSt S) (ts : List Tok) :
    revealSt m d ts = afterReveal d ts (releaseAll m (d.shown ++ ts) d.evs d.table).2 := by
  simp only [revealSt, afterReveal, releaseAll_fst]

end Generic

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- The committer's program makes a token: the salt of the Fiat-Shamir chain of Test. -/
theorem makes_Cp : Makes (Cp W WP p i) := by
  refine Makes.bind_right _ fun root => Makes.bind_left _ (Makes.bind_left _ ?_)
  refine Makes.bind_right _ fun c0 => Makes.bind_left _ ?_
  show Makes
    ((initSlot p.sFS (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) WP.T
      (i, root.r) c0 (some ())).bind _)
  exact Makes.bind_left _ (Makes.bind_right _ fun cj => trivial)

variable {W p}

/-- under `InvD`, before the setup the state is orderly -/
theorem tidy_of_none {d : DSt (spec lam W.K L)} (h : Spec.InvD W p none d) :
    TidyO (rulesB W.K L lam p) d := by
  rcases h with rfl | ⟨T, rfl⟩
  · exact TidyO.init
  · exact TidyO.init.table T

/-- `InvD` does not depend on the table -/
theorem invD_table (s : Option (IskH lam L × ℕ)) (d : DSt (spec lam W.K L))
    (T : Table (spec lam W.K L)) (h : Spec.InvD W p s d) :
    Spec.InvD W p s { d with table := T } := by
  rcases s with _ | ⟨k, N₀⟩
  · rcases h with rfl | ⟨T', rfl⟩
    · exact Or.inr ⟨T, rfl⟩
    · exact Or.inr ⟨T, rfl⟩
  · obtain ⟨h, h0⟩ := h
    exact ⟨⟨h.1.table T, WorldB.iskOK_of h.2.1 fun ts _ hc => ⟨hc.lt, hc.tail, hc.others⟩,
      ⟨h.2.2.1.len, h.2.2.1.tails, h.2.2.1.low, h.2.2.1.high⟩, h.2.2.2⟩, h0⟩

end WithinD

open WithinD


end Compile.Batch
