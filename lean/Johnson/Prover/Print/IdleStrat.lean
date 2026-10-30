-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/IdleStrat.lean: AN IDLE STRATEGY OF A WHOLE FILE, WRITTEN, FOR ALL DATA: in the
front round, the joining round and the seam it sends three given plain parts; in every other round
the round's fixed message. It meets StratLaw (Johnson/Prover/Print/StratLaw.lean) at the run values
that it is given.

Why. StratLaw is a premise (lawT, lawB of LastFits, Johnson/Goal/Conditions/HomeLast.lean). Here is
a strategy that meets it: so the law is not one that no strategy can meet.

Main names.
  idleW   the strategy.
  idle_front, idle_tr₁, idle_msgJ, idle_tr₂, idle_msg3, idle_tr₃   its run, part by part.
  colT_zero, words_dflt, cols_dflt   the fixed messages' words are 0. (canonI_dflt, okF_zero:
    Johnson/Prover/Print/Member.lean; GPlain.old_mk: Iop/GrindProofs.lean.)
  stratLaw_idle   THE STATEMENT.

Limits. NOTHING ON ACCEPTANCE: no verifier is said to accept this strategy, and none is meant to.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.StratLaw
import Johnson.Prover.Print.Member
import Iop.ShapeKit
import Iop.GrindProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open _root_.Run.PQ (View SgX CK PlainOf Dn)
open Compile.Joined (JoinMsg Chains plainRound)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Maker
open OnBytes.Prover OnBytes.Prover.Print

/-! ## The fixed messages' words -/

theorem colT_zero : ∀ (ts : List _root_.Fmt.Shape) (p : TypedOracleCompiler.Run.PQ.PosT ts),
    ∀ w ∈ TypedOracleCompiler.Run.PQ.colT ts p (TypedOracleCompiler.Run.PQ.zeroT ts p), Carrier.okF w
  | _ :: _, .inl _, w, h => by
    obtain ⟨_, rfl⟩ := List.mem_ofFn.1 h
    exact okF_zero
  | _ :: ts, .inr p, w, h => colT_zero ts p w h

variable (C : CK)

theorem words_dflt : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    WordsP C ds ((Strat.dflt (uLT C ds) ()).run ρ).1.plains
  | [], _ => trivial
  | d :: ds, (_, ρ) => ⟨by
      show CanonI d.items (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items)
        (GPlain.mk d.entry.work (PlainOf.dflt d.items) default))
      rw [GPlain.old_mk]
      exact canonI_dflt _, words_dflt ds ρ⟩

theorem cols_dflt : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)) (q : OPos (uLT C ds)),
    ∀ w ∈ colOfSym C ds q (((Strat.dflt (uLT C ds) ()).run ρ).1.read q), Carrier.okF w
  | d :: _, (_, _), .inl p, w, h => colT_zero d.trees p w h
  | _ :: ds, (_, ρ), .inr q, w, h => cols_dflt ds ρ q w h

/-! ## The strategy -/

variable (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray)

/-- from the seam on -/
def idle3 (r3 : ByteArray) : Strat (chainsOf C D tF tJ t3).sh₃ Unit :=
  (((), r3), fun _ => Strat.dflt (uLT C D.ds₃) ())

/-- from the joining round on -/
def idleJ (j : JoinMsg (List OnBytes.E) ByteArray) (r3 : ByteArray) :
    Strat (chainsOf C D tF tJ t3).shJ Unit :=
  (((), j), fun _ => (Strat.dflt (uLT C D.ds₂) ()).bind fun _ => idle3 C D tF tJ t3 r3)

/-- **The idle strategy of a whole file.** -/
def idleW (f : FrontMsg (List OnBytes.E)) (j : JoinMsg (List OnBytes.E) ByteArray)
    (r3 : ByteArray) : Strat (chainsOf C D tF tJ t3).sh Unit :=
  (((), f), fun _ => (Strat.dflt (uLT C D.ds₁) ()).bind fun _ => idleJ C D tF tJ t3 j r3)

variable (f : FrontMsg (List OnBytes.E)) (j : JoinMsg (List OnBytes.E) ByteArray) (r3 : ByteArray)
  (ρ : Rho (chainsOf C D tF tJ t3).sh)

theorem idle_front : ((idleW C D tF tJ t3 f j r3).run ρ).1.1 = ((), f) := rfl

theorem idle_rest : ((idleW C D tF tJ t3 f j r3).run ρ).1.2.2 =
    Tr.app ((Strat.dflt (uLT C D.ds₁) ()).run (Rho.fst ρ.2)).1
      ((idleJ C D tF tJ t3 j r3).run (Rho.snd (s := uLT C D.ds₁) ρ.2)).1 := by
  show (((Strat.dflt (uLT C D.ds₁) ()).bind fun _ => idleJ C D tF tJ t3 j r3).run ρ.2).1 = _
  rw [Strat.run_bind]

theorem idle_tr₁ : (chainsOf C D tF tJ t3).tr₁ ((idleW C D tF tJ t3 f j r3).run ρ).1 =
    ((Strat.dflt (uLT C D.ds₁) ()).run (Rho.fst ρ.2)).1 := by
  unfold Chains.tr₁
  rw [idle_rest, Tr.fst_app]

theorem idle_trJ : (chainsOf C D tF tJ t3).trJ ((idleW C D tF tJ t3 f j r3).run ρ).1 =
    ((idleJ C D tF tJ t3 j r3).run (Rho.snd (s := uLT C D.ds₁) ρ.2)).1 := by
  unfold Chains.trJ
  rw [idle_rest, Tr.snd_app]

theorem idleJ_rest (ρJ : Rho (chainsOf C D tF tJ t3).shJ) :
    ((idleJ C D tF tJ t3 j r3).run ρJ).1.2.2 =
      Tr.app ((Strat.dflt (uLT C D.ds₂) ()).run (Rho.fst ρJ.2)).1
        ((idle3 C D tF tJ t3 r3).run (Rho.snd (s := uLT C D.ds₂) ρJ.2)).1 := by
  show (((Strat.dflt (uLT C D.ds₂) ()).bind fun _ => idle3 C D tF tJ t3 r3).run ρJ.2).1 = _
  rw [Strat.run_bind]

theorem idle_msgJ :
    (chainsOf C D tF tJ t3).msgJ ((idleW C D tF tJ t3 f j r3).run ρ).1 = ((), j) := by
  unfold Chains.msgJ
  rw [idle_trJ]
  rfl

theorem idle_tr₂ : ∃ ρ₂, (chainsOf C D tF tJ t3).tr₂ ((idleW C D tF tJ t3 f j r3).run ρ).1 =
    ((Strat.dflt (uLT C D.ds₂) ()).run ρ₂).1 := by
  unfold Chains.tr₂
  rw [idle_trJ, idleJ_rest, Tr.fst_app]
  exact ⟨_, rfl⟩

theorem idle_msg3 :
    (chainsOf C D tF tJ t3).msg3 ((idleW C D tF tJ t3 f j r3).run ρ).1 = ((), r3) := by
  unfold Chains.msg3
  rw [idle_trJ, idleJ_rest, Tr.snd_app]
  rfl

theorem idle_tr₃ : ∃ ρ₃, (chainsOf C D tF tJ t3).tr₃ ((idleW C D tF tJ t3 f j r3).run ρ).1 =
    ((Strat.dflt (uLT C D.ds₃) ()).run ρ₃).1 := by
  unfold Chains.tr₃
  rw [idle_trJ, idleJ_rest, Tr.snd_app]
  exact ⟨_, rfl⟩

/-- **The idle strategy meets the law**, at the run values that it is given. -/
theorem stratLaw_idle : StratLaw C D tF tJ t3 (idleW C D tF tJ t3 f j r3) j.run r3 where
  run2 := fun ρ => by rw [idle_msgJ]
  run3 := fun ρ => by rw [idle_msg3]
  words₁ := fun ρ => by
    rw [idle_tr₁]
    exact words_dflt C _ _
  words₂ := fun ρ => by
    obtain ⟨ρ₂, e⟩ := idle_tr₂ C D tF tJ t3 f j r3 ρ
    rw [e]
    exact words_dflt C _ _
  words₃ := fun ρ => by
    obtain ⟨ρ₃, e⟩ := idle_tr₃ C D tF tJ t3 f j r3 ρ
    rw [e]
    exact words_dflt C _ _
  cols₁ := fun ρ q => by
    rw [idle_tr₁]
    exact cols_dflt C _ _ q
  cols₂ := fun ρ q => by
    obtain ⟨ρ₂, e⟩ := idle_tr₂ C D tF tJ t3 f j r3 ρ
    rw [e]
    exact cols_dflt C _ _ q
  cols₃ := fun ρ q => by
    obtain ⟨ρ₃, e⟩ := idle_tr₃ C D tF tJ t3 f j r3 ρ
    rw [e]
    exact cols_dflt C _ _ q

end Johnson.Prover.Print
