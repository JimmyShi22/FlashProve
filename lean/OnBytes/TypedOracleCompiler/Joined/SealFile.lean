-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/SealFile.lean: a yes of the verifier of a file lays three joined chains into the
trace.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The verifier of a file walks three chains one after the other (`FileW.verify`,
OnBytes/TypedOracleCompiler/Joined/Verifier.lean). This file follows the phase of the walk through the three, and
so gets `Three` (OnBytes/TypedOracleCompiler/Joined/Seal.lean) for every yes: the first chain ends in the query to
g, whose answer is the slot value; the slot value stands at the slot's leaf under the binding root;
the binding root stands in the first query of the second chain; the first query of the third chain
holds the value in which the second ends, and the slot value.

Main names:
  `IsLoc`, `IsShr`, `IsAft`: in which stretch a chain stands.
  `vstep_lo`, `vstep_sh`: how one round moves the phase, by the round's kind.
  `loc_of_lo`, `aft_of_lo`, `shr_of_sh`: rounds of one kind keep the stretch.
  `three_of_file`: a yes of the verifier of a file, with all its queries in the trace, gives
    `Three`.

Limits: a statement on one trace; nothing on probability; nothing on the openings of trees. It asks
the law of the joining round's kind (`Chains.Laws`, Compile/Joined/Types.lean) and no law of the
wire record.

Terms: lean/GLOSSARY.md.

-/
import Iop.JoinKit
import OnBytes.TypedOracleCompiler.Joined.After
import OnBytes.TypedOracleCompiler.Joined.SealRun
import OnBytes.TypedOracleCompiler.Joined.Verifier

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile (Tag posOf RunsIn runsIn_pure_iff)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The stretch in which a chain stands -/

/-- the chain stands in its first local rounds, behind the first query -/
def IsLoc : Phase lam → Prop
  | .loc _ => True
  | _ => False

/-- the chain stands in the shared rounds -/
def IsShr : Phase lam → Prop
  | .shr _ _ => True
  | _ => False

/-- the chain stands in the local rounds behind the shared ones -/
def IsAft : Phase lam → Prop
  | .aft _ _ => True
  | _ => False

section Step
variable {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
  {tr : Trace (typedOracleFamily lam K L)} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
  {rtreq : Dig lam} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
  {pl : r.Plain} {ph ph₁ : Phase lam} {cur : Item lam L t} {ans : FsAns lam K}
  {rt : RtC lam × RtC lam}

/-- A local round leads from the start or the first local rounds into the first local rounds, and
from the shared rounds or the last local rounds into the last local rounds. -/
theorem vstep_lo (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    (hk : a.kind = .lo) :
    (ph = .first ∨ IsLoc ph → IsLoc ph₁) ∧ (IsShr ph ∨ IsAft ph → IsAft ph₁) := by
  cases h with
  | f1 root ans _ => exact ⟨fun _ => trivial, fun h => h.elim False.elim False.elim⟩
  | f2 ρ root ans _ => exact ⟨fun _ => trivial, fun h => h.elim False.elim False.elim⟩
  | join ρ rtj rt0 c ans hk' _ => exact absurd (hk.symm.trans hk') (by decide)
  | f5 ρ0 c root ans hk' => exact absurd (hk.symm.trans hk') (by decide)
  | f3 ρ0 c root ans _ => exact ⟨fun h => h.elim (fun e => by cases e) False.elim, fun _ => trivial⟩
  | f2' ρ c root ans _ => exact ⟨fun h => h.elim (fun e => by cases e) False.elim, fun _ => trivial⟩

/-- A shared round leads into the shared rounds. -/
theorem vstep_sh (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    (hk : a.kind = .sh) : IsShr ph₁ := by
  cases h with
  | f1 root ans hk' => exact absurd (hk.symm.trans hk') (by decide)
  | f2 ρ root ans hk' => exact absurd (hk.symm.trans hk') (by decide)
  | join ρ rtj rt0 c ans _ _ => trivial
  | f5 ρ0 c root ans _ => trivial
  | f3 ρ0 c root ans hk' => exact absurd (hk.symm.trans hk') (by decide)
  | f2' ρ c root ans hk' => exact absurd (hk.symm.trans hk') (by decide)

end Step

section Keep
variable {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
  {rtreq : Dig lam}

/-- Local rounds keep a chain in its first local rounds. -/
theorem loc_of_lo :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RoundSplits.AllKind .lo A → IsLoc ph →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      IsLoc ph'
  | [], _, _, _, _, ph, ph', _, _, _, _, _, hp, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hp
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), hA, hp, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      exact loc_of_lo s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hA.2
        ((vstep_lo hv hA.1).1 (Or.inr hp)) hr

/-- Local rounds keep a chain in its last local rounds. -/
theorem aft_of_lo :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RoundSplits.AllKind .lo A → IsAft ph →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      IsAft ph'
  | [], _, _, _, _, ph, ph', _, _, _, _, _, hp, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hp
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), hA, hp, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      exact aft_of_lo s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hA.2
        ((vstep_lo hv hA.1).2 (Or.inr hp)) hr

/-- Shared rounds keep a chain in the shared rounds. -/
theorem shr_of_sh :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      RoundSplits.AllKind .sh A → IsShr ph →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      IsShr ph'
  | [], _, _, _, _, ph, ph', _, _, _, _, _, hp, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hp
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), hA, _, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      exact shr_of_sh s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs hA.2 (vstep_sh hv hA.1) hr

end Keep

/-! ## A file -/

section File
variable {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type} {E : ExtSpec}

/-- **A yes of the verifier of a file lays three joined chains into the trace.** The first chain
starts at (F1) with our outer roots, instance and salt; the second at (F4) with our outer roots and
binding root; the slot value c stands at our slot's leaf under that root. -/
theorem three_of_file (F : FileW W G Y E) (hG : G.Laws) {sMT sFS : ℕ} {cms : List (Dig lam)} {x : Y}
    {π : F.Prf} {tr : Tc W} (hrun : RunsIn tr (F.verify sMT sFS cms x π) true) :
    ∃ v c q₁ l₁ qg q₂ l₂ ρ0 q₃ l₃,
      Three F.t tr (W.dReq F.t) π.slot q₁ l₁ qg c q₂ l₂ ρ0 q₃ l₃ v ∧
        q₁.head = .f1 cms ((F.xin x).map L.early) π.salt ∧
        q₂.head = .f4 cms (List.ofFn π.rtreq) := by
  obtain ⟨⟨⟨c₁, ρ₁⟩, ⟨rt₁, R₁⟩, p₁⟩, ⟨⟨c₂, ρ₂⟩, ⟨rt₂, R₂⟩, p₂⟩, ⟨⟨c₃, ρ₃⟩, ⟨rt₃, R₃⟩, p₃⟩, h₁, h₂,
    h₃, -, hA⟩ := (runsIn_verifyFile_iff sMT sFS F.t F.D F.wq F.embS F.embP F.xin F.embE
      (W.dReq F.t) cms x π).1 hrun
  -- what the three walks have laid into the trace
  have b₁ := behind_of_chainB _ _ _ _ _ .first p₁ _ _ _ _ trivial h₁
  have b₂ := behind_of_chainB _ _ _ _ _ p₁ p₂ _ _ _ _ b₁ h₂
  have b₃ := behind_of_chainB _ _ _ _ _ p₂ p₃ _ _ _ _ b₂ h₃
  -- the phases
  have k₁ : IsLoc p₁ := by
    obtain ⟨cur, ans, ph, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h₁
    exact loc_of_lo _ _ _ _ _ ph p₁ _ _ _ _ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.s₁)
      ((vstep_lo hv rfl).1 (Or.inl rfl)) hr
  have k₂ : IsShr p₂ := by
    obtain ⟨cur, ans, ph, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h₂
    exact shr_of_sh _ _ _ _ _ ph p₂ _ _ _ _ (RoundSplits.allKind_const .sh _ (fun _ => rfl) G.s₂)
      (vstep_sh hv hG.kindJ) hr
  have k₃ : IsAft p₃ := by
    obtain ⟨cur, ans, ph, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h₃
    exact aft_of_lo _ _ _ _ _ ph p₃ _ _ _ _ (RoundSplits.allKind_const .lo _ (fun _ => rfl) G.s₃)
      ((vstep_lo hv rfl).2 (Or.inl k₂)) hr
  cases p₃ with
  | first => exact k₃.elim
  | loc _ => exact k₃.elim
  | shr _ _ => exact k₃.elim
  | aft v c =>
    obtain ⟨q₁, l₁, qg, q₂, l₂, ρ0, q₃, l₃, e, hl, hg, e2, hl2, e3, hl3⟩ := b₃
    obtain ⟨_, _, _, _, hr, _⟩ :=
      (runsIn_afterBO_iff F.wq F.embS F.embE (W.dReq F.t) cms x π _ _ _).1 hA
    exact ⟨v, c, q₁, l₁, qg, q₂, l₂, ρ0, q₃, l₃,
      ⟨chainFields_f1 e, hl, hg,
        ⟨cms, π.rtreq, e2, opensIn_of_reqCheck ((runsIn_reqPart_iff (W.dReq F.t) π _).1 hr c rfl)⟩,
        hl2, e3, hl3⟩, e, e2⟩

end File

end TypedOracleCompiler.Joined
