-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/RunSome.lean: under fixed oracle functions the recomputation of a chain does
not fail, if the list of roots is long enough; and it takes as many roots as its rounds have trees.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


The verifier of a file recomputes its three chains (`recomputeChain`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). `recomputeChain` yields none in two cases only: a round's kind
does not fit the phase, or a root is missing (`takeRt`: the list is too short, or a component has
more than `maxRt` trees). Neither hangs on an answer of an oracle. So that a chain has a value, the
first three premises of "yes, cut by cut" (`CutsAt`, OnBytes/TypedOracleCompiler/Joined/YesByCutsMore.lean), wants
nothing of how typed queries are written as strings.

Main names:
  `sumJ`, `sum0`: the number of trees over the slot's components, over the shared components.
  `length_treesSB_lo`, `length_treesSB_sh`: these are the lengths of the table of trees
    (`treesSB`, OnBytes/TypedOracleCompiler/Joined/Wire.lean) over local rounds, and over shared rounds behind the
    joining round.
  `FewJ`, `Few0`: each such component has at most `maxRt` trees.
  `det_chainB_lo`: local rounds, from any phase (the first and the third chain).
  `det_chainB_sh`: shared rounds, from a phase behind the joining round.
  `det_chainB_join`: a joining round and then shared rounds, from a phase before it (the second
    chain).
  Each says: there is a value e, and `RootsOfChain.count` of its roots is the number of trees.

Limits: nothing on what the value is, beyond the count.

Terms: lean/GLOSSARY.md.
-/
import Rom.Cache
import Iop.JoinKit
import OnBytes.TypedOracleCompiler.Joined.Cut
import OnBytes.TypedOracleCompiler.Joined.Wire

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (TreeRef)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the number of trees over the slot's components of the rounds -/
def sumJ : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => w.depthJ.length + sumJ s A W

/-- the number of trees over the shared components of the rounds -/
def sum0 : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => w.depth0.length + sum0 s A W

/-- each slot's component has at most `maxRt` trees -/
def FewJ : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => w.depthJ.length ≤ maxRt ∧ FewJ s A W

/-- each shared component has at most `maxRt` trees -/
def Few0 : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => w.depth0.length ≤ maxRt ∧ Few0 s A W

/-- in local rounds the table of trees (`treesSB`, OnBytes/TypedOracleCompiler/Joined/Wire.lean) has `sumJ`
entries -/
theorem length_treesSB_lo : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (j : Bool),
    RoundSplits.AllKind .lo A → (treesSB s A W i j).length = sumJ s A W
  | [], _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), i, j, h => by
    rw [treesSB, h.1]
    show (refs i true w.depthJ.length ++ treesSB s A W (i + 1) j).length = _
    rw [List.length_append, length_treesSB_lo s A W (i + 1) j h.2]
    simp [refs, sumJ]

/-- in shared rounds behind the joining round it has `sum0` entries -/
theorem length_treesSB_sh : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ),
    RoundSplits.AllKind .sh A → (treesSB s A W i true).length = sum0 s A W
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), i, h => by
    rw [treesSB, h.1]
    show ([] ++ (refs i false w.depth0.length ++ treesSB s A W (i + 1) true)).length = _
    rw [List.nil_append, List.length_append, length_treesSB_sh s A W (i + 1) h.2]
    simp [refs, sum0]

theorem takeRt_of_le {n : ℕ} {rts : List (Dig lam)} (h1 : n ≤ maxRt) (h2 : n ≤ rts.length) :
    takeRt n rts = some (rts.take n, rts.drop n) := if_pos ⟨h1, h2⟩

/-- in a local round every phase has a format, with the slot's component -/
theorem actOf_lo (cms : List (Dig lam)) (x : Option X) (salt : Bits) (ph : Phase lam) :
    ∃ h next, actOf cms x salt .lo ph = some (.one h true next) := by
  cases ph <;> exact ⟨_, _, rfl⟩

section Det
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
  (rtreq : Dig lam)

/-- **Local rounds, from any phase.** -/
theorem det_chainB_lo :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains s),
      RoundSplits.AllKind .lo A → FewJ s A W → sumJ s A W ≤ rts.length →
      ∃ e, (recomputeChain t cms x salt rtreq s A W embP i ph rts pls).det g = some e ∧
        RootsOfChain.count s e.2.1 = sumJ s A W
  | [], _, _, _, _, ph, _, _, _, _, _ => ⟨((), (), ph), rfl, rfl⟩
  | r :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls), hk, hf, hn => by
    obtain ⟨h, next, hact⟩ := actOf_lo cms (x.map L.early) salt ph
    have hn' : w.depthJ.length + sumJ s A W ≤ rts.length := hn
    have htk := takeRt_of_le (rts := rts) hf.1 (by omega)
    have hlen : (rts.take w.depthJ.length).length = w.depthJ.length :=
      List.length_take_of_le (by omega)
    simp only [recomputeChain, hk.1, hact, htk]
    set ans := g (OracleName.fb t) (⟨i, h.withLate (lateInstancePart L i x), rts.take w.depthJ.length,
              embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t) with hans
    obtain ⟨e, he, hc⟩ := det_chainB_lo s A W (fun z => embP (.inr z)) (i + 1)
      (next (List.ofFn ans.2)) (rts.drop w.depthJ.length) pls hk.2 hf.2
      (by rw [List.length_drop]; omega)
    refine ⟨((w.chal ans.1, e.1), ((none, some (rts.take w.depthJ.length)), e.2.1), e.2.2), ?_, ?_⟩
    · show ((recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
        (next (List.ofFn ans.2)) (rts.drop w.depthJ.length) pls).bind _).det g = _
      rw [OComp.det_bind, he]
      rfl
    · show ([] : List (Dig lam)).length + (rts.take w.depthJ.length).length + RootsOfChain.count s e.2.1 =
        w.depthJ.length + sumJ s A W
      rw [hlen, hc, List.length_nil, Nat.zero_add]

/-- **Shared rounds, from a phase behind the joining round.** -/
theorem det_chainB_sh :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ρ0 : Bits) (c : Dig lam)
      (rts : List (Dig lam)) (pls : Plains s),
      RoundSplits.AllKind .sh A → Few0 s A W → sum0 s A W ≤ rts.length →
      ∃ e, (recomputeChain t cms x salt rtreq s A W embP i (.shr ρ0 c) rts pls).det g = some e ∧
        RootsOfChain.count s e.2.1 = sum0 s A W
  | [], _, _, _, _, ρ0, c, _, _, _, _, _ => ⟨((), (), .shr ρ0 c), rfl, rfl⟩
  | r :: s, (a, A), (w, W), embP, i, ρ0, c, rts, (pl, pls), hk, hf, hn => by
    have hn' : w.depth0.length + sum0 s A W ≤ rts.length := hn
    have htk := takeRt_of_le (rts := rts) hf.1 (by omega)
    have hlen : (rts.take w.depth0.length).length = w.depth0.length :=
      List.length_take_of_le (by omega)
    simp only [recomputeChain, hk.1, actOf, htk]
    set ans := g (OracleName.fb t) (⟨i, .f5 ρ0, rts.take w.depth0.length,
              embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t) with hans
    obtain ⟨e, he, hc⟩ := det_chainB_sh s A W (fun z => embP (.inr z)) (i + 1)
      (List.ofFn ans.2) c (rts.drop w.depth0.length) pls hk.2 hf.2
      (by rw [List.length_drop]; omega)
    refine ⟨((w.chal ans.1, e.1), ((some (rts.take w.depth0.length), none), e.2.1), e.2.2), ?_, ?_⟩
    · show ((recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
        (.shr (List.ofFn ans.2) c) (rts.drop w.depth0.length) pls).bind _).det g = _
      rw [OComp.det_bind, he]
      rfl
    · show (rts.take w.depth0.length).length + ([] : List (Dig lam)).length + RootsOfChain.count s e.2.1 =
        w.depth0.length + sum0 s A W
      rw [hlen, hc, List.length_nil, Nat.add_zero]

/-- **A joining round and then shared rounds, from a phase before the joining round.** The joining
round takes the roots of the slot's component and then those of the shared one. -/
theorem det_chainB_join {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ρ : Bits) (rts : List (Dig lam)) (pl : r.Plain) (pls : Plains s) (hk : a.kind = .sh)
    (hA : RoundSplits.AllKind .sh A) (hJ : w.depthJ.length ≤ maxRt) (h0 : w.depth0.length ≤ maxRt)
    (hf : Few0 s A W) (hn : w.depthJ.length + (w.depth0.length + sum0 s A W) ≤ rts.length) :
    ∃ e, (recomputeChain t cms x salt rtreq (r :: s) (a, A) (w, W) embP i (.loc ρ) rts (pl, pls)).det g =
        some e ∧
      RootsOfChain.count (r :: s) e.2.1 = w.depthJ.length + (w.depth0.length + sum0 s A W) := by
  have htJ := takeRt_of_le (rts := rts) hJ (by omega)
  have ht0 := takeRt_of_le (rts := rts.drop w.depthJ.length) h0
    (by rw [List.length_drop]; omega)
  have hlJ : (rts.take w.depthJ.length).length = w.depthJ.length :=
    List.length_take_of_le (by omega)
  have hl0 : ((rts.drop w.depthJ.length).take w.depth0.length).length = w.depth0.length :=
    List.length_take_of_le (by rw [List.length_drop]; omega)
  simp only [recomputeChain, hk, actOf, htJ, ht0]
  set c := g (OracleName.g t) (⟨i, ρ, rts.take w.depthJ.length,
            embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t) with hc
  set ans := g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn rtreq),
            (rts.drop w.depthJ.length).take w.depth0.length,
            embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t) with hans
  obtain ⟨e, he, hce⟩ := det_chainB_sh g t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
    (List.ofFn ans.2) c ((rts.drop w.depthJ.length).drop w.depth0.length) pls hA hf
    (by rw [List.length_drop, List.length_drop]; omega)
  refine ⟨((w.chal ans.1, e.1), ((some ((rts.drop w.depthJ.length).take w.depth0.length),
    some (rts.take w.depthJ.length)), e.2.1), e.2.2), ?_, ?_⟩
  · show ((recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
      (.shr (List.ofFn ans.2) c) ((rts.drop w.depthJ.length).drop w.depth0.length) pls).bind
        _).det g = _
    rw [OComp.det_bind, he]
    rfl
  · show ((rts.drop w.depthJ.length).take w.depth0.length).length +
      (rts.take w.depthJ.length).length + RootsOfChain.count s e.2.1 = _
    rw [hl0, hlJ, hce]
    omega

end Det

end TypedOracleCompiler.Joined
