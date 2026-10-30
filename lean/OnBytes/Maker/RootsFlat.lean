-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RootsFlat.lean: the root under which the compiled verifier checks an opening at a
position of a file's stretch is the entry of the proof string's list of roots at the number of the
position's tree.

The compiled verifier's chain takes roots from the front of one list (OnBytes/TypedOracleCompiler/Joined/Roots.lean,
`RT.flat`) and keeps them round by round; the check of an opening climbs to the root that the wire
record and these roots give to the position (`treeOf`, OnBytes/TypedOracleCompiler/Joined/Clauses.lean). At the wire
records of OnBytes/Maker/Wire.lean a round takes one root for each of its trees, a silent round
none. So the roots of a stretch in a row are numbered as the stretch's trees are.

  `flat_lo`, `flat_sh`   a stretch of local, or of shared, rounds: as many roots in a row as trees,
                        and the root of a position is the entry at the number of its tree.
  `flat_behind`         a silent round in front adds no root.
  `flat_of_det`         what a chain has taken, in a row, is the front of the list that it was
                        given, from the chain's value under fixed oracle functions.
  `roots_of_three`      the three stretches of a file: the root of a position of stretch 1, 2, 3 is
                        the entry of the proof string's list of roots at the number of its tree over
                        the whole file.
  `rootsRead_of`        **`RootsRead` (OnBytes/Maker/WalksTree.lean) for the three stretches**, if
                        each opening of the tree number j over the whole file has walked to a root
                        whose digest is entry j of the proof string's list of roots (`hT`).

The premises of the last two: the three chains' values under g.

Not claimed. That an opening has walked to the root that was sent (the premise `hT` of `rootsRead_of`).
Nothing on soundness (index binding included), what a root fixes, opening-form binding, no two
openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.WalksTree
import OnBytes.TypedOracleCompiler.Joined.Roots

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening Tag)
open _root_.Run _root_.Run.PQ

section Stretch
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **A stretch of local rounds.** -/
theorem flat_lo :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)),
      RtFlagsAll (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R →
      SentK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) R →
      (RT.flat (uLT C ds) R).length = (ds.map (·.trees.length)).sum ∧
        ∀ q d c, treeOf (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R q =
            some (d, c) →
          (RT.flat (uLT C ds) R)[treeAt C ds q]? = some c
  | [], _, _, _ => ⟨rfl, fun q => nomatch q⟩
  | d0 :: ds, (rt, R), ⟨hf, hF⟩, ⟨h1, _, hK⟩ => by
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h1 rfl)
      have el : l.length = d0.trees.length := by
        have e : l.length = (d0.trees.map (·.a)).length := (hf.2 l hl).1
        rw [e, List.length_map]
      have eo : rt.1.getD [] = [] := by
        cases ho : rt.1 with
        | none => rfl
        | some y => exact List.eq_nil_of_length_eq_zero (hf.1 y ho).1
      obtain ⟨ihl, ih⟩ := flat_lo ds R hF hK
      have ef : RT.flat (uLT C (d0 :: ds)) (rt, R) = l ++ RT.flat (uLT C ds) R := by
        show rt.2.getD [] ++ rt.1.getD [] ++ RT.flat (uLT C ds) R = _
        rw [eo, hl]
        simp
      refine ⟨?_, fun q d c hq => ?_⟩
      · rw [ef, List.length_append, ihl, el]
        rfl
      · rw [ef]
        match q, hq with
        | .inl p, hq =>
          have hq' : TypedOracleCompiler.Joined.treeAt (d0.trees.map (·.a)) (rt.2.getD []) (treeT d0.trees p) =
              some (d, c) := hq
          rw [hl, ← treeIn_eq] at hq'
          have hc : l[treeIn d0.trees p]? = some c := (treeAt_eq_some hq').2
          show (l ++ RT.flat (uLT C ds) R)[treeIn d0.trees p]? = some c
          rw [List.getElem?_append_left (by rw [el]; exact treeIn_lt d0.trees p)]
          exact hc
        | .inr q', hq =>
          show (l ++ RT.flat (uLT C ds) R)[d0.trees.length + treeAt C ds q']? = some c
          rw [← el, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact ih q' d c hq

/-- **A stretch of shared rounds.** -/
theorem flat_sh :
    ∀ (ds : List RDT) (R : RootsOfChain 256 (uLT C ds)),
      RtFlagsAll (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) R →
      SentK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) R →
      (RT.flat (uLT C ds) R).length = (ds.map (·.trees.length)).sum ∧
        ∀ q d c, treeOf (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
            (wiresSh C K chal ds) R q = some (d, c) →
          (RT.flat (uLT C ds) R)[treeAt C ds q]? = some c
  | [], _, _, _ => ⟨rfl, fun q => nomatch q⟩
  | d0 :: ds, (rt, R), ⟨hf, hF⟩, ⟨_, h1, hK⟩ => by
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h1 rfl)
      have el : l.length = d0.trees.length := by
        have e : l.length = (d0.trees.map (·.a)).length := (hf.1 l hl).1
        rw [e, List.length_map]
      have eo : rt.2.getD [] = [] := by
        cases ho : rt.2 with
        | none => rfl
        | some y => exact List.eq_nil_of_length_eq_zero (hf.2 y ho).1
      obtain ⟨ihl, ih⟩ := flat_sh ds R hF hK
      have ef : RT.flat (uLT C (d0 :: ds)) (rt, R) = l ++ RT.flat (uLT C ds) R := by
        show rt.2.getD [] ++ rt.1.getD [] ++ RT.flat (uLT C ds) R = _
        rw [eo, hl]
        simp
      refine ⟨?_, fun q d c hq => ?_⟩
      · rw [ef, List.length_append, ihl, el]
        rfl
      · rw [ef]
        match q, hq with
        | .inl p, hq =>
          have hq' : TypedOracleCompiler.Joined.treeAt (d0.trees.map (·.a)) (rt.1.getD []) (treeT d0.trees p) =
              some (d, c) := hq
          rw [hl, ← treeIn_eq] at hq'
          have hc : l[treeIn d0.trees p]? = some c := (treeAt_eq_some hq').2
          show (l ++ RT.flat (uLT C ds) R)[treeIn d0.trees p]? = some c
          rw [List.getElem?_append_left (by rw [el]; exact treeIn_lt d0.trees p)]
          exact hc
        | .inr q', hq =>
          show (l ++ RT.flat (uLT C ds) R)[d0.trees.length + treeAt C ds q']? = some c
          rw [← el, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
          exact ih q' d c hq

/-- A silent round in front adds no root. -/
theorem flat_behind {T0 : Type} (t : T0) (a0 : RAnn (plainRound T0 t)) {s : Shape}
    (R : RootsOfChain 256 (plainRound T0 t :: s)) (hf : RtFlags (wireSilent (K + 1) T0 t a0) R.1) :
    RT.flat (plainRound T0 t :: s) R = RT.flat s R.2 := by
  obtain ⟨rt, R⟩ := R
  have e1 : rt.1.getD [] = [] := by
    cases ho : rt.1 with
    | none => rfl
    | some y => exact List.eq_nil_of_length_eq_zero (hf.1 y ho).1
  have e2 : rt.2.getD [] = [] := by
    cases ho : rt.2 with
    | none => rfl
    | some y => exact List.eq_nil_of_length_eq_zero (hf.2 y ho).1
  show rt.2.getD [] ++ rt.1.getD [] ++ RT.flat s R = RT.flat s R
  rw [e1, e2]
  rfl

end Stretch

/-- **What a chain has taken is the front of the list that it was given.** -/
theorem flat_of_det {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (typedOracleFamily lam K L)) (t : Tag)
    (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (z : Out lam s)
    (h : (recomputeChain (K := K) t cms x salt rtreq s A W embP i ph rts pls).det g = some z) :
    RT.flat s z.2.1 = rts.take (RootsOfChain.count s z.2.1) := by
  obtain ⟨tr, -, hr⟩ := runsIn_log' g (noCoin_chainB t cms x salt rtreq s A W embP i ph rts pls) h
  exact (flat_of_runsIn (ρ := z.1) (R := z.2.1) (ph' := z.2.2) hr).1

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) {I X : Type} {L : BatchProtocolWithLeafBody I X}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) {t : Tag}
  {embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)} {xin : Xi → Option X} {cms : List (Dig 256)}

/-- **The root of a position is the entry of the list of roots at the number of its tree over the
whole file.** -/
theorem roots_of_three (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (x : Xi)
    (a' : Out 256 (chainsOf C D tF tJ t3).c₁) (b' : Out 256 (chainsOf C D tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C D tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π a' b').det g = some e') :
    (∀ q d c, treeOf (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)) (wiresLo C K chal D.ds₁)
        a'.2.1.2 q = some (d, c) → π.roots[0 + treeAt C D.ds₁ q]? = some c) ∧
      (∀ q d c, treeOf (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
        (wiresSh C K chal D.ds₂) b'.2.1.2 q = some (d, c) →
        π.roots[D.t₁ + treeAt C D.ds₂ q]? = some c) ∧
      ∀ q d c, treeOf (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)) (wiresLo C K chal D.ds₃)
        e'.2.1.2 q = some (d, c) → π.roots[D.t₁ + D.t₂ + treeAt C D.ds₃ q]? = some c := by
  obtain ⟨F₁, K₁⟩ := flags₁_of_det g h₁
  obtain ⟨F₂, K₂⟩ := flags₂_of_det g h₂
  obtain ⟨F₃, K₃⟩ := flags₃_of_det g h₃
  have w1 : wire₁ (wqWhole C K chal D tF tJ t3 silent run) = _ :=
    wire₁_qb (wiresOf C K chal D tF tJ t3) _ _ _ _ _
  have w2 : wire₂ (wqWhole C K chal D tF tJ t3 silent run) = _ :=
    wire₂_qb (wiresOf C K chal D tF tJ t3) _ _ _ _ _
  have w3 : wire₃ (wqWhole C K chal D tF tJ t3 silent run) = _ :=
    wire₃_qb (wiresOf C K chal D tF tJ t3) _ _ _ _ _
  rw [w1] at F₁
  rw [w2] at F₂
  rw [w3] at F₃
  obtain ⟨n₁, r₁⟩ := flat_lo C K chal D.ds₁ a'.2.1.2 F₁.2 K₁.2.2
  obtain ⟨n₂, r₂⟩ := flat_sh C K chal D.ds₂ b'.2.1.2 F₂.2 K₂.2.2
  obtain ⟨n₃, r₃⟩ := flat_lo C K chal D.ds₃ e'.2.1.2 F₃.2 K₃.2.2
  have b₁ := flat_behind K tF _ a'.2.1 F₁.1
  have b₂ := flat_behind K tJ _ b'.2.1 F₂.1
  have b₃ := flat_behind K t3 _ e'.2.1 F₃.1
  have c₁ : RootsOfChain.count (chainsOf C D tF tJ t3).c₁ a'.2.1 = D.t₁ := by
    rw [← RT.length_flat, b₁, n₁]
    rfl
  have c₂ : RootsOfChain.count (chainsOf C D tF tJ t3).c₂ b'.2.1 = D.t₂ := by
    rw [← RT.length_flat, b₂, n₂]
    rfl
  have f₁ := flat_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ a' h₁
  have f₂ := flat_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ b' h₂
  have f₃ := flat_of_det g _ _ _ _ _ _ _ _ _ _ _ _ _ e' h₃
  rw [b₁] at f₁
  rw [b₂, c₁] at f₂
  rw [b₃, c₁, c₂] at f₃
  have take_some : ∀ (l : List (Dig 256)) (m n : ℕ) (c : Dig 256),
      (l.take m)[n]? = some c → l[n]? = some c := fun l m n c hc => by
    rw [List.getElem?_take] at hc
    split at hc
    · exact hc
    · cases hc
  refine ⟨fun q d c hq => ?_, fun q d c hq => ?_, fun q d c hq => ?_⟩
  · have := r₁ q d c hq
    rw [f₁] at this
    rw [Nat.zero_add]
    exact take_some _ _ _ _ this
  · have := r₂ q d c hq
    rw [f₂] at this
    have h' := take_some _ _ _ _ this
    rwa [List.getElem?_drop] at h'
  · have := r₃ q d c hq
    rw [f₃] at this
    have h' := take_some _ _ _ _ this
    rw [List.getElem?_drop, List.getElem?_drop, ← Nat.add_assoc] at h'
    exact h'

/-- **`RootsRead` for the three stretches**, if each opening of the tree number j over the whole
file has walked to a root whose digest is entry j of the proof string's list of roots. -/
theorem rootsRead_of (W : Three.Whole) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (x : Xi)
    (a' : Out 256 (chainsOf C D tF tJ t3).c₁) (b' : Out 256 (chainsOf C D tF tJ t3).c₂)
    (e' : Out 256 (chainsOf C D tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π).det g = some a')
    (h₂ : (run₂ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π a').det g = some b')
    (h₃ : (run₃ t (wholeDesc C D tF tJ t3 silent run) (wqWhole C K chal D tF tJ t3 silent run)
      embP xin cms x π a' b').det g = some e')
    (hT : ∀ j z, (j, z) ∈ ownRowsW W r → π.roots[j]? = some (bytesToDig z.2.2.root)) :
    RootsRead W r C D.ds₁ 0 (wiresLo C K chal D.ds₁) a'.2.1.2 ∧
      RootsRead W r C D.ds₂ D.t₁ (wiresSh C K chal D.ds₂) b'.2.1.2 ∧
      RootsRead W r C D.ds₃ (D.t₁ + D.t₂) (wiresLo C K chal D.ds₃) e'.2.1.2 := by
  obtain ⟨r₁, r₂, r₃⟩ := roots_of_three C K chal D tF tJ t3 silent run g π x a' b' e' h₁ h₂ h₃
  exact ⟨fun q d c z hq hz => Option.some.inj ((hT _ z hz).symm.trans (r₁ q d c hq)),
    fun q d c z hq hz => Option.some.inj ((hT _ z hz).symm.trans (r₂ q d c hq)),
    fun q d c z hq hz => Option.some.inj ((hT _ z hz).symm.trans (r₃ q d c hq))⟩

end File

end OnBytes.Maker
