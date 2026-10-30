-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieRun.lean: ONE COMPILED RUN: THE TOKEN SIDE DOES WHAT THE COMPILED PROVER DOES:
the proof of Spec.sameRun (Johnson/TokenSide/SpecSame.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

How it goes: all hashing (hash_tie, Johnson/TokenSide/TieHash.lean); then no oracle is asked. Where
the chain has no value, or the test says stop, both sides give "none". Else the token side reveals
and calls the compiled prover's finish at the revealed values, and that is the compiled prover's
string (finish_eq, Johnson/TokenSide/TieFinish.lean), since every token whose value finish reads is
among those that are shown (mem_shownK, and the text of the list of what is shown).

Main names (namespace OnBytes.TokenSide).
  plainOf_revealsT_bind   as an ordinary algorithm a reveal whose values are dropped does nothing.
  mem_shownTree, mem_shownTrees, mem_shownK   the tokens of the leaf of a read position are shown.
  sameRun   THE THEOREM.

Limits. Those of Spec.sameRun (the head of Johnson/TokenSide/SpecSame.lean): all is said of the
erased program; one slot; wq.OKG,
CoversRun and ExtTie are premises, and of the first and the last no member is shown in this folder.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieHash
import Johnson.TokenSide.TieFinish
import OnBytes.Prover.Accept

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem plainOf_revealsT_bind {β : Type} (f : Unit → StT lam K L β) (vs : List Bits) :
    ∀ l : List (List Tok), plainOf ((revealsT (K := K) (L := L) l).bind f) vs = plainOf (f ()) vs
  | [] => rfl
  | _ :: l => plainOf_revealsT_bind f vs l

/-! ## What is shown -/

theorem mem_shownTree {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool) (T : TreeT lam L)
    (j : ℕ) (p : r.Pos) (hj : j < (T.lv.headD []).length) (hp : posAt j = some p)
    (hr : rd p = true) : T.toksAt j ∈ shownTree posAt rd T :=
  List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simp only [hp, hr]⟩, rfl⟩

theorem mem_shownTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) (j : ℕ)
    (p : r.Pos) (hr : rd p = true) :
    ∀ (Ts : List (TreeT lam L)) (k n : ℕ) (T : TreeT lam L), Ts[n]? = some T →
      j < (T.lv.headD []).length → posAt (k + n) j = some p →
      T.toksAt j ∈ shownTrees posAt rd k Ts
  | [], _, _, _, h, _, _ => by simp at h
  | T0 :: Ts, k, 0, T, h, hj, hp => by
    obtain rfl : T0 = T := by simpa using h
    exact List.mem_append_left _ (mem_shownTree (posAt k) rd T0 j p hj hp hr)
  | T0 :: Ts, k, n + 1, T, h, hj, hp =>
    List.mem_append_right _ (mem_shownTrees posAt rd j p hr Ts (k + 1) n T (by simpa using h) hj
      (by rwa [show k + 1 + n = k + (n + 1) by omega]))

theorem mem_shownK {ℓ : ℕ} (vs : List Bits) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ks : KeptT lam L s) (rd : OPos s → Bool),
      RoundsQueryLayout.OKG s A W → KeptOK ℓ s A W ks vs → ∀ p, rd p = true →
      ∀ u ∈ openT s A W ks p, ∃ c ∈ shownK s A W ks rd, u ∈ c
  | [], _, _, _, _, _, _, p, _, _, _ => nomatch p
  | _ :: s, (_, A), (_, W), (_, ks), rd, hW, hk, .inr q, hr, u, hu => by
    obtain ⟨c, hc, huc⟩ := mem_shownK vs s A W ks (fun p => rd (.inr p)) hW.2 hk.2.2 q hr u hu
    exact ⟨c, List.mem_append_right _ (List.mem_append_right _ hc), huc⟩
  | _ :: s, (a, A), (w, W), (kp, ks), rd, hW, hk, .inl p, hr, u, hu => by
    have hu' : u ∈ (match (if a.own p then kp.2.2 else kp.2.1)[w.tree p]? with
      | some T => T.toksAt (w.place p)
      | none => []) := hu
    cases hb : a.own p with
    | true =>
      rw [hb] at hu'
      simp only [if_true] at hu'
      cases hT : kp.2.2[w.tree p]? with
      | none =>
        rw [hT] at hu'
        exact absurd hu' (List.not_mem_nil)
      | some T =>
        rw [hT] at hu'
        have hts : TreesOK ℓ w.depthJ vs kp.2.2 := by
          rcases hk.2.1 with e | e
          · rw [e] at hT
            simp at hT
          · exact e
        obtain ⟨d, hd, hok⟩ := forall₂_get hts _ _ hT
        obtain ⟨d', hd', hlt⟩ := hW.1.place_ltJ p hb
        obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
        exact ⟨_, List.mem_append_left _ (mem_shownTrees w.posAtJ (fun p => rd (.inl p)) (w.place p)
          p hr kp.2.2 0 (w.tree p) T hT (by rw [hok.2.2]; exact hlt)
          (by rw [Nat.zero_add]; exact hW.1.posAtJ_place p hb)), hu'⟩
    | false =>
      rw [hb] at hu'
      simp only [Bool.false_eq_true, if_false] at hu'
      cases hT : kp.2.1[w.tree p]? with
      | none =>
        rw [hT] at hu'
        exact absurd hu' (List.not_mem_nil)
      | some T =>
        rw [hT] at hu'
        have hts : TreesOK ℓ w.depth0 vs kp.2.1 := by
          rcases hk.1 with e | e
          · rw [e] at hT
            simp at hT
          · exact e
        obtain ⟨d, hd, hok⟩ := forall₂_get hts _ _ hT
        obtain ⟨d', hd', hlt⟩ := hW.1.place_lt0 p hb
        obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
        exact ⟨_, List.mem_append_right _ (List.mem_append_left _ (mem_shownTrees w.posAt0
          (fun p => rd (.inl p)) (w.place p) p hr kp.2.1 0 (w.tree p) T hT
          (by rw [hok.2.2]; exact hlt) (by rw [Nat.zero_add]; exact hW.1.posAt0_place p hb))), hu'⟩

/-! ## The theorem -/

/-- **One compiled run: the token side does what the compiled prover does.** -/
theorem sameRun : Spec.sameRun := by
  intro I X lam K L t Y E Q wq embS embP xin cms x y xtK xt preX σ ln pre cap stop Ω μ Z rl vs hW hC
    hX
  show Tie μ _ _ (plainOf ((hashT t Q wq embS embP xin cms x σ ln pre cap).bind
    (endC Q wq x y xt preX pre stop)) vs) _
  rw [plainOf_bind]
  refine ((hash_tie t Q wq embS embP xin cms x σ pre cap rl vs hC).bind
    (f' := fun a => .pure (shown stop (a.1.map fun z =>
      (finish Q wq x y xtK a.2 z, trK Q.loc.shape z.2.1 z.1)))) fun p hp => ?_).congr fun ω => ?_
  swap
  · unfold proveX
    rw [Tie.obind_assoc, Tie.obind_assoc]
    refine congrArg _ (funext fun r => ?_)
    cases r <;> rfl
  obtain ⟨⟨salt, cd, r⟩, vs'⟩ := p
  obtain ⟨hp1, hp2, hp3⟩ := hp
  cases r with
  | noFormat => exact .done hp1 fun _ => rfl
  | ranOut j => exact .done hp1 fun _ => rfl
  | ok z =>
    obtain ⟨hK, hrq⟩ := hp3 z rfl
    show Tie μ _ _ (plainOf (if stop z.rho then Step.pure none
      else (finishC Q wq x y xt preX pre salt cd z).bind fun π => Step.pure (some π)) vs')
      (fun ω => .pure (if stop (trK Q.loc.shape
          (outW rl.leaf (fun i b => pre i b (vs'.getD salt [])) vs' 0 z ω).1.2.1 z.rho).rho then
              none
        else some (finish Q wq x y xtK (coinsK (vs'.getD salt []) cd)
          (outW rl.leaf (fun i b => pre i b (vs'.getD salt [])) vs' 0 z ω).1)))
    simp only [rho_trK]
    by_cases hs : stop z.rho = true
    · simp only [if_pos hs]
      exact .done hp1 fun _ => rfl
    · simp only [if_neg hs]
      have eP : plainOf ((finishC Q wq x y xt preX pre salt cd z).bind fun π =>
          Step.pure (some π)) vs' =
          .pure (some (finish Q wq x y
            (fun k => (xt k).toK (valOf (showC Q wq x xt salt z)
              ((showC Q wq x xt salt z).map fun u => vs'.getD u [])) preX)
            (coinsK (valOf (showC Q wq x xt salt z)
              ((showC Q wq x xt salt z).map fun u => vs'.getD u []) salt) cd)
            (outK (valOf (showC Q wq x xt salt z)
              ((showC Q wq x xt salt z).map fun u => vs'.getD u []))
              (fun i b => pre i b (valOf (showC Q wq x xt salt z)
                ((showC Q wq x xt salt z).map fun u => vs'.getD u []) salt)) z)), vs') := by
        rw [plainOf_bind]
        unfold finishC
        rw [plainOf_revealsT_bind]
        rfl
      rw [eP]
      have hval : ∀ u ∈ showC Q wq x xt salt z, valOf (showC Q wq x xt salt z)
          ((showC Q wq x xt salt z).map fun u => vs'.getD u []) u = vs'.getD u [] :=
        fun u hu => valOf_map (fun u => vs'.getD u []) _ u hu
      have hmem : ∀ c ∈ chunksT Q wq x xt salt z, ∀ u ∈ c, u ∈ showC Q wq x xt salt z :=
        fun c hc u hu => List.mem_flatten.mpr ⟨c, hc, hu⟩
      have hsalt : salt ∈ showC Q wq x xt salt z :=
        hmem _ (List.mem_cons_self ..) salt (List.mem_cons_self ..)
      refine .done hp1 fun ω => ?_
      rw [hval salt hsalt]
      refine congrArg (fun π => OComp.pure (some π)) ?_
      refine finish_eq rl.leaf Q wq x y xtK xt preX cd _ _ z vs vs' ω _ hW hK hC.2.2.2 hX hp1
        (fun u hu => hval u (hmem _ (List.mem_cons_self ..) u (List.mem_cons_of_mem _ (hrq u hu))))
        (fun p hp u hu => ?_) (fun p hp u hu => ?_)
      · obtain ⟨c, hc, huc⟩ := mem_shownK vs' Q.loc.shape Q.ann wq.sh z.kept (fun p =>
            haveI := wq.decO
            decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) hW.sh hK p
          (by
            letI := wq.decO
            exact decide_eq_true hp) u hu
        exact hval u (hmem c (List.mem_cons_of_mem _ (List.mem_append_left _ hc)) u huc)
      · refine hval u (hmem _ (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hW.ext.complete p, by
            letI := wq.ext.dec
            exact decide_eq_true hp⟩, rfl⟩))) u hu)

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.sameRun
