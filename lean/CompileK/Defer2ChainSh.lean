-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2ChainSh.lean: the invariant between two rounds of the compiled prover, for the lemma
on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). What holds
between two rounds of the chains of a batch, both ways (`ChainInv2`: CompileK/Defer2Chain.lean), is
kept by a shared round without format (in `chainT`, Compile/Batch/Prover.lean, no Fiat-Shamir
evaluation is made in it), by a local round, and by a shared round in format (F5)
(Compile/Batch/Oracles.lean: `Head.f5`); each under the hypotheses of its statement.

Lemmas on states only: `ChainInv2.skip`, `ChainInv2.of_eachLo`, `ChainInv2.after_f5`. The analogue
of Compile/Batch/DisciplineChainSh.lean. Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.

Why, in `ChainInv2.after_f5`: every slot's set stays closed upwards when the shared chain's tries
add their tails and the shared tree's root to it: the reasons told at `SlotF2.after_tries`
(CompileK/Defer2Chain.lean).

Limits: This file gives no instance of `ChainInv2`, so as far as this file shows its theorems may
hold of nothing; it does not say whether the library has an instance elsewhere.

Words used in this file. Closed upwards, both ways: the paragraph "Words used in this file." of
CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Chain
import Compile.Batch.DisciplineChainSh

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterMark length_afterMark cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type}

section Pad2
variable {d : DSt (spec lam K L)}
  {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y}

theorem Trees02.pad (h : Trees02 d n₀ done a0.trees) (x : ℕ × ℕ) :
    Trees02 d n₀ (done ++ [x]) (a0.trees ++ [none]) :=
  forall₂_append (List.Forall₂.cons (fun _ h => by cases h) List.Forall₂.nil) h

/-- The shared part notes "no tree". -/
theorem SlotI2.pad0 (h : SlotI2 p d n₀ done ph a0 j acc) :
    SlotI2 p d n₀ done ph { a0 with trees := a0.trees ++ [none] } j acc := by
  have hiff : ∀ u,
      InU { a0 with trees := a0.trees ++ [none] } j acc u ↔ InU a0 j acc u := fun u => by
    unfold InU
    simp only [some_mem_append_none]
  refine ⟨⟨h.fin.cl.congr hiff fun _ _ hu => hu, h.fin.up.congr hiff,
      fun u hu => h.fin.new u ((hiff u).1 hu), h.fin.trees, h.fin.ne⟩,
    ?_, h.alive⟩
  have hc := h.cap
  cases ph <;> exact hc

/-- A slot notes "no tree", and blocks. -/
theorem SlotI2.padJ (h : SlotI2 p d n₀ done ph a0 j acc) (x : ℕ × ℕ) (bl : List (Blk lam K)) :
    SlotI2 p d n₀ (done ++ [x]) ph a0 j
      { acc with blocks := bl, trees := acc.trees ++ [none] } := by
  have hiff : ∀ u,
      InU a0 j { acc with blocks := bl, trees := acc.trees ++ [none] } u ↔
      InU a0 j acc u := fun u => by
    unfold InU
    simp only [some_mem_append_none]
  refine ⟨⟨h.fin.cl.congr hiff fun _ _ hu => ?_,
      h.fin.up.congr hiff,
      fun u hu => h.fin.new u ((hiff u).1 hu),
      forall₂_append (List.Forall₂.cons (fun _ h => by cases h) List.Forall₂.nil) h.fin.trees,
      h.fin.ne⟩,
    ?_, ?_⟩
  · cases ph <;> exact hu
  · have hc := h.cap
    cases ph <;> exact hc
  · have ha := h.alive
    cases ph <;> exact ha

end Pad2

section Rounds2
variable {r : Round} {s : Shape} {a : RAnn r} {d : DSt (spec lam K L)} {n₀ : ℕ}
  {done : List (ℕ × ℕ)} {ph : PhT} {a0 : Acc0}

/-- A shared round without format. -/
theorem ChainInv2.skip {zs : List (SlotSt lam K Y (r :: s))} (h : ChainInv2 p d n₀ done ph a0 zs)
    (_hph : ∀ tk0, ph ≠ PhT.shr tk0) (w : WireRB lam K r a) (bl : Blk lam K) (x : ℕ × ℕ) :
    ChainInv2 p d n₀ (done ++ [x]) ph { a0 with trees := a0.trees ++ [none] }
      (zs.map (hear (s := s) w bl false)) where
  slots := AllFrom.map _ (fun j z hz => by
    obtain ⟨⟨m, k⟩, acc⟩ := z
    exact (SlotI2.padJ hz x (acc.blocks ++ [bl])).pad0) 0 zs h.slots
  trees0 := h.trees0.pad x
  nodup := by
    rw [List.map_map]
    have e : ((fun z : SlotSt lam K Y s => live ph z.2) ∘ hear (s := s) w bl false) =
        fun z : SlotSt lam K Y (r :: s) => live ph z.2 :=
      funext fun z => live_hear w bl false ph z
    rw [e]
    exact h.nodup
  le := h.le
  shr := h.shr
  req := h.req

/-- After a local round in all slots. -/
theorem ChainInv2.of_eachLo {zs' : List (SlotSt lam K Y s)} {x : ℕ × ℕ}
    (hall : AllFrom (fun j z => SlotI2 p d n₀ (done ++ [x]) ph.afterLo a0 j z.2) 0 zs')
    (hnd : (zs'.map fun z => z.2.tk).Nodup) (h0 : Trees02 d n₀ done a0.trees)
    (hle : n₀ ≤ d.vals.length) (hreq : ph = PhT.first ∨ ph = PhT.loc → a0.req = none) :
    ChainInv2 p d n₀ (done ++ [x]) ph.afterLo { a0 with trees := a0.trees ++ [none] } zs' where
  slots := AllFrom.mono (fun _ _ hz => hz.pad0) 0 zs' hall
  trees0 := h0.pad x
  nodup := by
    have e : (fun z : SlotSt lam K Y s => live ph.afterLo z.2) = fun z => z.2.tk :=
      funext fun z => by cases ph <;> rfl
    rw [e]
    exact hnd
  le := hle
  shr := fun tk0 h => by cases ph <;> cases h
  req := fun h => by
    cases ph with
    | first => exact hreq (Or.inl rfl)
    | loc => exact hreq (Or.inr rfl)
    | shr tk0 => rcases h with h | h <;> cases h
    | aft => rcases h with h | h <;> cases h

/-- After a shared round in format (F5). d₁: the state after the tree over the shared component;
tr0: that tree, if the component has one; d': the state after all tries of the evaluation; nn: the
numbers of the kept tries of the shared rounds; dd: the tails of the failed tries; tl: the tail of
the kept try. -/
theorem ChainInv2.after_f5 {zs : List (SlotSt lam K Y (r :: s))} {tk0 : Tok}
    {d₁ : DSt (spec lam K L)} {M : OracleName → ℕ} {tr0 : Option TTree} (w : WireRB lam K r a)
    (h : ChainInv2 p d n₀ done (PhT.shr tk0) a0 zs) (hd : TidyBoth p mG d) (hd₁ : TidyBoth p mG d₁)
    (hr₁ : Run NoTok NoTok NoTok zr M d d₁) (htt : NewT2 d₁ d.vals.length w.depth0 tr0) (t : Tag)
    {n : ℕ} (nn : List ℕ) {dd : List Tok} {tl : Tok} {d' : DSt (spec lam K L)}
    (hd' : TidyBoth p mG d')
    (hT : Tries (split lam K L) tk0 (rtL tr0) d₁ (osTry t n) (dd.reverse ++ [tl]) d')
    (bl : Blk lam K) :
    ChainInv2 p d' n₀ (done ++ [(w.depthJ, w.depth0)]) (PhT.shr tl)
      { a0 with
        trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], nons := nn, dead := dd ++ a0.dead }
      (zs.map (hear (s := s) w bl false)) := by
  obtain ⟨hu0, hl0, ha0⟩ := h.shr tk0 rfl
  have hu0₁ : Untouched d₁ tk0 := hu0.grows hr₁.grows (fun x => x) (fun x => x)
  have hns : ¬ Sealed d₁ tk0 := hu0₁.not_sealed
  have hrun : Run (fun t' => t' = tk0) (fun t' => t' = tk0 ∨ t' ∈ rtL tr0) NoTok zr
      (fun o => (osTry t n).count o) d₁ d' := hT.run
  have ho : ∀ o ∈ osTry t n, ¬ Wk o := fun o hm => osTry_ne_rleaf t n o hm
  have hus : ∀ u ∈ rtL tr0, u < d₁.vals.length := fun u hu => htt.lt hu
  have hle₁ : n₀ ≤ d₁.vals.length := le_trans h.le hr₁.length_le
  have htl : d₁.vals.length ≤ tl :=
    hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  refine ⟨AllFrom.map _ (fun j z hz => ?_) 0 zs h.slots, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨⟨m, k⟩, acc⟩ := z
    have hz₁ : SlotI2 p d₁ n₀ done (PhT.shr tk0) a0 j acc :=
      SlotI2.frame hz hd hr₁ (fun _ hu => hu.elim) (fun x => x)
        (GJ.of_grows hr₁.grows) (fun _ hu => hu.elim)
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hz₁.cap
    have c0 : acc.c < d.vals.length := hz.cap.1
    have hcr : acc.c ∉ rtL tr0 := fun hu => absurd (htt.le hu) (Nat.not_le.mpr c0)
    have hiff : ∀ u,
        InU { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
              nons := nn, dead := dd ++ a0.dead }
          j { acc with blocks := acc.blocks ++ [bl], trees := acc.trees ++ [none] } u ↔
        (InU a0 j acc u ∨ u = tl ∨ u ∈ dd.reverse ∨ u ∈ rtL tr0) := fun u => by
      unfold InU
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
      constructor
      · rintro (h1 | (h1 | h1) | h1 | ⟨tr, h1 | h1, h2⟩ | h1 | h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨tr, h1, h2⟩))))
        · exact Or.inr (Or.inr (Or.inr (mem_rtL.2 ⟨tr, h1.symm, h2⟩)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
        · exact Or.inr (Or.inr (Or.inl (List.mem_reverse.mpr h1)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
      · rintro ((h1 | h1 | h1 | ⟨tr, h1, h2⟩ | h1 | h1 | h1) | h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tr, Or.inl h1, h2⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
        · exact Or.inr (Or.inl (Or.inr h1))
        · exact Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_reverse.mp h1)))))))
        · obtain ⟨tr, e, h2⟩ := mem_rtL.1 h1
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tr, Or.inr e.symm, h2⟩)))
    refine ⟨⟨?_, ?_, ?_, ?_, hz₁.fin.ne⟩, ?_, ?_⟩
    · refine (hz₁.fin.cl.extend_tries hd₁.1 (t := tk0) (us := rtL tr0) ho (fun u hu => ?_) hT).congr
        hiff fun u _ hu => ?_
      · exact ⟨htt.lt hu, Or.inr ((htt.unt hu).deps [])⟩
      · show (u = acc.c ∨ u = tl) ∨ Dead d' u
        rcases hu with hu | hu | ⟨(h1 | h1) | h1, h2, -⟩
        · exact Or.inl (Or.inr hu)
        · exact Or.inr hu
        · exact Or.inl (Or.inl h1)
        · exact absurd h1 h2
        · exact Or.inr (h1.mono hrun.keeps)
    · intro e he hJe b hb hV
      have he₀ : e ∈ d₁.evs := by
        rcases hT.mem_evs e he with he | ⟨_, _, _, hoo⟩
        · exact he
        · rw [osTry_notJ t n _ hoo] at hJe
          simp at hJe
      have hblt : b < d₁.vals.length := hd₁.1.others_lt e he₀ b hb
      rcases (hiff b).1 hV with h1 | h1 | h1 | h1
      · exact (hiff _).2 (Or.inl (hz₁.fin.up e he₀ hJe b hb h1))
      · exact absurd hblt (Nat.not_lt.mpr (h1 ▸ htl))
      · exact absurd hblt (Nat.not_lt.mpr (hT.tail_ge b (List.mem_append_left _ h1)))
      · exact absurd hb ((htt.unt h1).not_held e he₀).2
    · intro u hu
      rcases (hiff u).1 hu with h1 | h1 | h1 | h1
      · exact hz₁.fin.new u h1
      · exact h1 ▸ le_trans hle₁ htl
      · exact le_trans hle₁ (hT.tail_ge u (List.mem_append_left _ h1))
      · exact le_trans h.le (htt.le h1)
    · exact forall₂_append (List.Forall₂.cons (fun _ h => by cases h) List.Forall₂.nil)
        (hz₁.fin.trees.keeps hrun (fun u hu => hu ▸ hns)
          (hT.gj (osTry_notJ t n)) fun _ hu => hu.elim)
    · have hnc : ¬ (acc.c = tk0 ∨ acc.c ∈ rtL tr0) := fun hh => hh.elim c7 hcr
      exact ⟨lt_of_lt_of_le c1 hrun.length_le,
        not_shown_grows c1 c2 hrun.grows (fun x => x),
        c3.grows c1 hrun.grows hnc,
        c4.grows hrun.grows, c5,
        List.mem_append_right _ (List.mem_singleton.mpr rfl),
        Nat.ne_of_lt (lt_of_lt_of_le c1 htl)⟩
    · exact DeadW.keeps_not hz₁.alive hd₁.1 c1 hrun fun u hu => hu ▸ hns
  · exact forall₂_append
      (List.Forall₂.cons (htt.tts_tries h.le ho (osTry_notJ t n) hu0.lt (fun _ hu => hu) hT)
        List.Forall₂.nil)
      ((h.trees0.keeps hr₁ (fun _ hu => hu.elim) (GJ.of_grows hr₁.grows) fun _ hu => hu.elim).keeps
        hrun (fun u hu => hu ▸ hns) (hT.gj (osTry_notJ t n)) fun _ hu => hu.elim)
  · rw [List.map_map]
    have e : ((fun z : SlotSt lam K Y s => live (PhT.shr tl) z.2) ∘ hear (s := s) w bl false)
        = fun z : SlotSt lam K Y (r :: s) => live (PhT.shr tk0) z.2 := funext fun z => by
      obtain ⟨⟨m, k⟩, acc⟩ := z
      rfl
    rw [e]
    exact h.nodup
  · exact le_trans hle₁ hrun.length_le
  · intro tk0' he
    cases he
    exact ⟨hT.untouched_last hd₁.1 hu0₁.lt hus,
      hT.len_last (osTry_tl lam K L t n),
      hT.not_dead_last hd'.1⟩
  · intro he
    rcases he with he | he <;> cases he

end Rounds2


end Compile.Batch.Disc
