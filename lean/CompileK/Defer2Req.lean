-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Req.lean: the hash tree over the slots' values of a batch, for the lemma on deferred
programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The library's request
tree (Compile/Batch/TokTree.lean: `rleafT`, `rleavesT`, `reqT`) obeys the discipline with joint
charges (CompileK/Defer2Safe.lean: `SafeO2`) at the vertex oracles, both children counting; and its
paths are closed upwards; each under the hypotheses of its statement.

Theorems `safe2_rleafT`, `safe2_rleavesT`, `safe2_reqT`: the analogues for `SafeO2` of
`safe_rleafT`, `safe_rleavesT`, `safe_reqT` (Compile/Batch/DisciplineReq.lean); `HeldAt.rnone`.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Against `safe_reqT` the end of `safe2_reqT`
has one clause more: every evaluation at a vertex oracle that holds a token beside or on the way
from a leaf to the root as a further token is charged to a token of that set (`rdeps_PA`,
CompileK/Defer2Tree.lean).

Why: the sets that a request tree gives to be shown are paths of a tree made by the same `levelsM`,
with `rnodeT`: so what holds of a tree over a message holds of them. A slot value is held at the
request trees' leaf oracle alone (the clause HeldAt .. (o = rleaf) of that end): so it is no
vertex's further token (`HeldAt.rnone`).

Limits: this file does not say where a request tree's path is shown (the finish).

Words used in this file. The discipline with joint charges, the vertex oracles, closed upwards: the
paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Tree
import Compile.Batch.DisciplineReq

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterMark length_afterMark cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ}

/-- a token that is held at oracles without joint charges only is no vertex's further token -/
theorem HeldAt.rnone {d : DSt (spec lam K L)} {t : Tok} {P : OracleName → Prop} (h : HeldAt d t P)
    (hP : ∀ o, P o → Jt o = false) {A : Tok → Prop} : RDep d t A :=
  fun e he hJ hb => by
    have := hP _ (h e he (Or.inr hb))
    rw [hJ] at this
    simp at this

/-- One leaf of a request tree. -/
theorem safe2_rleafT (c : Tok) (d : DSt (spec lam K L)) (hd : TidyBoth p mG d)
    (hc : Untouched d c) (hl : Len d c lam) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (rleafT (lam := lam) (K := K) (L := L) c) d fun dg d' =>
      TidyBoth p mG d' ∧
      Run (fun t => t = c) (fun t => t = c) NoTok zr (cnt1 OracleName.rleaf 1) d d' ∧
      dg = d.vals.length ∧
      Deps d' c [dg] ∧ HeldAt d' c (fun o => o = OracleName.rleaf) ∧ c ∉ d'.shown ∧
      Untouched d' dg ∧ Len d' dg lam := by
  have hus : ∀ u ∈ ([] : List Tok), u < d.vals.length := fun _ h => absurd h List.not_mem_nil
  have hbit : (rulesT K L lam p mG).bits OracleName.rleaf ≤ (d.val c).length := le_of_eq hl.2.symm
  have hmk : OracleName.rleaf ∈ osBG mG := osB_sub mG (by decide)
  have hJM : Jt OracleName.rleaf = true → JMark (ellT lam) d OracleName.rleaf c [] (fun v _ => (v : Bits)) :=
    fun h => by simp [Jt] at h
  refine ⟨hus, List.not_mem_nil, hc.freeAt _, hbit, hmk, hJM,
    fun r T =>
      ⟨⟨hd.1.mark hus List.not_mem_nil (hc.freeAt _) _ hbit hmk r T,
          Tidy2.mark hd.1 hd.2 hus (hc.freeAt _) hJM _ r T⟩,
        ?_, rfl,
        (hc.deps []).of_mark _ r T,
        ?_, hc.not_shown,
        Untouched.of_tail hd.1 hc.lt hus _ r T,
        Len.of_tail d _ c [] _ r T⟩⟩
  · exact (Run.ofMark (R := NoTok) (e := zr) d OracleName.rleaf c [] _ r T).mono (fun _ h => Or.inl h)
      (fun _ h => Or.inl (h.resolve_right List.not_mem_nil)) (fun _ h => Or.inl h)
      (fun _ => le_rfl) (fun _ => le_rfl)
  · exact fun e he hh =>
      ((hc.heldAt fun _ => False).of_mark OracleName.rleaf c [] _ r T e he hh).resolve_left id

/-- The leaves of a request tree. -/
theorem safe2_rleavesT :
    ∀ (cs : List Tok) (d : DSt (spec lam K L)), TidyBoth p mG d → Ready lam d cs →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (rleavesT (lam := lam) (K := K) (L := L) cs) d fun ls d' =>
      TidyBoth p mG d' ∧
      Run (fun t => t ∈ cs) (fun t => t ∈ cs) NoTok zr (cnt1 OracleName.rleaf cs.length) d d' ∧
      ls.length = cs.length ∧
      Ready lam d' ls ∧ (∀ c ∈ ls, d.vals.length ≤ c) ∧
      ∀ j < cs.length,
        Deps d' (cs.getD j 0) [ls.getD j 0] ∧
        HeldAt d' (cs.getD j 0) (fun o => o = OracleName.rleaf) ∧
        cs.getD j 0 ∉ d'.shown
  | [], d, hd, _ =>
    ⟨hd, Run.refl d, rfl, ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩,
      fun _ h => absurd h List.not_mem_nil, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | c :: t, d, hd, hr => by
      show SafeO2 _ _ _
        ((rleafT c).bind fun dg => (rleavesT t).bind fun r => Step.pure (dg :: r)) d _
      obtain ⟨hcu, hcl⟩ := hr.1 c List.mem_cons_self
      have hct : c ∉ t := (List.nodup_cons.mp hr.2).1
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_rleafT c d hd hcu hcl))
      rintro dg d₁ ⟨hd₁, hr₁, rfl, hdep, hheld, hns, hdu, hdl⟩
      have hrt : Ready lam d₁ t := ⟨fun a ha => by
        obtain ⟨h1, h2⟩ := hr.1 a (List.mem_cons_of_mem _ ha)
        exact ⟨h1.grows hr₁.grows (fun h => hct (h ▸ ha)) (fun h => h), h2.grows hr₁.grows⟩,
          (List.nodup_cons.mp hr.2).2⟩
      refine SafeO2.bind _ _ d₁ (SafeO2.mono ?_ _ d₁ (safe2_rleavesT t d₁ hd₁ hrt))
      rintro r d₂ ⟨hd₂, hr₂, hlen, hrd, hnew, hall⟩
      have hc₁ : c < d₁.vals.length := lt_of_lt_of_le hcu.lt hr₁.length_le
      have hdt : d.vals.length ∉ t := fun h =>
        absurd (hr.1 _ (List.mem_cons_of_mem _ h)).1.lt (lt_irrefl _)
      have hlt₁ : d.vals.length < d₁.vals.length := hdu.lt
      refine ⟨hd₂,
        (hr₁.mono (Cc := fun u => u ∈ c :: t) (Ch := fun u => u ∈ c :: t) (R := NoTok) (e := zr)
            (M := cnt1 OracleName.rleaf 1) (fun u hu => Or.inl (hu ▸ List.mem_cons_self))
            (fun u hu => Or.inl (hu ▸ List.mem_cons_self)) (fun _ h => Or.inl h)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₂ (fun u hu => Or.inl (List.mem_cons_of_mem _ hu))
          (fun u hu => Or.inl (List.mem_cons_of_mem _ hu)) (fun _ h => Or.inl h)
          (fun _ => le_rfl) (fun o => ?_),
        by simp [hlen], ⟨?_, ?_⟩, ?_, ?_⟩
      · exact le_of_eq (by rw [cnt1_add, List.length_cons, Nat.add_comm])
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨hdu.grows hr₂.grows hdt (fun h => h), hdl.grows hr₂.grows⟩
        · exact hrd.1 a ha
      · exact List.nodup_cons.mpr ⟨fun h => absurd (hnew _ h) (Nat.not_le.mpr hlt₁), hrd.2⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_rfl
        · exact le_trans hr₁.length_le (hnew a ha)
      · intro j hj
        cases j with
        | zero =>
          exact ⟨hdep.keeps hc₁ hr₂.charges hct,
            hheld.grows hc₁ hr₂.grows hct,
            not_shown_grows hc₁ hns hr₂.grows (fun h => h)⟩
        | succ j => exact hall j (Nat.lt_of_succ_lt_succ hj)

/-- The request tree over the slot values cs. -/
theorem safe2_reqT (depthReq : ℕ) (cs : List Tok) (d : DSt (spec lam K L))
    (hd : TidyBoth p mG d) (hlen : cs.length = 2 ^ depthReq)
    (hr : Ready lam d cs) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (reqT (lam := lam) (K := K) (L := L) depthReq cs) d fun rq d' =>
      TidyBoth p mG d' ∧
      Run (fun t => t ∈ cs) (fun t => t ∈ cs) NoTok zr
        (fun o => cnt1 OracleName.rleaf cs.length o + cnt1 OracleName.rnode cs.length o) d d' ∧
      (∀ j < cs.length,
        ∀ u ∈ PA rq.levels j, Deps d' u (PA rq.levels j) ∧ u < d'.vals.length ∧ d.vals.length ≤ u) ∧
      (∀ j < cs.length,
        Deps d' (cs.getD j 0) (PA rq.levels j) ∧
        HeldAt d' (cs.getD j 0) (fun o => o = OracleName.rleaf) ∧
        cs.getD j 0 ∉ d'.shown) ∧
      Untouched d' rq.root ∧ Len d' rq.root lam ∧ d.vals.length ≤ rq.root ∧
      (∀ j < cs.length, ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d' u) ∧
      (∀ j < cs.length, ∀ u ∈ PA rq.levels j, RDep d' u (fun c => c ∈ PA rq.levels j)) := by
  show SafeO2 _ _ _
    ((rleavesT cs).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
    d _
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_rleavesT cs d hd hr))
  rintro ls d₁ ⟨hd₁, hr₁, hl₁, hrd₁, hnew₁, hall₁⟩
  refine SafeO2.bind _ _ d₁
    (SafeO2.mono ?_ _ d₁
      (safe2_levelsT OracleName.rnode rnodeT (fun a b d => safe2_rnodeT a b d) depthReq ls d₁
        (hl₁.trans hlen) hd₁ hrd₁))
  rintro lv d₂ ⟨hd₂, hr₂, ⟨rest, rfl⟩, hlev, hmem, ⟨hru, hrl⟩, hrn, hseal, hLR⟩
  have hcs : ∀ j < cs.length, cs.getD j 0 < d.vals.length ∧ cs.getD j 0 ∉ ls := fun j hj => by
    have h1 := (hr.1 _ (getD_mem hj)).1.lt
    exact ⟨h1, fun h => absurd (hnew₁ _ h) (Nat.not_le.mpr h1)⟩
  have hge : ∀ u, (u ∈ ls ∨ d₁.vals.length ≤ u) → d.vals.length ≤ u := fun u hu => by
    rcases hu with hu | hu
    · exact hnew₁ u hu
    · exact le_trans hr₁.length_le hu
  refine ⟨hd₂,
    hr₁.trans hr₂ (fun u hu => Or.inr (hnew₁ u hu)) (fun u hu => Or.inr (hnew₁ u hu))
      (fun _ h => Or.inl h) (fun _ => le_rfl) (fun o => by rw [hl₁]),
    ?_, ?_, hru, hrl, hge _ hrn, ?_,
    fun j hj u hu => rdeps_PA d₂ (ls :: rest) j hlev hLR (hl₁ ▸ hj) u hu⟩
  · intro j hj u hu
    have hj' : j < ((ls :: rest).headD []).length := hl₁ ▸ hj
    obtain ⟨l', hl', hul'⟩ := exists_mem_of_mem_PA d₂ (ls :: rest) j hlev hj' u hu
    exact ⟨deps_PA d₂ (ls :: rest) j hlev hj' u hu,
      (hmem l' hl' u hul').1,
      hge u (hmem l' hl' u hul').2⟩
  · intro j hj
    obtain ⟨h1, h2, h3⟩ := hall₁ j hj
    obtain ⟨h4, h5⟩ := hcs j hj
    have h4' : cs.getD j 0 < d₁.vals.length := lt_of_lt_of_le h4 hr₁.length_le
    exact ⟨(h1.keeps h4' hr₂.charges h5).mono fun v hv => by
        rw [List.mem_singleton.mp hv]; exact head_mem_PA ls rest j,
      h2.grows h4' hr₂.grows h5,
      not_shown_grows h4' h3 hr₂.grows (fun h => h)⟩
  · intro j hj u hu
    obtain ⟨l', hl', hul'⟩ := exists_mem_of_mem_PA d₂ (ls :: rest) j hlev (hl₁ ▸ hj) u hu
    exact hseal l' hl' u hul'


end Compile.Batch.Disc
