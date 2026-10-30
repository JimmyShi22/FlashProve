-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineReq.lean: the request tree (the Merkle tree over the slot values of a batch)
obeys the rules of deferred programming, for 2^depthReq slot values with `Ready`, from a state with
`TidyO` (words of this library: lean/GLOSSARY.md).

For `Spec.safeProveB` (Compile/Batch/DisciplineStar.lean): `rleafT`, `rleavesT`, `reqT` of
Compile/Batch/TokTree.lean. The main lemma, `safe_reqT`, is for 2^depthReq slot values that are
untouched, of lam bits and different (`Ready`, Compile/Batch/DisciplineTree.lean), from an orderly
state (`TidyO`). A leaf is a marked query to `rleaf` that is charged to a slot value and holds
nothing else; its digest is a new token. The inner nodes are those of any token tree
(Compile/Batch/DisciplineTree.lean, with the oracle `rnode`). Afterwards a slot value depends on the
digests beside and on its path, is held at `rleaf` only (so it can still be charged at the
Fiat-Shamir oracle, format (F3): `Head`, Compile/Batch/Oracles.lean), and is not shown; the root is
untouched.
-/
import Compile.Batch.DisciplineTree

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterMark length_afterMark cnt1)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params}

/-- One leaf of a request tree. -/
theorem safe_rleafT (c : Tok) (d : DSt (spec lam K L)) (hd : TidyO (rulesB K L lam p) d)
    (hc : Untouched d c) (hl : Len d c lam) :
    SafeO (rulesB K L lam p) (rleafT (lam := lam) (K := K) (L := L) c) d fun dg d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun t => t = c) (fun t => t = c) NoTok zr (cnt1 OracleName.rleaf 1) d d' ∧
      dg = d.vals.length ∧
      Deps d' c [dg] ∧ HeldAt d' c (fun o => o = OracleName.rleaf) ∧ c ∉ d'.shown ∧
      Untouched d' dg ∧ Len d' dg lam := by
  have hus : ∀ u ∈ ([] : List Tok), u < d.vals.length := fun _ h => absurd h List.not_mem_nil
  have hbit : (rulesB K L lam p).bits OracleName.rleaf ≤ (d.val c).length := le_of_eq hl.2.symm
  have hmk : OracleName.rleaf ∈ osB ∨ ∃ t k, OracleName.rleaf = OracleName.fbw t k := Or.inl (by decide)
  refine ⟨hus, List.not_mem_nil, hc.freeAt _, hbit, hmk,
    fun r T =>
      ⟨hd.mark hus List.not_mem_nil (hc.freeAt _) _ hbit hmk r T, ?_, rfl,
        (hc.deps []).of_mark _ r T, ?_, hc.not_shown,
        Untouched.of_tail hd hc.lt hus _ r T, Len.of_tail d _ c [] _ r T⟩⟩
  · exact (Run.ofMark (R := NoTok) (e := zr) d OracleName.rleaf c [] _ r T).mono (fun _ h => Or.inl h)
      (fun _ h => Or.inl (h.resolve_right List.not_mem_nil)) (fun _ h => Or.inl h)
      (fun _ => le_rfl) (fun _ => le_rfl)
  · exact fun e he hh =>
      ((hc.heldAt fun _ => False).of_mark OracleName.rleaf c [] _ r T e he hh).resolve_left id

/-- The leaves of a request tree. -/
theorem safe_rleavesT : ∀ (cs : List Tok) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d → Ready lam d cs →
    SafeO (rulesB K L lam p) (rleavesT (lam := lam) (K := K) (L := L) cs) d fun ls d' =>
      TidyO (rulesB K L lam p) d' ∧
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
      show SafeO _ ((rleafT c).bind fun dg => (rleavesT t).bind fun r => Step.pure (dg :: r)) d _
      obtain ⟨hcu, hcl⟩ := hr.1 c List.mem_cons_self
      have hct : c ∉ t := (List.nodup_cons.mp hr.2).1
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_rleafT c d hd hcu hcl))
      rintro dg d₁ ⟨hd₁, hr₁, rfl, hdep, hheld, hns, hdu, hdl⟩
      have hrt : Ready lam d₁ t := ⟨fun a ha => by
        obtain ⟨h1, h2⟩ := hr.1 a (List.mem_cons_of_mem _ ha)
        exact ⟨h1.grows hr₁.grows (fun h => hct (h ▸ ha)) (fun h => h), h2.grows hr₁.grows⟩,
          (List.nodup_cons.mp hr.2).2⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_rleavesT t d₁ hd₁ hrt))
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

/-- Under `TidyO`, for 2^depthReq slot values cs with `Ready`: the request tree over the slot values
cs (`reqT`) obeys the rules and keeps `TidyO`; what holds afterwards is told in the head; beyond
that: it makes at most cs.length marked queries to `rleaf` and to `rnode` each and no ordinary one
(`Run`), and each token beside or on a path (`PA`) is new, depends on the tokens beside and on that
path (`Deps`), and is the root or sealed (`Sealed`, Compile/Batch/DisciplineTree.lean). -/
theorem safe_reqT (depthReq : ℕ) (cs : List Tok) (d : DSt (spec lam K L))
    (hd : TidyO (rulesB K L lam p) d) (hlen : cs.length = 2 ^ depthReq) (hr : Ready lam d cs) :
    SafeO (rulesB K L lam p) (reqT (lam := lam) (K := K) (L := L) depthReq cs) d fun rq d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun t => t ∈ cs) (fun t => t ∈ cs) NoTok zr
        (fun o => cnt1 OracleName.rleaf cs.length o + cnt1 OracleName.rnode cs.length o) d d' ∧
      (∀ j < cs.length,
        ∀ u ∈ PA rq.levels j, Deps d' u (PA rq.levels j) ∧ u < d'.vals.length ∧ d.vals.length ≤ u) ∧
      (∀ j < cs.length,
        Deps d' (cs.getD j 0) (PA rq.levels j) ∧
        HeldAt d' (cs.getD j 0) (fun o => o = OracleName.rleaf) ∧
        cs.getD j 0 ∉ d'.shown) ∧
      Untouched d' rq.root ∧ Len d' rq.root lam ∧ d.vals.length ≤ rq.root ∧
      (∀ j < cs.length, ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d' u) := by
  show SafeO _
    ((rleavesT cs).bind fun ls =>
      (levelsM rnodeT depthReq ls).bind fun lv => Step.pure (⟨lv, []⟩ : TTree))
    d _
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_rleavesT cs d hd hr))
  rintro ls d₁ ⟨hd₁, hr₁, hl₁, hrd₁, hnew₁, hall₁⟩
  refine SafeO.bind _ _ d₁
    (SafeO.mono ?_ _ d₁
      (safe_levelsT OracleName.rnode rnodeT safe_rnodeT depthReq ls d₁ (hl₁.trans hlen) hd₁ hrd₁))
  rintro lv d₂ ⟨hd₂, hr₂, ⟨rest, rfl⟩, hlev, hmem, ⟨hru, hrl⟩, hrn, hseal⟩
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
    ?_, ?_, hru, hrl, hge _ hrn, ?_⟩
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
