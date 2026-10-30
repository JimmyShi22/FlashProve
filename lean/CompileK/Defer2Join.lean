-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Join.lean: the compiled prover's joining round of a batch, in its slots
(Compile/Batch/Prover.lean: `gT`, `slotJoin`, `joinM`), obeys the discipline with joint charges
(CompileK/Defer2Safe.lean: `SafeO2`), and when the request tree enters the slots' sets of tokens
these stay closed upwards (CompileK/Defer2Slot.lean: `ClUp`); each under the hypotheses of its
statement.

One record and theorems, with proofs, for `safe2_chainT` (CompileK/Defer2ChainAll.lean). Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs. The
analogue of Compile/Batch/DisciplineJoin.lean (`MJ`, `accJ`, `AllFrom.map_idx`, `inU_req` are that
file's), whose head tells the round, for `SafeO2`.
Tokens, marked evaluations, charged and further tokens: the head of Rom/Defer.lean. The oracles with
joint charges are the vertex oracles `OracleName.node`, `OracleName.rnode` (CompileK/Defer2Tree.lean: `Jt`). Closed
upwards (`ClUp`): every evaluation at a vertex oracle with a further token in the set is charged
within the set. Open ends: the tokens of the slot that may still be charged (`OpenOf`,
Compile/Batch/DisciplineSlot.lean). The end of a statement on `SafeO2` is its last argument: what
the program leaves behind.

Main names:
  `safe2_slotJoin`, `safe2_joinM`: the round in one slot, in all slots, is `SafeO2`, under the
    hypotheses of their statements. Their ends have `JoinedI2` of each slot and the clause
    `GJ NoTok d d'` (CompileK/Defer2Kit.lean): every evaluation of d' at a vertex oracle is one of
    d, or its further tokens are new.
  `JoinedI2.after_req`: the slot's set with its request path and the request root is closed upwards,
    under the hypotheses of its statement.
  `SlotI2.after_f4`, `ChainInv2.after_join`: these records after the tries of the evaluation in
    format (F4) (Compile/Batch/Oracles.lean: `Head.f4`); that the sets stay closed upwards
    (`SlotF2.up`, CompileK/Defer2Slot.lean) has the reasons told at `SlotF2.after_tries`
    (CompileK/Defer2Chain.lean).

Why `JoinedI2.after_req`: take a vertex evaluation e of the state after the request tree with a
further token b in the set. b on or beside the path: e is charged within the path's set. b the root:
nothing holds it. b in the old set: e is old (the old set's closure), or new: then b is a slot
value, which only the request trees' leaf oracle holds, or a new token, which the old set has not.
Its premises hRcs, hRPA are what `safe2_reqT` (CompileK/Defer2Req.lean) leaves behind, hRcs by
`HeldAt.rnone`.

Limits: This file gives no instance of `ChainInv2`, so as far as this file shows its theorems may
hold of nothing; it does not say whether the library has an instance elsewhere.
-/
import CompileK.Defer2Chain
import Compile.Batch.DisciplineJoin

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type}

/-- `SlotF2.after_tries` (CompileK/Defer2Chain.lean) for one marked evaluation at an oracle without
joint charges, not `OracleName.rleaf`, under its other hypotheses: the loop with one try. -/
theorem SlotF2.after_mark {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {Op : Tok → Prop}
    {a0 : Acc0} {j : ℕ} {acc acc' : SlotAcc lam K Y} (hd : TidyBoth p mG d)
    (h : SlotF2 d n₀ done Op a0 j acc) {o : OracleName} (ho : o ≠ OracleName.rleaf) (hJ : Jt o = false) {t : Tok}
    {us : List Tok} {tr : Option TTree} {lo depth x : ℕ} (hn : n₀ ≤ lo) (hlo : lo ≤ d.vals.length)
    (ht : t < lo) (hts : ¬ Sealed d t) (hop : ∀ u, Op u → u = t ∨ u ∈ us)
    (hus : ∀ u ∈ us, u ∈ rtL tr ∨ u ∈ a0.toks) (hrm : ∀ u ∈ rtL tr, u ∈ us)
    (htr : NewT2 d lo depth tr) (htoks : acc'.toks = acc.toks ++ [d.vals.length])
    (htrees : acc'.trees = acc.trees ++ [tr]) (hdead : acc'.dead = acc.dead)
    (P : (spec lam K L).Dom o) (r : (spec lam K L).Rng o) (T : Table (spec lam K L)) :
    SlotF2 (afterMark (split lam K L) d o t us P r T) n₀ (done ++ [(depth, x)])
      (fun u => u = d.vals.length) a0 j acc' :=
  h.after_tries (dd := []) hd (os := [o]) (fun _ ho' => (List.mem_singleton.mp ho') ▸ ho)
    (fun _ ho' => (List.mem_singleton.mp ho') ▸ hJ) hn hlo ht hts hop hus hrm htr
    (Tries.one d o P r T) htoks htrees hdead

/-- a slot after g (`gT`: the evaluation at `OracleName.g t`): its slot value is its one open end, and is
untouched -/
structure JoinedI2 (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (a0 : Acc0)
    (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  fin : SlotF2 d n₀ done (fun u => u = acc.c) a0 j acc
  unt : Untouched d acc.c
  len : Len d acc.c lam
  mem : acc.c ∈ acc.toks
  alive : ¬ Dead d acc.c

theorem JoinedI2.frame {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {a0 : Acc0}
    {j : ℕ} {acc : SlotAcc lam K Y} {Cc Ch ChJ : Tok → Prop} {e M : OracleName → ℕ}
    (h : JoinedI2 d n₀ done a0 j acc) (hd : TidyBoth p mG d) (hr : Run Cc Ch NoTok e M d d')
    (hc : ∀ u, Cc u → Fit d u ∧ u ≠ acc.c) (hh : ¬ Ch acc.c) (hj : GJ ChJ d d')
    (hcj : ∀ u, ChJ u → ¬ Sealed d u ∧ ¬ InU a0 j acc u) : JoinedI2 d' n₀ done a0 j acc :=
  ⟨h.fin.keeps hr hc hj hcj,
    h.unt.grows hr.grows hh fun x => x,
    h.len.grows hr.grows,
    h.mem,
    DeadW.keeps_not h.alive hd.1 h.unt.lt hr fun u hu => (hc u hu).1.1⟩


theorem safe2_slotJoin {r : Round} {s : Shape} (t : Tag) (a : RAnn r) (w : WireRB lam K r a)
    (emb : (q : r.Pos) → r.Sym q → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (z : SlotSt lam K Y (r :: s)) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (a0 : Acc0) (j : ℕ) (hd : TidyBoth p mG d) (hn : n₀ ≤ d.vals.length)
    (h : SlotI2 p d n₀ done PhT.loc a0 j z.2) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (slotJoin p.sMT t a w emb plJ i z) d fun z' d' =>
      TidyBoth p mG d' ∧
      Run (fun u => u = z.2.tk) (fun u => u = z.2.tk) NoTok zr (MJ lam K L t w.depthJ) d d' ∧
      JoinedI2 d' n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z'.2 ∧
      d.vals.length ≤ z'.2.c ∧
      GJ NoTok d d' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  show SafeO2 _ _ _
    (withTree p.sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      gT t i acc.tk (tr.map TTree.root) (plJ (a.plain m.2).2) fun c =>
        Step.pure ((m, k), accJ acc c tr))
    d _
  refine safe2_withTree w.hasJ w.depthJ _ _ d hd _ fun tr d₁ hd₁ hr₁ htt => ?_
  have hI₁ : SlotI2 p d₁ n₀ done PhT.loc a0 j acc :=
    h.frame hd hr₁ (fun _ hu => hu.elim) (fun hu => hu)
      (GJ.of_grows hr₁.grows) (fun _ hu => hu.elim)
  obtain ⟨c1, c2, c3⟩ := hI₁.cap
  have hlt : acc.tk < d.vals.length := h.cap.1.lt
  have hus : ∀ u ∈ rtL tr, u < d₁.vals.length := fun u hu => htt.lt hu
  have htu : acc.tk ∉ rtL tr := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hlt)
  have hbit : (rulesT K L lam p mG).bits (OracleName.g t) ≤ (d₁.val acc.tk).length := le_of_eq c2.2.symm
  have hJg : Jt (OracleName.g t) = false := by simp [Jt]
  refine ⟨hus, htu, c1.freeAt _, hbit, osB_sub mG (g_mem_osB t),
    jmark_none hJg _ _ _, fun rr T => ?_⟩
  refine ⟨hd₁.markN hJg hus htu (c1.freeAt _) _ hbit (osB_sub mG (g_mem_osB t)) rr T,
    ?_,
    ⟨?_, Untouched.of_tail hd₁.1 c1.lt hus _ rr T,
      Len.of_tail d₁ (OracleName.g t) _ _ _ rr T,
      List.mem_append_right _ (List.mem_singleton.mpr rfl),
      not_deadW_last (hd₁.markN hJg hus htu (c1.freeAt _) _ hbit (osB_sub mG (g_mem_osB t)) rr T).1
        (le_of_eq (length_afterMark _ _ _ _ _ _ _))⟩,
    hr₁.length_le,
    (GJ.of_grows hr₁.grows).trans
      (Tries.gj (Tries.one d₁ (OracleName.g t) _ rr T) fun o ho => by
        rw [List.mem_singleton.1 ho]; exact hJg)
      fun _ hu => hu.elim⟩
  · refine (hr₁.mono (Cc := fun u => u = acc.tk) (Ch := fun u => u = acc.tk) (R := NoTok) (e := zr)
        (M := fun o => cnt1 OracleName.leaf (2 ^ w.depthJ) o + cnt1 OracleName.node (2 ^ w.depthJ) o)
        (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ => le_rfl)
        (fun _ => le_rfl)).trans
      (Run.ofMark (R := NoTok) (e := zr) d₁ (OracleName.g t) _ _ _ rr T) (fun _ hu => Or.inl hu)
      (fun u hu => ?_) (fun _ hu => hu.elim) (fun _ => le_rfl) (fun _ => le_rfl)
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (htt.le hu)
  · exact hI₁.fin.after_mark (acc' := accJ acc d₁.vals.length tr) (x := w.depth0) hd₁ (o := OracleName.g t)
      (by simp) hJg (t := acc.tk) (us := rtL tr) hn hr₁.length_le hlt c1.not_sealed
      (fun u hu => Or.inl hu) (fun u hu => Or.inl hu) (fun _ hu => hu) htt rfl rfl rfl _ rr T

theorem safe2_joinM {r : Round} {s : Shape} (t : Tag) (a : RAnn r)
    (w : WireRB lam K r a) (emb : (q : r.Pos) → r.Sym q → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (n₀ : ℕ) (done : List (ℕ × ℕ)) (a0 : Acc0) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (j : ℕ) (d : DSt (spec lam K L)),
      TidyBoth p mG d → n₀ ≤ d.vals.length →
    AllFrom (fun j z => SlotI2 p d n₀ done PhT.loc a0 j z.2) j zs → (zs.map fun z => z.2.tk).Nodup →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (joinM p.sMT t a w emb plJ i zs) d fun o d' =>
      TidyBoth p mG d' ∧
      Run (fun u => ∃ z ∈ zs, u = z.2.tk) (fun u => ∃ z ∈ zs, u = z.2.tk) NoTok zr
        (fun o => zs.length * MJ lam K L t w.depthJ o) d d' ∧
      AllFrom (fun j z => JoinedI2 d' n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z.2) j o.1 ∧
      o.2 = o.1.map (fun z => z.2.c) ∧
      o.2.Nodup ∧
      (∀ c ∈ o.2, d.vals.length ≤ c) ∧ o.1.length = zs.length ∧ GJ NoTok d d'
  | [], _, d, hd, _, _, _ =>
    ⟨hd, Run.refl d, trivial, rfl, List.nodup_nil,
      fun _ h => absurd h List.not_mem_nil, rfl, GJ.refl _ d⟩
  | z :: zs, j, d, hd, hn, hall, hnd => by
      show SafeO2 _ _ _ ((slotJoin p.sMT t a w emb plJ i z).bind fun z' =>
        (joinM p.sMT t a w emb plJ i zs).bind fun o => Step.pure (z' :: o.1, z'.2.c :: o.2)) d _
      have hnd' := List.nodup_cons.mp hnd
      have hne : ∀ x ∈ zs, z.2.tk ≠ x.2.tk := fun x hx he =>
        hnd'.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      refine SafeO2.bind _ _ d
        (SafeO2.mono ?_ _ d (safe2_slotJoin t a w emb plJ i z d n₀ done a0 j hd hn hall.1))
      rintro z' d₁ ⟨hd₁, hr₁, hJ', hnew, hj₁⟩
      have hall₁ : AllFrom (fun j z => SlotI2 p d₁ n₀ done PhT.loc a0 j z.2) (j + 1) zs :=
        AllFrom.mono_mem (j + 1) zs
          (fun j' x hx hIx =>
            hIx.frame hd hr₁ (fun u hu => hu ▸ ⟨hall.1.fit, hne x hx⟩) (fun hu => hne x hx hu.symm)
              hj₁ (fun _ hu => hu.elim)) hall.2
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁
          (safe2_joinM t a w emb plJ i n₀ done a0 zs (j + 1) d₁ hd₁
            (le_trans hn hr₁.length_le) hall₁ hnd'.2))
      rintro o d₂ ⟨hd₂, hr₂, hall₂, hmap₂, hnd₂, hnew₂, hlen₂, hj₂⟩
      have hold : ∀ x ∈ zs, x.2.tk < d.vals.length := fun x hx => by
        obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
        exact hIx0.cap.1.lt
      refine ⟨hd₂, ?_, ⟨?_, hall₂⟩, by simp [hmap₂], ?_, ?_,
        by simp [hlen₂], hj₁.trans hj₂ fun _ hu => hu.elim⟩
      · refine (hr₁.mono (Cc := fun u => ∃ x ∈ z :: zs, u = x.2.tk)
            (Ch := fun u => ∃ x ∈ z :: zs, u = x.2.tk) (R := NoTok) (e := zr)
            (M := MJ lam K L t w.depthJ) (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩)
            (fun u hu => Or.inl ⟨z, List.mem_cons_self, hu⟩) (fun _ hu => hu.elim)
            (fun _ => le_rfl) (fun _ => le_rfl)).trans
          hr₂ (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩)
          (fun u ⟨x, hx, hu⟩ => Or.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩) (fun _ hu => hu.elim)
          (fun _ => le_rfl) (fun o => ?_)
        rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
      · refine hJ'.frame hd₁ hr₂ (fun u ⟨x, hx, hu⟩ => ?_) (fun ⟨x, hx, hu⟩ => ?_)
          hj₂ (fun _ hu => hu.elim)
        · obtain ⟨j', hIx⟩ := AllFrom.of_mem (j + 1) zs hall₁ x hx
          exact hu ▸ ⟨hIx.fit, fun he => absurd hnew (Nat.not_le.mpr (he ▸ hold x hx))⟩
        · exact absurd hnew (Nat.not_le.mpr (hu ▸ hold x hx))
      · exact List.nodup_cons.mpr ⟨fun hm => absurd (hnew₂ _ hm) (Nat.not_le.mpr hJ'.unt.lt), hnd₂⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hnew
        · exact le_trans hr₁.length_le (hnew₂ c hc)


section Req2
variable {d₁ d₂ d₃ : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {a0 : Acc0} {j : ℕ}
  {acc : SlotAcc lam K Y} {cs : List Tok} {rq : TTree} {tr0 : Option TTree} {M₂ M₃ : OracleName → ℕ}


/-- The tokens of a slot after the request tree: with those beside and on its request path, and the
request root; the open ends are the slot value and the request root. Under the hypotheses below
`SlotF2` holds of them. -/
theorem JoinedI2.after_req (h : JoinedI2 d₁ n₀ done a0 j acc) (hn : n₀ ≤ d₁.vals.length)
    (hreq0 : a0.req = none) (hunt : ∀ x ∈ cs, Untouched d₁ x) (hal : ∀ x ∈ cs, ¬ Dead d₁ x)
    (hr₂ : Run (fun u => u ∈ cs) (fun u => u ∈ cs) NoTok zr M₂ d₁ d₂)
    (hPA : ∀ u ∈ PA rq.levels j,
      Deps d₂ u (PA rq.levels j) ∧ u < d₂.vals.length ∧ d₁.vals.length ≤ u)
    (hC : Deps d₂ acc.c (PA rq.levels j)) (hroot : Untouched d₂ rq.root)
    (hrnew : d₁.vals.length ≤ rq.root) (hsePA : ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d₂ u)
    (hRcs : ∀ x ∈ cs, RDep d₂ x (fun _ => False))
    (hRPA : ∀ u ∈ PA rq.levels j, RDep d₂ u (fun c => c ∈ PA rq.levels j)) :
    SlotF2 d₂ n₀ done (fun u => u = acc.c ∨ u = rq.root) { a0 with req := some rq } j acc := by
  refine ⟨⟨fun e he hV => ?_, fun u hu => ?_, fun u hu => ?_⟩,
    ?_, fun u hu => ?_,
    h.fin.trees.keeps hr₂ (fun u hu => (hunt u hu).not_sealed)
      (GJ.of_grows hr₂.grows) (fun u hu => (hunt u hu).not_sealed),
    h.fin.ne⟩
  · have inPA : ∀ {e : Ev (spec lam K L)},
      (e.tail ∈ PA rq.levels j ∧ ∀ v ∈ e.others, v ∈ PA rq.levels j) →
        InU { a0 with req := some rq } j acc e.tail ∧
        ∀ v ∈ e.others, InU { a0 with req := some rq } j acc v := fun hh =>
      ⟨(inU_req hreq0 _).2 (Or.inr (Or.inl hh.1)),
        fun v hv => (inU_req hreq0 _).2 (Or.inr (Or.inl (hh.2 v hv)))⟩
    rcases (inU_req hreq0 _).1 hV with h1 | h1 | h1
    · by_cases hc : e.charged = acc.c
      · exact inPA (hC e he hc)
      · rcases hr₂.charges.evs e he with ⟨e₀, he₀, a1, a2, a3⟩ | hcc | hnew
        · have := h.fin.cl.closed e₀ he₀ (a1 ▸ h1)
          exact ⟨(inU_req hreq0 _).2 (Or.inl (a3 ▸ this.1)),
            fun v hv => (inU_req hreq0 _).2 (Or.inl (this.2 v (a2 ▸ hv)))⟩
        · rcases h.fin.cl.sealed _ h1 with hs | hs | hs
          · exact absurd hs (hunt _ hcc).not_sealed
          · exact absurd hs hc
          · exact absurd hs (hal _ hcc)
        · exact absurd (h.fin.cl.lt _ h1) (Nat.not_lt.mpr hnew)
    · exact inPA ((hPA _ h1).1 e he rfl)
    · exact absurd h1 (hroot.not_held e he).1
  · rcases (inU_req hreq0 _).1 hu with h1 | h1 | h1
    · exact lt_of_lt_of_le (h.fin.cl.lt _ h1) hr₂.length_le
    · exact (hPA _ h1).2.1
    · exact h1 ▸ hroot.lt
  · rcases (inU_req hreq0 _).1 hu with h1 | h1 | h1
    · exact (h.fin.cl.sealed _ h1).imp (fun hs => hs.mono hr₂.keeps) fun ho =>
        ho.imp Or.inl fun hdd => hdd.mono hr₂.keeps
    · exact (hsePA _ h1).symm.imp_right fun e => Or.inl (Or.inr e)
    · exact Or.inr (Or.inl (Or.inr h1))
  · intro e he hJe b hb hV
    rcases (inU_req hreq0 _).1 hV with h1 | h1 | h1
    · rcases (GJ.of_grows hr₂.grows).evs e he hJe with ⟨e₀, he₀, ho, hc, hot⟩ | hnew
      · exact (inU_req hreq0 _).2
          (Or.inl (hc ▸ h.fin.up e₀ he₀ (by rw [ho]; exact hJe) b (by rw [hot]; exact hb) h1))
      · rcases hnew b hb with h2 | h2
        · exact (hRcs b h2 e he hJe hb).elim
        · exact absurd (h.fin.cl.lt _ h1) (Nat.not_lt.mpr h2)
    · exact (inU_req hreq0 _).2 (Or.inr (Or.inl (hRPA b h1 e he hJe hb)))
    · exact absurd hb (h1 ▸ (hroot.not_held e he).2)
  · rcases (inU_req hreq0 _).1 hu with h1 | h1 | h1
    · exact h.fin.new _ h1
    · exact le_trans hn (hPA _ h1).2.2
    · exact h1 ▸ le_trans hn hrnew

/-- A slot after the tries of the evaluation in format (F4). nn: the numbers of the kept tries of
the shared rounds; dd: the tails of the failed tries; tl: the tail of the kept try. -/
theorem SlotI2.after_f4 {acc' : SlotAcc lam K Y}
    (hF : SlotF2 d₃ n₀ done (fun u => u = acc.c ∨ u = rq.root) { a0 with req := some rq } j acc)
    (hd₃ : TidyBoth p mG d₃) (hn : n₀ ≤ d₃.vals.length) (hroot : Untouched d₃ rq.root)
    (hur : ∀ u ∈ rtL tr0, Untouched d₃ u) (hrn : ∀ u ∈ rtL tr0, n₀ ≤ u)
    (hclt : acc.c < d₃.vals.length) (hcs : acc.c ∉ d₃.shown) (hch : HeldAt d₃ acc.c Wk)
    (hcl : Len d₃ acc.c lam) (hcm : acc.c ∈ acc.toks) (hcr : acc.c ≠ rq.root)
    (hct : acc.c ∉ rtL tr0) (hca : ¬ Dead d₃ acc.c) (e1 : acc'.toks = acc.toks)
    (e2 : acc'.trees = acc.trees) (e3 : acc'.c = acc.c) (e4 : acc'.dead = acc.dead) (t : Tag)
    {n : ℕ} (nn : List ℕ) {dd : List Tok} {tl : Tok} {d' : DSt (spec lam K L)}
    (hT : Tries (split lam K L) rq.root (rtL tr0) d₃ (osTry t n) (dd.reverse ++ [tl]) d') :
    SlotI2 p d' n₀ done (PhT.shr tl)
      ⟨a0.trees ++ [tr0], a0.toks ++ [tl], some rq, nn, dd ++ a0.dead⟩ j acc' := by
  have hrun : Run (fun t' => t' = rq.root) (fun t' => t' = rq.root ∨ t' ∈ rtL tr0) NoTok zr
      (fun o => (osTry t n).count o) d₃ d' := hT.run
  have htl : d₃.vals.length ≤ tl :=
    hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hiff : ∀ u,
      InU ⟨a0.trees ++ [tr0], a0.toks ++ [tl], some rq, nn, dd ++ a0.dead⟩ j acc' u ↔
      (InU { a0 with req := some rq } j acc u ∨ u = tl ∨
        u ∈ dd.reverse ∨ u ∈ rtL tr0) := fun u => by
    unfold InU
    rw [e1, e2, e4]
    constructor
    · rintro (h1 | h1 | h1 | ⟨tr', h1, h2⟩ | h1 | h1 | h1)
      · exact Or.inl (Or.inl h1)
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inl (Or.inr (Or.inl h1))
        · exact Or.inr (Or.inl (List.mem_singleton.mp h1))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨tr', h1, h2⟩))))
        · exact Or.inr (Or.inr (Or.inr (mem_rtL.2 ⟨tr', (List.mem_singleton.mp h1).symm, h2⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))))
      · rcases List.mem_append.mp h1 with h1 | h1
        · exact Or.inr (Or.inr (Or.inl (List.mem_reverse.mpr h1)))
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))))
    · rintro ((h1 | h1 | h1 | ⟨tr', h1, h2⟩ | h1 | h1 | h1) | h1 | h1 | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl (List.mem_append_left _ h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨tr', List.mem_append_left _ h1, h2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_append_right _ h1))))))
      · exact Or.inr (Or.inl (List.mem_append_right _ (List.mem_singleton.mpr h1)))
      · exact Or.inr
          (Or.inr
            (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_append_left _ (List.mem_reverse.mp h1)))))))
      · obtain ⟨tr', e, h2⟩ := mem_rtL.1 h1
        exact Or.inr
          (Or.inr
            (Or.inr (Or.inl ⟨tr', List.mem_append_right _ (List.mem_singleton.mpr e.symm), h2⟩)))
  refine ⟨⟨?_, ?_, fun u hu => ?_, ?_, by rw [e1]; exact hF.ne⟩, ?_, ?_⟩
  · refine (hF.cl.extend_tries hd₃.1 (t := rq.root) (us := rtL tr0)
        (fun o ho => osTry_ne_rleaf t n o ho) (fun u hu => ?_) hT).congr
      hiff fun u _ hu => ?_
    · exact ⟨(hur u hu).lt, Or.inr ((hur u hu).deps [])⟩
    · show (u = acc'.c ∨ u = tl) ∨ Dead d' u
      rcases hu with hu | hu | ⟨(h1 | h1) | h1, h2, _⟩
      · exact Or.inl (Or.inr hu)
      · exact Or.inr hu
      · exact Or.inl (Or.inl (e3 ▸ h1))
      · exact absurd h1 h2
      · exact Or.inr (h1.mono hrun.keeps)
  · intro e he hJe b hb hV
    have he₀ : e ∈ d₃.evs := by
      rcases hT.mem_evs e he with he | ⟨_, _, _, hoo⟩
      · exact he
      · rw [osTry_notJ t n _ hoo] at hJe
        simp at hJe
    have hblt : b < d₃.vals.length := hd₃.1.others_lt e he₀ b hb
    rcases (hiff b).1 hV with h1 | h1 | h1 | h1
    · exact (hiff _).2 (Or.inl (hF.up e he₀ hJe b hb h1))
    · exact absurd hblt (Nat.not_lt.mpr (h1 ▸ htl))
    · exact absurd hblt (Nat.not_lt.mpr (hT.tail_ge b (List.mem_append_left _ h1)))
    · exact absurd hb ((hur b h1).not_held e he₀).2
  · rcases (hiff u).1 hu with h1 | h1 | h1 | h1
    · exact hF.new u h1
    · exact h1 ▸ le_trans hn htl
    · exact le_trans hn (hT.tail_ge u (List.mem_append_left _ h1))
    · exact hrn u h1
  · rw [e2]
    exact hF.trees.keeps hrun (fun u hu => hu ▸ hroot.not_sealed)
      (hT.gj (osTry_notJ t n)) fun _ hu => hu.elim
  · exact ⟨by rw [e3]; exact lt_of_lt_of_le hclt hrun.length_le,
      by rw [e3]; exact not_shown_grows hclt hcs hrun.grows fun x => x,
      by rw [e3]; exact hch.grows hclt hrun.grows (fun hh => hh.elim hcr hct),
      by rw [e3]; exact hcl.grows hrun.grows,
      by rw [e3, e1]; exact hcm,
      List.mem_append_right _ (List.mem_singleton.mpr rfl),
      by rw [e3]; exact Nat.ne_of_lt (lt_of_lt_of_le hclt htl)⟩
  · show ¬ Dead d' acc'.c
    rw [e3]
    exact DeadW.keeps_not hca hd₃.1 hclt hrun fun u hu => hu ▸ hroot.not_sealed

/-- Between the joining round and the next. The premises, but for hn, hreq0 and ht0 (from the
`ChainInv2` before the round), are what `joinM`, `reqT`, the tree over the shared component and the
tries of the evaluation in format (F4) leave behind. -/
theorem ChainInv2.after_join {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a)
    {zs₁ : List (SlotSt lam K Y (r :: s))}
    (hall : AllFrom (fun j z => JoinedI2 d₁ n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z.2) 0 zs₁)
    (hcs : cs = zs₁.map fun z => z.2.c) (hnd : cs.Nodup) (hn : n₀ ≤ d₁.vals.length)
    (hreq0 : a0.req = none) (ht0 : Trees02 d₁ n₀ done a0.trees) (hd₁ : TidyBoth p mG d₁)
    (hd₂ : TidyBoth p mG d₂) (hr₂ : Run (fun u => u ∈ cs) (fun u => u ∈ cs) NoTok zr M₂ d₁ d₂)
    (hPA : ∀ j < cs.length,
      ∀ u ∈ PA rq.levels j, Deps d₂ u (PA rq.levels j) ∧ u < d₂.vals.length ∧ d₁.vals.length ≤ u)
    (hC : ∀ j < cs.length,
      Deps d₂ (cs.getD j 0) (PA rq.levels j) ∧
      HeldAt d₂ (cs.getD j 0) (fun o => o = OracleName.rleaf) ∧
      cs.getD j 0 ∉ d₂.shown)
    (hroot : Untouched d₂ rq.root) (hrnew : d₁.vals.length ≤ rq.root)
    (hsePA : ∀ j < cs.length, ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d₂ u)
    (hRPA : ∀ j < cs.length, ∀ u ∈ PA rq.levels j, RDep d₂ u (fun c => c ∈ PA rq.levels j))
    (hd₃ : TidyBoth p mG d₃) (hr₃ : Run NoTok NoTok NoTok zr M₃ d₂ d₃)
    (htt : NewT2 d₃ d₂.vals.length w.depth0 tr0) (t : Tag) {n : ℕ} (nn : List ℕ) {dd : List Tok}
    {tl : Tok} {d' : DSt (spec lam K L)} (hd' : TidyBoth p mG d')
    (hT : Tries (split lam K L) rq.root (rtL tr0) d₃ (osTry t n) (dd.reverse ++ [tl]) d')
    (bl : Blk lam K) :
    ChainInv2 p d' n₀ (done ++ [(w.depthJ, w.depth0)]) (PhT.shr tl)
      ⟨a0.trees ++ [tr0], a0.toks ++ [tl], some rq, nn, dd ++ a0.dead⟩
      (zs₁.map (hear w bl true)) := by
  have hrun : Run (fun t' => t' = rq.root) (fun t' => t' = rq.root ∨ t' ∈ rtL tr0) NoTok zr
      (fun o => (osTry t n).count o) d₃ d' := hT.run
  have hunt : ∀ x ∈ cs, Untouched d₁ x := fun x hx => by
    rw [hcs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 zs₁ hall z hz
    exact hJ.unt
  have hal : ∀ x ∈ cs, ¬ Dead d₁ x := fun x hx => by
    rw [hcs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 zs₁ hall z hz
    exact hJ.alive
  have hRcs : ∀ x ∈ cs, RDep d₂ x (fun _ => False) := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have h2 := (hC i hi).2.1
    have e : cs.getD i 0 = cs[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [e] at h2
    exact h2.rnone fun o ho => by rw [ho]; simp [Jt]
  have hroot₃ : Untouched d₃ rq.root := hroot.grows hr₃.grows (fun h => h) (fun h => h)
  have hn₂ : n₀ ≤ d₂.vals.length := le_trans hn hr₂.length_le
  have hn₃ : n₀ ≤ d₃.vals.length := le_trans hn₂ hr₃.length_le
  have hus : ∀ u ∈ rtL tr0, u < d₃.vals.length := fun u hu => htt.lt hu
  refine ⟨?_, ?_, ?_, le_trans hn₃ hrun.length_le, ?_, ?_⟩
  · refine AllFrom.map_idx (hear w bl true) zs₁ 0 hall fun i hi hJ => ?_
    have hi' : i < cs.length := by rw [hcs, List.length_map]; exact hi
    have hci : cs.getD i 0 = zs₁[i].2.c := by
      rw [hcs]
      simp [List.getD_eq_getElem?_getD, hi]
    rw [Nat.zero_add] at hJ ⊢
    obtain ⟨c1, c2, c3⟩ := hC i hi'
    rw [hci] at c1 c2 c3
    have hPAi := hPA i hi'
    have hsei := hsePA i hi'
    generalize zs₁[i] = z at hJ c1 c2 c3 ⊢
    obtain ⟨⟨m, k⟩, acc⟩ := z
    have hclt₁ : acc.c < d₁.vals.length := hJ.unt.lt
    have hclt₂ : acc.c < d₂.vals.length := lt_of_lt_of_le hclt₁ hr₂.length_le
    exact SlotI2.after_f4 (acc' := (hear w bl true ((m, k), acc)).2)
      ((hJ.after_req hn hreq0 hunt hal hr₂ hPAi c1 hroot hrnew hsei hRcs (hRPA i hi')).keeps
        hr₃ (fun _ h => h.elim) (GJ.of_grows hr₃.grows) (fun _ h => h.elim))
      hd₃ hn₃ hroot₃ (fun _ hu => htt.unt hu) (fun _ hu => le_trans hn₂ (htt.le hu))
      (lt_of_lt_of_le hclt₂ hr₃.length_le) (not_shown_grows hclt₂ c3 hr₃.grows fun h => h)
      (c2.grows hclt₂ hr₃.grows fun h => h) ((hJ.len.grows hr₂.grows).grows hr₃.grows) hJ.mem
      (Nat.ne_of_lt (lt_of_lt_of_le hclt₁ hrnew))
      (fun hu => absurd (htt.le hu) (Nat.not_le.mpr hclt₂))
      (DeadW.keeps_not (DeadW.keeps_not hJ.alive hd₁.1 hclt₁ hr₂ fun u hu => (hunt u hu).not_sealed)
        hd₂.1 hclt₂ hr₃ fun _ h => h.elim)
      rfl rfl rfl rfl t nn hT
  · exact forall₂_append
      (List.Forall₂.cons
        (htt.tts_tries hn₂ (fun o ho => osTry_ne_rleaf t n o ho) (osTry_notJ t n)
          hroot.lt (fun _ hu => hu) hT)
        List.Forall₂.nil)
      (((ht0.keeps hr₂ (fun u hu => (hunt u hu).not_sealed) (GJ.of_grows hr₂.grows)
            fun u hu => (hunt u hu).not_sealed).keeps
          hr₃ (fun _ h => h.elim) (GJ.of_grows hr₃.grows) fun _ h => h.elim).keeps
        hrun (fun u hu => hu ▸ hroot₃.not_sealed) (hT.gj (osTry_notJ t n)) fun _ h => h.elim)
  · have : ((zs₁.map (hear w bl true)).map fun z => live (PhT.shr tl) z.2) = cs := by
      rw [hcs, List.map_map]
      refine List.map_congr_left fun z _ => ?_
      obtain ⟨⟨m, k⟩, acc⟩ := z
      rfl
    rw [this]
    exact hnd
  · intro tk0 h
    obtain rfl : tl = tk0 := by injection h
    exact ⟨hT.untouched_last hd₃.1 hroot₃.lt hus,
      hT.len_last (osTry_tl lam K L t n),
      hT.not_dead_last hd'.1⟩
  · intro h
    rcases h with h | h <;> cases h

end Req2


end Compile.Batch.Disc
