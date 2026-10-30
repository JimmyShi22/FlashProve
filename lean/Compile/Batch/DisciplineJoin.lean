-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineJoin.lean: in the joining round of a batch (the first shared round after a
local one) the slots' part (`joinM`) obeys the rules of deferred programming, from a state with
`TidyO`, at least n₀ tokens, `SlotI` (phase `loc`) in each slot and different last tails (words of
this library: lean/GLOSSARY.md).

For `Spec.safeChainT0` (Compile/Batch/DisciplineProve.lean): `gT`, `slotJoin`, `joinM` of
Compile/Batch/Prover.lean, and the state after the request tree, the tree over the shared component
and the query in format (F4). A component may have no tree: `rtL` and `NewT` are those of
Compile/Batch/DisciplineChain.lean. In each slot g is charged to the last tail and its answer is the
slot value; a query to the leaf oracle of request trees is charged to the slot value; (F4) is
charged to the request root. So the tokens of slot j now include those beside and on its request
path, and the request root. The query in format (F4) may have proof-of-work bits: then a search
(`Tries`, Compile/Batch/DisciplineLoop.lean), whose failed tails join the shared dead tails (`Dead`,
Compile/Batch/DisciplineSlot.lean).

Notation:
  g: the oracle `OracleName.g t` (Compile/Batch/Oracles.lean); `gT` (Compile/Batch/Prover.lean): the query
    to g in the joining round: its answer is the slot value;
  `done`: a list of pairs of numbers: the depths of the trees of the rounds made (`ChainInv`,
    Compile/Batch/DisciplineChain.lean); in a pair the slot's tree first, then the shared one
    (`depthsOf`, Compile/Batch/DisciplineSlot.lean);
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `acc.tk`, `acc.c` (fields of `SlotAcc`, Compile/Batch/Prover.lean: what a slot has accumulated):
    the token that the next query of its chain holds (not in the phase `shr tk0`: see `live`,
    Compile/Batch/DisciplineSlot.lean); its slot value, once the chains have joined;
  `Wk` (Compile/Batch/DisciplineSlot.lean): the leaf oracle of request trees;
  `PA lv j` (Compile/Batch/DisciplineTree.lean): the tokens beside the way from leaf j to the
    root, and those on it.
-/
import Compile.Batch.DisciplineChain
noncomputable section -- Lean tags what it cannot compile

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type}

/-! ## 1. One slot, all slots -/

/-- a slot after g: its slot value is its one open end, and is untouched -/
structure JoinedI (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (a0 : Acc0)
    (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  fin : SlotF d n₀ done (fun u => u = acc.c) a0 j acc
  unt : Untouched d acc.c
  len : Len d acc.c lam
  mem : acc.c ∈ acc.toks
  alive : ¬ Dead d acc.c

theorem JoinedI.frame {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {a0 : Acc0} {j : ℕ}
    {acc : SlotAcc lam K Y} {Cc Ch : Tok → Prop} {e M : OracleName → ℕ} (h : JoinedI d n₀ done a0 j acc)
    (hd : TidyO (rulesB K L lam p) d) (hr : Run Cc Ch NoTok e M d d')
    (hc : ∀ u, Cc u → Fit d u ∧ u ≠ acc.c) (hh : ¬ Ch acc.c) : JoinedI d' n₀ done a0 j acc :=
  ⟨h.fin.keeps hr hc,
    h.unt.grows hr.grows hh fun x => x,
    h.len.grows hr.grows,
    h.mem,
    DeadW.keeps_not h.alive hd h.unt.lt hr fun u hu => (hc u hu).1.1⟩

/-- the queries of one slot in the joining round (a bound: a component without a tree has no leaf
and no node) -/
def MJ (lam K : ℕ) (L : BatchProtocol I X) (t : Tag) (dJ : ℕ) : OracleName → ℕ := fun o =>
  cnt1 (S := spec lam K L) OracleName.leaf (2 ^ dJ) o +
    cnt1 (S := spec lam K L) OracleName.node (2 ^ dJ) o + cnt1 (S := spec lam K L) (OracleName.g t) 1 o

/-- the accumulator of a slot after g -/
def accJ (acc : SlotAcc lam K Y) (c : Tok) (tr : Option TTree) : SlotAcc lam K Y :=
  { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] }

theorem safe_slotJoin {r : Round} {s : Shape} (t : Tag) (a : RAnn r) (w : WireRB lam K r a)
    (emb : (q : r.Pos) → r.Sym q → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (z : SlotSt lam K Y (r :: s)) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ))
    (a0 : Acc0) (j : ℕ) (hd : TidyO (rulesB K L lam p) d) (hn : n₀ ≤ d.vals.length)
    (h : SlotI p d n₀ done PhT.loc a0 j z.2) :
    SafeO (rulesB K L lam p) (slotJoin p.sMT t a w emb plJ i z) d fun z' d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun u => u = z.2.tk) (fun u => u = z.2.tk) NoTok zr (MJ lam K L t w.depthJ) d d' ∧
      JoinedI d' n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z'.2 ∧ d.vals.length ≤ z'.2.c := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  show SafeO _
    (withTree p.sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      gT t i acc.tk (tr.map TTree.root) (plJ (a.plain m.2).2) fun c =>
        Step.pure ((m, k), accJ acc c tr))
    d _
  refine safe_withTree w.hasJ w.depthJ _ _ d hd _ fun tr d₁ hd₁ hr₁ htt => ?_
  have hI₁ : SlotI p d₁ n₀ done PhT.loc a0 j acc :=
    h.frame hd hr₁ (fun _ hu => hu.elim) (fun hu => hu)
  obtain ⟨c1, c2, c3⟩ := hI₁.cap
  have hlt : acc.tk < d.vals.length := h.cap.1.lt
  have hus : ∀ u ∈ rtL tr, u < d₁.vals.length := fun u hu => htt.lt hu
  have htu : acc.tk ∉ rtL tr := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hlt)
  have hbit : (rulesB K L lam p).bits (OracleName.g t) ≤ (d₁.val acc.tk).length := le_of_eq c2.2.symm
  refine ⟨hus, htu, c1.freeAt _, hbit, g_mk t, fun rr T => ?_⟩
  refine ⟨hd₁.mark hus htu (c1.freeAt _) _ hbit (g_mk t) rr T,
    ?_,
    ⟨?_, Untouched.of_tail hd₁ c1.lt hus _ rr T,
      Len.of_tail d₁ (OracleName.g t) _ _ _ rr T,
      List.mem_append_right _ (List.mem_singleton.mpr rfl),
      not_deadW_last (hd₁.mark hus htu (c1.freeAt _) _ hbit (g_mk t) rr T)
        (le_of_eq (length_afterMark _ _ _ _ _ _ _))⟩,
    hr₁.length_le⟩
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
      (by simp) (t := acc.tk) (us := rtL tr) hn hr₁.length_le hlt c1.not_sealed
      (fun u hu => Or.inl hu) (fun u hu => Or.inl hu) (fun _ hu => hu) htt rfl rfl rfl _ rr T

theorem safe_joinM {r : Round} {s : Shape} (t : Tag) (a : RAnn r)
    (w : WireRB lam K r a) (emb : (q : r.Pos) → r.Sym q → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (n₀ : ℕ) (done : List (ℕ × ℕ)) (a0 : Acc0) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (j : ℕ) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → n₀ ≤ d.vals.length →
    AllFrom (fun j z => SlotI p d n₀ done PhT.loc a0 j z.2) j zs → (zs.map fun z => z.2.tk).Nodup →
    SafeO (rulesB K L lam p) (joinM p.sMT t a w emb plJ i zs) d fun o d' =>
      TidyO (rulesB K L lam p) d' ∧
      Run (fun u => ∃ z ∈ zs, u = z.2.tk) (fun u => ∃ z ∈ zs, u = z.2.tk) NoTok zr
        (fun o => zs.length * MJ lam K L t w.depthJ o) d d' ∧
      AllFrom (fun j z => JoinedI d' n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z.2) j o.1 ∧
      o.2 = o.1.map (fun z => z.2.c) ∧
      o.2.Nodup ∧
      (∀ c ∈ o.2, d.vals.length ≤ c) ∧ o.1.length = zs.length
  | [], _, d, hd, _, _, _ =>
    ⟨hd, Run.refl d, trivial, rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | z :: zs, j, d, hd, hn, hall, hnd => by
      show SafeO _ ((slotJoin p.sMT t a w emb plJ i z).bind fun z' =>
        (joinM p.sMT t a w emb plJ i zs).bind fun o => Step.pure (z' :: o.1, z'.2.c :: o.2)) d _
      have hnd' := List.nodup_cons.mp hnd
      have hne : ∀ x ∈ zs, z.2.tk ≠ x.2.tk := fun x hx he =>
        hnd'.1 (List.mem_map.mpr ⟨x, hx, he.symm⟩)
      refine SafeO.bind _ _ d
        (SafeO.mono ?_ _ d (safe_slotJoin t a w emb plJ i z d n₀ done a0 j hd hn hall.1))
      rintro z' d₁ ⟨hd₁, hr₁, hJ', hnew⟩
      have hall₁ : AllFrom (fun j z => SlotI p d₁ n₀ done PhT.loc a0 j z.2) (j + 1) zs :=
        AllFrom.mono_mem (j + 1) zs (fun j' x hx hIx => hIx.frame hd hr₁
          (fun u hu => hu ▸ ⟨hall.1.fit, hne x hx⟩) (fun hu => hne x hx hu.symm)) hall.2
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁
          (safe_joinM t a w emb plJ i n₀ done a0 zs (j + 1) d₁ hd₁
            (le_trans hn hr₁.length_le) hall₁ hnd'.2))
      rintro o d₂ ⟨hd₂, hr₂, hall₂, hmap₂, hnd₂, hnew₂, hlen₂⟩
      have hold : ∀ x ∈ zs, x.2.tk < d.vals.length := fun x hx => by
        obtain ⟨j'', hIx0⟩ := AllFrom.of_mem (j + 1) zs hall.2 x hx
        exact hIx0.cap.1.lt
      refine ⟨hd₂, ?_, ⟨?_, hall₂⟩, by simp [hmap₂], ?_, ?_, by simp [hlen₂]⟩
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
        · obtain ⟨j', hIx⟩ := AllFrom.of_mem (j + 1) zs hall₁ x hx
          exact hu ▸ ⟨hIx.fit, fun he => absurd hnew (Nat.not_le.mpr (he ▸ hold x hx))⟩
        · exact absurd hnew (Nat.not_le.mpr (hu ▸ hold x hx))
      · exact List.nodup_cons.mpr ⟨fun hm => absurd (hnew₂ _ hm) (Nat.not_le.mpr hJ'.unt.lt), hnd₂⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hnew
        · exact le_trans hr₁.length_le (hnew₂ c hc)

/-! ## 2. After the request tree -/

theorem AllFrom.map_idx {σ τ : Type} {P : ℕ → σ → Prop} {Q : ℕ → τ → Prop} (f : σ → τ) :
    ∀ (l : List σ) (j₀ : ℕ), AllFrom P j₀ l →
      (∀ i (hi : i < l.length), P (j₀ + i) l[i] → Q (j₀ + i) (f l[i])) → AllFrom Q j₀ (l.map f)
  | [], _, _, _ => trivial
  | a :: t, j₀, h, hf => ⟨hf 0 (Nat.succ_pos _) h.1, AllFrom.map_idx f t (j₀ + 1) h.2 fun i hi hP => by
      have :=
        hf (i + 1) (Nat.succ_lt_succ hi) (by rw [show j₀ + (i + 1) = j₀ + 1 + i by omega]; exact hP)
      rw [show j₀ + (i + 1) = j₀ + 1 + i by omega] at this
      exact this⟩

section Req
variable {d₁ d₂ d₃ : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {a0 : Acc0} {j : ℕ}
  {acc : SlotAcc lam K Y} {cs : List Tok} {rq : TTree} {tr0 : Option TTree} {M₂ M₃ : OracleName → ℕ}

theorem inU_req (hreq0 : a0.req = none) (u : Tok) :
    InU { a0 with req := some rq } j acc u ↔ InU a0 j acc u ∨ u ∈ PA rq.levels j ∨ u = rq.root := by
  unfold InU
  rw [hreq0]
  constructor
  · rintro (h1 | h1 | h1 | h1 | ⟨rq', h1, h2⟩ | h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h1))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · obtain rfl : rq = rq' := Option.some.inj h1
      exact Or.inr h2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1)))))
  · rintro ((h1 | h1 | h1 | h1 | ⟨rq', h1, _⟩ | h1) | h1)
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact absurd h1 (by simp)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rq, rfl, h1⟩))))

/-- Under the hypotheses below, the tokens of a slot after the request tree: with those beside and
on its request path, and the request root; the open ends are the slot value and the request root. -/
theorem JoinedI.after_req (h : JoinedI d₁ n₀ done a0 j acc) (hn : n₀ ≤ d₁.vals.length)
    (hreq0 : a0.req = none) (hunt : ∀ x ∈ cs, Untouched d₁ x) (hal : ∀ x ∈ cs, ¬ Dead d₁ x)
    (hr₂ : Run (fun u => u ∈ cs) (fun u => u ∈ cs) NoTok zr M₂ d₁ d₂)
    (hPA : ∀ u ∈ PA rq.levels j,
      Deps d₂ u (PA rq.levels j) ∧ u < d₂.vals.length ∧ d₁.vals.length ≤ u)
    (hC : Deps d₂ acc.c (PA rq.levels j)) (hroot : Untouched d₂ rq.root)
    (hrnew : d₁.vals.length ≤ rq.root) (hsePA : ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d₂ u) :
    SlotF d₂ n₀ done (fun u => u = acc.c ∨ u = rq.root) { a0 with req := some rq } j acc := by
  refine ⟨⟨fun e he hV => ?_, fun u hu => ?_, fun u hu => ?_⟩,
    fun u hu => ?_,
    h.fin.trees.keeps hr₂ fun u hu => (hunt u hu).not_sealed,
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
  · rcases (inU_req hreq0 _).1 hu with h1 | h1 | h1
    · exact h.fin.new _ h1
    · exact le_trans hn (hPA _ h1).2.2
    · exact h1 ▸ le_trans hn hrnew

/-- A slot after the attempts of the query in format (F4). nn: the numbers of the final attempts of
the shared rounds; dd: the tails of the failed attempts; tl: the tail of the final attempt. -/
theorem SlotI.after_f4 {acc' : SlotAcc lam K Y}
    (hF : SlotF d₃ n₀ done (fun u => u = acc.c ∨ u = rq.root) { a0 with req := some rq } j acc)
    (hd₃ : TidyO (rulesB K L lam p) d₃) (hn : n₀ ≤ d₃.vals.length) (hroot : Untouched d₃ rq.root)
    (hur : ∀ u ∈ rtL tr0, Untouched d₃ u) (hrn : ∀ u ∈ rtL tr0, n₀ ≤ u)
    (hclt : acc.c < d₃.vals.length) (hcs : acc.c ∉ d₃.shown) (hch : HeldAt d₃ acc.c Wk)
    (hcl : Len d₃ acc.c lam) (hcm : acc.c ∈ acc.toks) (hcr : acc.c ≠ rq.root)
    (hct : acc.c ∉ rtL tr0) (hca : ¬ Dead d₃ acc.c) (e1 : acc'.toks = acc.toks)
    (e2 : acc'.trees = acc.trees) (e3 : acc'.c = acc.c) (e4 : acc'.dead = acc.dead) (t : Tag)
    {n : ℕ} (nn : List ℕ) {dd : List Tok} {tl : Tok} {d' : DSt (spec lam K L)}
    (hT : Tries (split lam K L) rq.root (rtL tr0) d₃ (osTry t n) (dd.reverse ++ [tl]) d') :
    SlotI p d' n₀ done (PhT.shr tl)
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
  refine ⟨⟨?_, fun u hu => ?_, ?_, by rw [e1]; exact hF.ne⟩, ?_, ?_⟩
  · refine (hF.cl.extend_tries hd₃ (t := rq.root) (us := rtL tr0)
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
  · rcases (hiff u).1 hu with h1 | h1 | h1 | h1
    · exact hF.new u h1
    · exact h1 ▸ le_trans hn htl
    · exact le_trans hn (hT.tail_ge u (List.mem_append_left _ h1))
    · exact hrn u h1
  · rw [e2]
    exact hF.trees.keeps hrun fun u hu => hu ▸ hroot.not_sealed
  · exact ⟨by rw [e3]; exact lt_of_lt_of_le hclt hrun.length_le,
      by rw [e3]; exact not_shown_grows hclt hcs hrun.grows fun x => x,
      by rw [e3]; exact hch.grows hclt hrun.grows (fun hh => hh.elim hcr hct),
      by rw [e3]; exact hcl.grows hrun.grows,
      by rw [e3, e1]; exact hcm,
      List.mem_append_right _ (List.mem_singleton.mpr rfl),
      by rw [e3]; exact Nat.ne_of_lt (lt_of_lt_of_le hclt htl)⟩
  · show ¬ Dead d' acc'.c
    rw [e3]
    exact DeadW.keeps_not hca hd₃ hclt hrun fun u hu => hu ▸ hroot.not_sealed

/-- Between the joining round and the next. The premises are what joinM, reqT, the tree over the
shared component and the attempts of the query in format (F4) leave behind. -/
theorem ChainInv.after_join {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a)
    {zs₁ : List (SlotSt lam K Y (r :: s))}
    (hall : AllFrom (fun j z => JoinedI d₁ n₀ (done ++ [(w.depthJ, w.depth0)]) a0 j z.2) 0 zs₁)
    (hcs : cs = zs₁.map fun z => z.2.c) (hnd : cs.Nodup) (hn : n₀ ≤ d₁.vals.length)
    (hreq0 : a0.req = none) (ht0 : Trees0 d₁ n₀ done a0.trees) (hd₁ : TidyO (rulesB K L lam p) d₁)
    (hd₂ : TidyO (rulesB K L lam p) d₂)
    (hr₂ : Run (fun u => u ∈ cs) (fun u => u ∈ cs) NoTok zr M₂ d₁ d₂)
    (hPA : ∀ j < cs.length,
      ∀ u ∈ PA rq.levels j, Deps d₂ u (PA rq.levels j) ∧ u < d₂.vals.length ∧ d₁.vals.length ≤ u)
    (hC : ∀ j < cs.length,
      Deps d₂ (cs.getD j 0) (PA rq.levels j) ∧
      HeldAt d₂ (cs.getD j 0) (fun o => o = OracleName.rleaf) ∧
      cs.getD j 0 ∉ d₂.shown)
    (hroot : Untouched d₂ rq.root) (hrnew : d₁.vals.length ≤ rq.root)
    (hsePA : ∀ j < cs.length, ∀ u ∈ PA rq.levels j, u = rq.root ∨ Sealed d₂ u)
    (hd₃ : TidyO (rulesB K L lam p) d₃) (hr₃ : Run NoTok NoTok NoTok zr M₃ d₂ d₃)
    (htt : NewT d₃ d₂.vals.length w.depth0 tr0) (t : Tag) {n : ℕ} (nn : List ℕ) {dd : List Tok}
    {tl : Tok} {d' : DSt (spec lam K L)} (hd' : TidyO (rulesB K L lam p) d')
    (hT : Tries (split lam K L) rq.root (rtL tr0) d₃ (osTry t n) (dd.reverse ++ [tl]) d')
    (bl : Blk lam K) :
    ChainInv p d' n₀ (done ++ [(w.depthJ, w.depth0)]) (PhT.shr tl)
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
    exact SlotI.after_f4 (acc' := (hear w bl true ((m, k), acc)).2)
      ((hJ.after_req hn hreq0 hunt hal hr₂ hPAi c1 hroot hrnew hsei).keeps hr₃ fun _ h => h.elim)
      hd₃ hn₃ hroot₃ (fun _ hu => htt.unt hu) (fun _ hu => le_trans hn₂ (htt.le hu))
      (lt_of_lt_of_le hclt₂ hr₃.length_le) (not_shown_grows hclt₂ c3 hr₃.grows fun h => h)
      (c2.grows hclt₂ hr₃.grows fun h => h) ((hJ.len.grows hr₂.grows).grows hr₃.grows) hJ.mem
      (Nat.ne_of_lt (lt_of_lt_of_le hclt₁ hrnew))
      (fun hu => absurd (htt.le hu) (Nat.not_le.mpr hclt₂))
      (DeadW.keeps_not (DeadW.keeps_not hJ.alive hd₁ hclt₁ hr₂ fun u hu => (hunt u hu).not_sealed)
        hd₂ hclt₂ hr₃ fun _ h => h.elim)
      rfl rfl rfl rfl t nn hT
  · exact forall₂_append
      (List.Forall₂.cons
        (htt.tts_tries hn₂ (fun o ho => osTry_ne_rleaf t n o ho) hroot.lt (fun _ hu => hu) hT)
        List.Forall₂.nil)
      (((ht0.keeps hr₂ fun u hu => (hunt u hu).not_sealed).keeps hr₃ fun _ h => h.elim).keeps
        hrun fun u hu => hu ▸ hroot₃.not_sealed)
  · have : ((zs₁.map (hear w bl true)).map fun z => live (PhT.shr tl) z.2) = cs := by
      rw [hcs, List.map_map]
      refine List.map_congr_left fun z _ => ?_
      obtain ⟨⟨m, k⟩, acc⟩ := z
      rfl
    rw [this]
    exact hnd
  · intro tk0 h
    obtain rfl : tl = tk0 := by injection h
    exact ⟨hT.untouched_last hd₃ hroot₃.lt hus,
      hT.len_last (osTry_tl lam K L t n),
      hT.not_dead_last hd'⟩
  · intro h
    rcases h with h | h <;> cases h

end Req

end Compile.Batch.Disc
