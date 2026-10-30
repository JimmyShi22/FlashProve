-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadU.lean: for every relation ag with `OnlyFb` and `FitsSh`, all chains of the
compiled prover with free empty slots (no query for an empty slot: `chainTU`,
Compile/Batch/ProverU.lean) are a `LiveW ag` (Compile/LiveWalk.lean); in particular, started on a
store that holds all tokens taken as live, after two answers that ag relates they never use the new
tail (the part of an answer that the program gets as a new token: Rom/Defer.lean). The counterpart
of Compile/Batch/DeadProver.lean (words of this library: lean/GLOSSARY.md).

An empty slot holds no token that is ever used: its fields tk and c are the default token 0, its
lists hold no token, and no piece of the program reads them. So the live tokens of a slot are
counted only if it holds a request:

  `liveAccU acc u`  acc holds a request, and u is live in it (`liveAcc`,
                    Compile/Batch/DeadFrame.lean). `liveOutU`: the same for what the chains return.
  `lw_rleavesTU`, `lw_reqTU`  The request tree: the leaf of an empty slot is a fresh token, which is
                              live.
  `ends_levelsM`, `ends_rleavesTU`, `ends_reqTU`
      Over a list of slot values that is not empty the request tree holds a token. `ends_eachM_ne`,
      `ends_joinMU_ne`: the lists of slots stay non-empty.
  `lw_chainTU`  All chains. It needs that the live tokens of the slots (`liveAccU`), of the shared
                part (`liveA0`) and of the phase (`livePh`; both: Compile/Batch/DeadFrame.lean) are
                among the tokens T that are taken as live, and either a slot (empty or not) or a
                token in T (`zs ≠ [] ∨ ∃ u, T u`). With all slots empty and no live token, the first
                tokens are the sampled leaves of the request tree, to whose root the first shared
                query is charged (Rom/Defer.lean: every marked query is charged to one token).

Notation:
  `sMT`: a natural number; the length of the salt of a leaf (Compile/Batch/Verifier.lean);
  `t`: a `Tag` (Compile/Oracles.lean): `test`, `link` or `onl`;
  `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the trees
    over the external strings;
  `depthReq`: a natural number; depth of a request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `embS`, `embP`: maps; they say how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `ph`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
  `σ0`: an `SStrat s A` (Iop/Batch.lean): a strategy for the shared part: m_0 in every round;
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated.

Limits: those in the header of Compile/Batch/DeadFrame.lean; those on `LiveW` in the header of
Compile/LiveWalk.lean (the larger T, the less is said).
Nothing on the relation `agF` (`FitsSh` is a hypothesis here). Nothing on the end of a slot
(`finishAll`) or on `proveBU` as a whole.
-/
import Compile.Batch.DeadProver
import Compile.Batch.NeedBlocksU

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile
open Compile.Batch.Need (chainTU_lo chainTU_join chainTU_shr chainTU_none)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}

local notation "Lw" => LiveW (S := spec lam K L) (sp := split lam K L) ag

/-- the live tokens of a slot, if it holds a request -/
def liveAccU {Y : Type} (a : SlotAcc lam K Y) (u : Tok) : Prop := a.x ≠ none ∧ liveAcc a u

/-- the live tokens of what the chains return -/
def liveOutU {Y : Type} (out : List (SlotAcc lam K Y) × Acc0) (u : Tok) : Prop :=
  (∃ acc ∈ out.1, liveAccU acc u) ∨ liveA0 out.2 u

/-! ## The request tree -/

theorem lw_rleavesTU (hag : OnlyFb ag) :
    ∀ (T : Tok → Prop) (l : List (Option Tok)), (∀ c, some c ∈ l → T c ∨ c = 0) →
      Lw T (fun x u => u ∈ x) (rleavesTU (lam := lam) (K := K) (L := L) l)
  | _, [], _ => .pure fun _ hu => nomatch hu
  | T, some c :: t, h =>
      (lw_rleafT hag (h c (by simp))).bind fun d =>
          (lw_rleavesTU hag _ t fun u hu => (h u (by simp [hu])).imp .inl id).bind
              fun r => .pure fun u hu => by
      rcases List.mem_cons.1 hu with e | e
      · exact .inl (.inr e)
      · exact .inr e
  | T, none :: t, h =>
      .fresh _ fun d =>
          (lw_rleavesTU hag _ t fun u hu => (h u (by simp [hu])).imp .inl id).bind
              fun r => .pure fun u hu => by
      rcases List.mem_cons.1 hu with e | e
      · exact .inl (.inr e)
      · exact .inr e

theorem lw_reqTU (hag : OnlyFb ag) {T : Tok → Prop} (depthReq : ℕ)
    (cs : List (Option Tok)) (h : ∀ c, some c ∈ cs → T c ∨ c = 0) :
    Lw T liveTT (reqTU (lam := lam) (K := K) (L := L) depthReq cs) :=
  (lw_rleavesTU hag T cs h).bind fun ls =>
      (lw_levelsM (fun _ _ _ => lw_rnodeT hag) depthReq _ ls fun _ hu => Or.inr hu).bind
          fun _ => .pure fun u hu => by
    rcases hu with h | h
    · exact .inr h
    · exact nomatch h

/-- the list that one starts from is one of the levels -/
theorem ends_levelsM {node : Tok → Tok → St lam K L Tok} :
    ∀ (d : ℕ) (l : List Tok), Ends (fun lv => l ∈ lv) (levelsM node d l)
  | 0, _ => List.mem_singleton.2 rfl
  | _ + 1, l =>
    Ends.bind (ends_true _) fun _ _ =>
      Ends.bind (ends_true _) fun r _ => show l ∈ l :: r from List.mem_cons_self

theorem ends_rleavesTU :
    ∀ l : List (Option Tok),
      l ≠ [] → Ends (fun x => x ≠ []) (rleavesTU (lam := lam) (K := K) (L := L) l)
  | [], h => absurd rfl h
  | some _ :: _, _ =>
    Ends.bind (ends_true _) fun d _ =>
      Ends.bind (ends_true _) fun r _ => show d :: r ≠ [] from List.cons_ne_nil _ _
  | none :: _, _ =>
    fun d => Ends.bind (ends_true _) fun r _ => show d :: r ≠ [] from List.cons_ne_nil _ _

/-- over a list of slot values that is not empty the request tree holds a token -/
theorem ends_reqTU (depthReq : ℕ) (cs : List (Option Tok)) (h : cs ≠ []) :
    Ends (fun rq => ∃ u, liveTT rq u) (reqTU (lam := lam) (K := K) (L := L) depthReq cs) :=
  Ends.bind (ends_rleavesTU cs h) fun ls hls =>
      Ends.bind (ends_levelsM depthReq ls) fun lv hlv => by
    obtain ⟨u, t, rfl⟩ := List.exists_cons_of_ne_nil hls
    exact ⟨u, .inl ⟨_, hlv, List.mem_cons_self⟩⟩

/-! ## The rounds -/

theorem ends_eachM_ne {σ τ : Type} (f : σ → St lam K L τ) :
    ∀ l : List σ, l ≠ [] → Ends (fun r => r ≠ []) (eachM f l)
  | [], h => absurd rfl h
  | _ :: _, _ =>
    Ends.bind (ends_true _) fun b _ =>
      Ends.bind (ends_true _) fun r _ => show b :: r ≠ [] from List.cons_ne_nil _ _

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem lw_slotLoU (hag : OnlyFb ag) {T : Tok → Prop} {r : Round} {s : Shape} (a : RAnn r)
    (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT)
    (hF : ∀ α g, w.grJ = some g → FitsLoop ag w.chal t plJ α g)
    (hN : w.grJ = none → ∀ α (q : FbIn lam L t) r r', q.plain = plJ α → ¬ ag (.fb t) q r r')
    (z : SlotSt lam K Y (r :: s)) (hz : ∀ u, liveAccU z.2 u → T u) (hph : ∀ u, livePh ph u → T u) :
    Lw T (fun z' u => liveAccU z'.2 u) (slotLoU sMT t cms xin a w emb plJ i ph z) := by
  unfold slotLoU
  cases hx : z.2.x with
  | none => exact .pure fun u hu => absurd hx hu.1
  | some y =>
    exact (lw_slotLo hag sMT t cms xin a w emb plJ i ph hF hN z
        (fun u hu => hz u ⟨by rw [hx]; exact nofun, hu⟩) hph).imp
      (fun _ h => h) fun _ _ h => h.2

theorem lw_slotJoinU (hag : OnlyFb ag) {T : Tok → Prop} {r : Round} {s : Shape}
    (a : RAnn r) (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (z : SlotSt lam K Y (r :: s)) (hz : ∀ u, liveAccU z.2 u → T u) :
    Lw T (fun z' u => liveAccU z'.2 u) (slotJoinU sMT t a w emb plJ i z) := by
  unfold slotJoinU
  cases hx : z.2.x with
  | none => exact .pure fun u hu => absurd hx hu.1
  | some y =>
    exact (lw_slotJoin hag sMT t a w emb plJ i z fun u hu => hz u ⟨by rw [hx]; exact nofun, hu⟩).imp
      (fun _ h => h) fun _ _ h => h.2

theorem lw_joinMU (hag : OnlyFb ag) {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (T : Tok → Prop),
      (∀ z ∈ zs, ∀ u, liveAccU z.2 u → T u) →
      Lw T (fun o u => (∃ z ∈ o.1, liveAccU z.2 u) ∨ some u ∈ o.2) (joinMU sMT t a w emb plJ i zs)
  | [], _, _ => .pure fun _ hu => by
      rcases hu with ⟨_, h, _⟩ | h
      · exact nomatch h
      · exact nomatch h
  | z :: zs, T, h =>
      (lw_slotJoinU sMT t hag a w emb plJ i z (h z (by simp))).bind fun z' =>
          (lw_joinMU hag a w emb plJ i zs _ fun x hx u hu => .inl (h x (by simp [hx]) u hu)).bind
              fun o => .pure fun u hu => by
      rcases hu with ⟨y, hy, hu⟩ | hu
      · rcases List.mem_cons.1 hy with e | e
        · exact .inl (.inr (e ▸ hu))
        · exact .inr (.inl ⟨y, e, hu⟩)
      · rcases List.mem_cons.1 hu with e | e
        · obtain ⟨y, hy, e'⟩ := Option.map_eq_some_iff.1 e.symm
          exact .inl (.inr ⟨by rw [hy]; exact nofun, .inr (.inl e'.symm)⟩)
        · exact .inr (.inr e)

theorem ends_joinMU_ne {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      zs ≠ [] → Ends (fun o => o.1 ≠ [] ∧ o.2 ≠ []) (joinMU sMT t a w emb plJ i zs)
  | [], h => absurd rfl h
  | _ :: _, _ =>
    Ends.bind (ends_true _) fun _ _ =>
      Ends.bind (ends_true _) fun _ _ => ⟨List.cons_ne_nil _ _, List.cons_ne_nil _ _⟩

/-- receiving a shared verifier message makes no token live -/
theorem liveAccU_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (z : SlotSt lam K Y (r :: s)) (u : Tok) (h : liveAccU (hear w bl noted z).2 u) :
    liveAccU z.2 u :=
  ⟨by obtain ⟨⟨m, k⟩, acc⟩ := z; exact h.1, liveAcc_hear w bl noted z u h.2⟩

/-- All chains of a batch, free empty slots, are a `LiveW`, under the hypotheses below. -/
theorem lw_chainTU (hag : OnlyFb ag) (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (T : Tok → Prop),
      FitsSh ag t s A W embP → (zs ≠ [] ∨ ∃ u, T u) → (∀ z ∈ zs, ∀ u, liveAccU z.2 u → T u) →
      (∀ u, liveA0 a0 u → T u) → (∀ u, livePh ph u → T u) →
      Lw T liveOutU (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, zs, a0, T, _, _, hz, h0, _ => .pure fun u hu => by
      rcases hu with ⟨acc, ha, hu⟩ | hu
      · obtain ⟨z, hzm, rfl⟩ := List.mem_map.1 ha
        exact hz z hzm u hu
      · exact h0 u hu
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, T, H, h1, hz, h0, hph => by
      have hnone : ∀ (T' : Tok → Prop) (a1 : Acc0), (∀ u, liveA0 a1 u → T' u) →
          ∀ u, liveA0 { a1 with trees := a1.trees ++ [none] } u → T' u := by
        intro T' a1 h u hu
        rcases hu with e | ⟨x, hx, hu⟩ | e
        · exact h u (.inl e)
        · rcases List.mem_append.1 hx with e | e
          · exact h u (.inr (.inl ⟨x, e, hu⟩))
          · rw [List.mem_singleton.1 e] at hu
            obtain ⟨_, e', _⟩ := hu
            exact nomatch e'
        · exact h u (.inr (.inr e))
      have hmap : ∀ (bl : Blk lam K) (noted : Bool) (l : List (SlotSt lam K Y (r :: s))),
          l ≠ [] → l.map (hear w bl noted) ≠ [] :=
        fun _ _ l hl e => hl (List.map_eq_nil_iff.1 e)
      by_cases hk : a.kind = .lo
      · rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        have hlw := lw_eachM (T0 := livePh ph)
          (lσ := fun (z : SlotSt lam K Y (r :: s)) u => liveAccU z.2 u)
          (lτ := fun (z : SlotSt lam K Y s) u => liveAccU z.2 u)
          (fun T' hT z hz' =>
            lw_slotLoU sMT t cms xin hag a w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i ph H.1.1 H.1.2 z hz' hT)
          zs T hph hz
        rcases h1 with hne | h1
        · refine hlw.bindG (ends_eachM_ne _ zs hne) fun zs' hzs' => ?_
          exact lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ zs' _ _ H.2.2 (.inl hzs')
            (fun z hzm u hu => .inr ⟨z, hzm, hu⟩) (hnone _ a0 fun u hu => .inl (h0 u hu))
            fun u hu => .inl (hph u (livePh_afterLo ph u hu))
        · refine hlw.bind fun zs' => ?_
          exact lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ zs' _ _ H.2.2
            (.inr (h1.imp fun _ h => .inl h)) (fun z hzm u hu => .inr ⟨z, hzm, hu⟩)
            (hnone _ a0 fun u hu => .inl (h0 u hu))
            fun u hu => .inl (hph u (livePh_afterLo ph u hu))
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          -- what follows the request tree, given a live token
          have hrest : ∀ (o : List (SlotSt lam K Y (r :: s)) × List (Option Tok)) (rq : TTree),
              (∃ u, T u ∨ liveTT rq u) →
              Lw (fun u => ((T u ∨ ((∃ z ∈ o.1, liveAccU z.2 u) ∨ some u ∈ o.2)) ∨ liveTT rq u))
                liveOutU
                (tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
                  fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root)
                      (fun _ => Head.f4 cms) (fun _ => f4_inj cms)
                      (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
                        chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p))
                            (fun z => embP (.inr z)) (i + 1) (.shr tl)
                            (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
                            { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }) := by
            intro o rq hl
            refine lw_withTree hag sMT _ _ _ fun tr0 => ?_
            refine lw_fbG i _ _ w.gr0 (H.2.1.1 _) (fun h => H.2.1.2 h _)
              (hl.imp fun _ h => .inl (h.elim (fun h => .inl (.inl h)) .inr))
              ((root_or rq).imp (fun h => .inl (.inr h)) id)
              (fun u hu => (rootOT_or tr0 u (by simpa using hu)).imp .inr id) fun nc dd bl tl => ?_
            refine lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 (.inr ⟨tl, .inr rfl⟩)
              (fun z hzm u hu => ?_) (fun u hu => ?_) fun u hu => .inr hu
            · obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
              exact .inl (.inl (.inl (.inr (.inl ⟨z0, hz0, liveAccU_hear w bl true z0 u hu⟩))))
            · rcases hu with e | ⟨x, hx, hu⟩ | ⟨x, e, hu⟩
              · rcases List.mem_append.1 e with e | e
                · exact .inl (.inl (.inl (.inl (h0 u (.inl e)))))
                · exact .inr (List.mem_singleton.1 e)
              · rcases List.mem_append.1 hx with e | e
                · exact .inl (.inl (.inl (.inl (h0 u (.inr (.inl ⟨x, e, hu⟩))))))
                · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))
              · exact .inl (.inl (.inr ((Option.some.inj e) ▸ hu)))
          rcases h1 with hne | h1
          · refine (lw_joinMU sMT t hag a w _ _ i zs T hz).bindG
              (ends_joinMU_ne sMT t a w _ _ i zs hne) fun o ho => ?_
            exact (lw_reqTU hag depthReq o.2 fun c hc => .inl (.inr (.inr hc))).bindG
              (ends_reqTU depthReq o.2 ho.2) fun rq hrq => hrest o rq (hrq.imp fun _ h => .inr h)
          · refine (lw_joinMU sMT t hag a w _ _ i zs T hz).bind fun o => ?_
            exact (lw_reqTU hag depthReq o.2 fun c hc => .inl (.inr (.inr hc))).bind
              fun rq => hrest o rq (h1.imp fun _ h => .inl h)
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine lw_withTree hag sMT _ _ _ fun tr0 => ?_
          refine lw_fbG i _ _ w.gr0 (H.2.1.1 _) (fun h => H.2.1.2 h _) ⟨tk0, .inl (hph tk0 rfl)⟩
            (.inl (.inl (hph tk0 rfl)))
            (fun u hu => (rootOT_or tr0 u (by simpa using hu)).imp .inr id) fun nc dd bl tl => ?_
          refine lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 (.inr ⟨tl, .inr rfl⟩)
            (fun z hzm u hu => ?_) (fun u hu => ?_) fun u hu => .inr hu
          · obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
            exact .inl (.inl (hz z0 hz0 u (liveAccU_hear w bl false z0 u hu)))
          · rcases hu with e | ⟨x, hx, hu⟩ | e
            · rcases List.mem_append.1 e with e | e
              · exact .inl (.inl (h0 u (.inl e)))
              · exact .inr (List.mem_singleton.1 e)
            · rcases List.mem_append.1 hx with e | e
              · exact .inl (.inl (h0 u (.inr (.inl ⟨x, e, hu⟩))))
              · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))
            · exact .inl (.inl (h0 u (.inr (.inr e))))
        | first =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          refine lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 (h1.imp (hmap _ _ zs) id)
            (fun z hzm u hu => ?_) (hnone _ a0 h0) hph
          obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
          exact hz z0 hz0 u (liveAccU_hear w _ false z0 u hu)
        | aft =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          refine lw_chainTU hag depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 (h1.imp (hmap _ _ zs) id)
            (fun z hzm u hu => ?_) (hnone _ a0 h0) hph
          obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
          exact hz z0 hz0 u (liveAccU_hear w _ false z0 u hu)

end Rounds

end Compile.Batch.Dead
