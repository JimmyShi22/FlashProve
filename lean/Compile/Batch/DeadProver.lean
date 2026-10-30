-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadProver.lean: for every relation ag with `OnlyFb` and `FitsSh`, one execution of
the compiled prover (`proveB`, Compile/Batch/Prover.lean) is a `LiveW ag` (Compile/LiveWalk.lean;
Compile/Batch/DeadFrame.lean); in particular, started on a store that holds all tokens taken as
live, after two answers that ag relates it never uses the new tail (the part of an answer that the
program gets as a new token: Rom/Defer.lean; words of this library: lean/GLOSSARY.md).

  `lw_slotJoin`, `lw_joinM`  The joining round.
  `FitsSh ag t s A W embP`  What the relation must say at the searches of all rounds that are left:
                            `FitsLoop` (Compile/Batch/DeadFrame.lean) for the slot's and the shared
                            record of each round; where a record is missing, the relation relates
                            nothing (exactly: no two answers at that round's query to `fb t`).
  `lw_finishSlot`  The one reveal (in this sense: the `Step.reveal` in the body of `finishSlot`;
                   `openT`, `openE` are further ones) names the tails of the failed attempts too;
                   what follows reads the salt, the roots, the path and the request root out of the
                   revealed list, and nothing after them (`LiveW.revealMore`).
  `lw_proveB`  It needs that the live tokens of the given trees are among the tokens T that are
               taken as live, and either a slot or a token in T. With neither, a shared round's
               first attempt would be charged (Rom/Defer.lean: every marked query is charged to one
               token) to the default token 0 (the head of Compile/LiveWalk.lean, "The default token
               0"), which would then be the first failed tail (on an empty store the first new token
               has the number 0).

Notation:
  `LiveW ag T TP c` (Compile/LiveWalk.lean): `LiveWalk`, with the live tokens given as sets: T:
    those in the arguments of c; TP a: those in its value a (`fun _ _ => False`: none);
  `Ends G c` (Compile/LiveWalk.lean): every value that the program returns has G, whatever the
    answers, the coins and the tokens;
  `sMT`, `sFS`: natural numbers; sMT is the length of the salt of a leaf, sFS that of the salt of
    a chain (Compile/Batch/Verifier.lean);
  `t`: a `Tag` (Compile/Oracles.lean): `test`, `link` or `onl`;
  `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the trees
    over the external strings;
  `depthReq`: a natural number; depth of a request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `embS`, `embP`: maps; they say how symbols and plain parts are written into queries (`verifyB`,
    Compile/Batch/Verifier.lean);
  `σ0`: an `SStrat s A` (Iop/Batch.lean): a strategy for the shared part: m_0 in every round;
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
    Compile/Batch/Prover.lean).

Limits: those in the header of Compile/Batch/DeadFrame.lean; those on `LiveW` in the header of
Compile/LiveWalk.lean (the larger T, the less is said).
Nothing on the relation `agF` (`FitsSh` is a hypothesis here).
-/
import Compile.Batch.DeadFrame

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile
open Compile.Batch.Need (chainT_lo chainT_join chainT_shr chainT_none)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}

local notation "Lw" => LiveW (S := spec lam K L) (sp := split lam K L) ag

/-- A program f that is run in each slot. T0: what f needs to be live beside its slot. -/
theorem lw_eachM {σ τ : Type} {f : σ → St lam K L τ} {lσ : σ → Tok → Prop} {lτ : τ → Tok → Prop}
    {T0 : Tok → Prop}
    (hf : ∀ T' : Tok → Prop, (∀ u, T0 u → T' u) → ∀ a, (∀ u, lσ a u → T' u) → Lw T' lτ (f a)) :
    ∀ (l : List σ) (T : Tok → Prop), (∀ u, T0 u → T u) → (∀ a ∈ l, ∀ u, lσ a u → T u) →
      Lw T (fun r u => ∃ b ∈ r, lτ b u) (eachM f l)
  | [], _, _, _ => .pure fun _ hu => by obtain ⟨_, h, _⟩ := hu; exact nomatch h
  | a :: t, T, h0, h =>
      (hf T h0 a (h a (by simp))).bind fun b =>
          (lw_eachM hf t _ (fun u hu => .inl (h0 u hu)) fun x hx u hu =>
                .inl (h x (by simp [hx]) u hu)).bind
              fun r => .pure fun u hu => by
      obtain ⟨y, hy, hu⟩ := hu
      rcases List.mem_cons.1 hy with e | e
      · exact .inl (.inr (e ▸ hu))
      · exact .inr ⟨y, e, hu⟩

section Rounds
variable {Y : Type} (hag : OnlyFb ag) (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
include hag

theorem lw_slotJoin {T : Tok → Prop} {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (z : SlotSt lam K Y (r :: s)) (hz : ∀ u, liveAcc z.2 u → T u) :
    Lw T (fun z' u => liveAcc z'.2 u) (slotJoin sMT t a w emb plJ i z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  refine lw_withTree hag sMT _ _ _ fun tr =>
    lw_gT hag t i _ (.inl (.inl (hz _ (.inl rfl))))
      (fun u hu => (rootOT_or tr u hu).imp .inr id) fun c => .pure fun u hu => ?_
  rcases hu with e | e | e | e
  · exact .inl (.inl (hz u (.inl e)))
  · exact .inr e
  · rcases List.mem_append.1 e with e | e
    · exact .inl (.inl (hz u (.inr (.inr (.inl e)))))
    · exact .inr (List.mem_singleton.1 e)
  · obtain ⟨x, hx, hu⟩ := e
    rcases List.mem_append.1 hx with e | e
    · exact .inl (.inl (hz u (.inr (.inr (.inr ⟨x, e, hu⟩)))))
    · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))

theorem lw_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (T : Tok → Prop), (∀ z ∈ zs, ∀ u, liveAcc z.2 u → T u) →
      Lw T (fun o u => (∃ z ∈ o.1, liveAcc z.2 u) ∨ u ∈ o.2) (joinM sMT t a w emb plJ i zs)
  | [], _, _ => .pure fun _ hu => by
      rcases hu with ⟨_, h, _⟩ | h
      · exact nomatch h
      · exact nomatch h
  | z :: zs, T, h =>
      (lw_slotJoin hag sMT t a w emb plJ i z (h z (by simp))).bind fun z' =>
          (lw_joinM a w emb plJ i zs _ fun x hx u hu => .inl (h x (by simp [hx]) u hu)).bind
              fun o => .pure fun u hu => by
      rcases hu with ⟨y, hy, hu⟩ | hu
      · rcases List.mem_cons.1 hy with e | e
        · exact .inl (.inr (e ▸ hu))
        · exact .inr (.inl ⟨y, e, hu⟩)
      · rcases List.mem_cons.1 hu with e | e
        · exact .inl (.inr (.inr (.inl e)))
        · exact .inr (.inr e)

omit hag in
/-- receiving a shared verifier message makes no token live -/
theorem liveAcc_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (z : SlotSt lam K Y (r :: s)) (u : Tok) (h : liveAcc (hear w bl noted z).2 u) :
    liveAcc z.2 u := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  rcases h with e | e | e | e
  · exact .inl e
  · exact .inr (.inl e)
  · exact .inr (.inr (.inl e))
  · refine .inr (.inr (.inr ?_))
    obtain ⟨x, hx, hu⟩ := e
    cases noted with
    | true => exact ⟨x, hx, hu⟩
    | false =>
      rcases List.mem_append.1 hx with e | e
      · exact ⟨x, e, hu⟩
      · rw [List.mem_singleton.1 e] at hu
        obtain ⟨_, e', _⟩ := hu
        exact nomatch e'

/-- What the relation must say at the searches of all rounds that are left. -/
def FitsSh (ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop) (t : Tag) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), embP =>
      ((∀ α g, w.grJ = some g → FitsLoop ag w.chal t (fun α => embP (.inl (.inr α))) α g) ∧
        (w.grJ = none →
          ∀ α (q : FbIn lam L t) r r', q.plain = embP (.inl (.inr α)) → ¬ ag (.fb t) q r r')) ∧
      ((∀ α g, w.gr0 = some g → FitsLoop ag w.chal t (fun α => embP (.inl (.inl α))) α g) ∧
        (w.gr0 = none →
          ∀ α (q : FbIn lam L t) r r', q.plain = embP (.inl (.inl α)) → ¬ ag (.fb t) q r r')) ∧
      FitsSh ag t s A W fun z => embP (.inr z)

/-- the live tokens of what the chains return -/
def liveOut (out : List (SlotAcc lam K Y) × Acc0) (u : Tok) : Prop :=
  (∃ acc ∈ out.1, liveAcc acc u) ∨ liveA0 out.2 u

omit hag in
theorem livePh_afterLo (ph : PhT) (u : Tok) (h : livePh ph.afterLo u) : livePh ph u := by
  cases ph <;> first | exact h | exact h.elim

/-- All chains of a batch are a `LiveW`, under `OnlyFb`, `FitsSh` and the hypotheses below. -/
theorem lw_chainT (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (T : Tok → Prop),
      FitsSh ag t s A W embP → (∃ u, T u) → (∀ z ∈ zs, ∀ u, liveAcc z.2 u → T u) →
      (∀ u, liveA0 a0 u → T u) → (∀ u, livePh ph u → T u) →
      Lw T liveOut (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
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
      by_cases hk : a.kind = .lo
      · rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        refine (lw_eachM (T0 := livePh ph) (lσ := fun z u => liveAcc z.2 u)
            (lτ := fun z u => liveAcc z.2 u)
            (fun T' hT z hz' => lw_slotLo hag sMT t cms xin a w _ _ i ph H.1.1 H.1.2 z hz' hT)
            zs T hph hz).bind fun zs' => ?_
        exact lw_chainT depthReq s A W _ _ (i + 1) _ _ zs' _ _ H.2.2 (h1.imp fun _ h => .inl h)
          (fun z hzm u hu => .inr ⟨z, hzm, hu⟩) (hnone _ a0 fun u hu => .inl (h0 u hu))
          fun u hu => .inl (hph u (livePh_afterLo ph u hu))
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine (lw_joinM hag sMT t a w _ _ i zs T hz).bind fun o =>
            (lw_reqT hag depthReq o.2 fun u hu => .inl (.inr (.inr hu))).bind fun rq =>
              lw_withTree hag sMT _ _ _ fun tr0 => ?_
          refine lw_fbG i _ _ w.gr0 (H.2.1.1 _) (fun h => H.2.1.2 h _)
            (h1.imp fun _ h => .inl (.inl (.inl h))) ((root_or rq).imp (fun h => .inl (.inr h)) id)
            (fun u hu => (rootOT_or tr0 u (by simpa using hu)).imp .inr id) fun nc dd bl tl => ?_
          refine lw_chainT depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2
            (h1.imp fun _ h => .inl (.inl (.inl (.inl h)))) (fun z hzm u hu => ?_)
            (fun u hu => ?_) fun u hu => .inr hu
          · obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
            exact .inl (.inl (.inl (.inr (.inl ⟨z0, hz0, liveAcc_hear w bl true z0 u hu⟩))))
          · rcases hu with e | ⟨x, hx, hu⟩ | ⟨x, e, hu⟩
            · rcases List.mem_append.1 e with e | e
              · exact .inl (.inl (.inl (.inl (h0 u (.inl e)))))
              · exact .inr (List.mem_singleton.1 e)
            · rcases List.mem_append.1 hx with e | e
              · exact .inl (.inl (.inl (.inl (h0 u (.inr (.inl ⟨x, e, hu⟩))))))
              · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))
            · exact .inl (.inl (.inr ((Option.some.inj e) ▸ hu)))
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine lw_withTree hag sMT _ _ _ fun tr0 => ?_
          refine lw_fbG i _ _ w.gr0 (H.2.1.1 _) (fun h => H.2.1.2 h _) (h1.imp fun _ h => .inl h)
            (.inl (.inl (hph tk0 rfl)))
            (fun u hu => (rootOT_or tr0 u (by simpa using hu)).imp .inr id) fun nc dd bl tl => ?_
          refine lw_chainT depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2
            (h1.imp fun _ h => .inl (.inl h)) (fun z hzm u hu => ?_)
            (fun u hu => ?_) fun u hu => .inr hu
          · obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
            exact .inl (.inl (hz z0 hz0 u (liveAcc_hear w bl false z0 u hu)))
          · rcases hu with e | ⟨x, hx, hu⟩ | e
            · rcases List.mem_append.1 e with e | e
              · exact .inl (.inl (h0 u (.inl e)))
              · exact .inr (List.mem_singleton.1 e)
            · rcases List.mem_append.1 hx with e | e
              · exact .inl (.inl (h0 u (.inr (.inl ⟨x, e, hu⟩))))
              · exact .inl (.inr ((List.mem_singleton.1 e) ▸ hu))
            · exact .inl (.inl (h0 u (.inr (.inr e))))
        | first =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          refine lw_chainT depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 h1
            (fun z hzm u hu => ?_) (hnone _ a0 h0) hph
          obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
          exact hz z0 hz0 u (liveAcc_hear w _ false z0 u hu)
        | aft =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          refine lw_chainT depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2.2 h1
            (fun z hzm u hu => ?_) (hnone _ a0 h0) hph
          obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
          exact hz z0 hz0 u (liveAcc_hear w _ false z0 u hu)

end Rounds

/-! ## A fact that is not about tokens: the list `toks` of a slot is not empty all along the chains,
if it is so at their start -/

section EndsW
variable {β : Type} {G : β → Prop}

local notation "En" => Ends (S := spec lam K L) (sp := split lam K L)

theorem ends_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} (hk : ∀ tr, En G (k tr)) :
    En G (withTree sMT has depth leaf k) := by
  cases has with
  | true => exact Ends.bind (ends_true _) fun tr _ => hk (some tr)
  | false => exact hk none

/-- Every value that `withTrees sMT ds leaf k` returns has G, if on every list of trees every value
of k has it. -/
theorem ends_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β},
      (∀ trs, En G (k trs)) → En G (withTrees sMT ds leaf k)
  | [], _, _, hk => hk []
  | _ :: ds, leaf, _, hk =>
    Ends.bind (ends_true _) fun tr _ =>
      ends_withTrees sMT ds (fun n => leaf (n + 1)) fun trs => hk (tr :: trs)

theorem ends_fbW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ m dd bl tl, En G (k m dd bl tl)) (n : ℕ) :
    ∀ (j : ℕ) (dd : List Tok), En G (fbW g chal t i tk us root hd' hinj emb α k n j dd) := by
  induction n with
  | zero => exact fun j dd bl tl => hk _ _ bl tl
  | succ n ih =>
    intro j dd bl tl
    show En G (if g.ok (chal bl) then _ else _)
    by_cases hok : g.ok (chal bl) = true
    · rw [if_pos hok]; exact hk _ _ bl tl
    · rw [if_neg hok]; exact ih _ _

theorem ends_fbG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (tk : Tok) (us : List Tok) (root : Option Tok) (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ m dd bl tl, En G (k m dd bl tl)) :
    En G (fbG gr chal t i tk us root hd' hinj emb α k) := by
  cases gr with
  | none => exact fun bl tl => hk _ _ bl tl
  | some g =>
    show En G (fbTG g chal t i tk us root hd' hinj emb α fun m => k (some m))
    unfold fbTG
    cases g.more with
    | zero => exact fun bl tl => hk _ _ bl tl
    | succ n =>
      intro bl tl
      show En G (if g.ok (chal bl) then _ else _)
      by_cases hok : g.ok (chal bl) = true
      · rw [if_pos hok]; exact hk _ _ bl tl
      · rw [if_neg hok]; exact ends_fbW g chal t i tk us root hd' hinj emb α (fun m dd bl tl => hk (some m) dd bl tl) n _ _

theorem ends_fbSlotG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (hk : ∀ m dd bl tl, En G (k m dd bl tl)) :
    En G (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph <;> exact ends_fbG gr chal t i _ _ root _ _ emb α hk

theorem ends_eachM {σ τ : Type} {f : σ → St lam K L τ} {Gτ : τ → Prop} (hf : ∀ a, En Gτ (f a)) :
    ∀ l : List σ, En (fun r => r.length = l.length ∧ ∀ b ∈ r, Gτ b) (eachM f l)
  | [] => ⟨rfl, fun _ h => nomatch h⟩
  | a :: t => Ends.bind (hf a) fun b hb => Ends.bind (ends_eachM hf t) fun r hr => ⟨congrArg (· + 1) hr.1, fun y hy => by
      rcases List.mem_cons.1 hy with e | e
      · exact e ▸ hb
      · exact hr.2 y e⟩

variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem ends_slotLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    En (fun z' => z'.2.toks ≠ []) (slotLo sMT t cms xin a w emb plJ i ph z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact ends_withTree _ _ _ _ fun tr => ends_fbSlotG _ _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl => by
    show acc.toks ++ [tl] ≠ []
    simp

theorem ends_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      En (fun o => ∀ z ∈ o.1, z.2.toks ≠ []) (joinM sMT t a w emb plJ i zs)
  | [] => fun _ h => nomatch h
  | z :: zs => Ends.bind (G := fun z' => z'.2.toks ≠ []) (by
      obtain ⟨⟨m, k⟩, acc⟩ := z
      dsimp only [slotJoin]
      exact ends_withTree _ _ _ _ fun tr => fun _ c => by
        show acc.toks ++ [c] ≠ []
        simp) fun z' hz' => Ends.bind (ends_joinM a w emb plJ i zs) fun o ho => fun y hy => by
      rcases List.mem_cons.1 hy with e | e
      · exact e ▸ hz'
      · exact ho y e

theorem toks_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (z : SlotSt lam K Y (r :: s)) :
    (hear w bl noted z).2.toks = z.2.toks := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  rfl

/-- The chains return slots whose lists of tokens (`toks`) are not empty, if they are given such
slots. -/
theorem ends_chainT (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      (∀ z ∈ zs, z.2.toks ≠ []) →
      En (fun out => ∀ acc ∈ out.1, acc.toks ≠ [])
        (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, zs, a0, hz => fun acc ha => by
      obtain ⟨z, hzm, rfl⟩ := List.mem_map.1 ha
      exact hz z hzm
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, hz => by
      have hh : ∀ (l : List (SlotSt lam K Y (r :: s))) bl noted,
          (∀ z ∈ l, z.2.toks ≠ []) → ∀ z ∈ l.map (hear w bl noted), z.2.toks ≠ [] := by
        intro l bl noted h z hzm
        obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
        rw [toks_hear]
        exact h z0 hz0
      by_cases hk : a.kind = .lo
      · rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        exact Ends.bind (ends_eachM (fun z => ends_slotLo sMT t cms xin a w _ _ i ph z) zs)
          fun zs' h => ends_chainT depthReq s A W _ _ (i + 1) _ _ zs' _ h.2
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          exact Ends.bind (ends_joinM sMT t a w _ _ i zs) fun o ho =>
              Ends.bind (ends_true _) fun rq _ =>
                  ends_withTree _ _ _ _ fun tr0 => ends_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            ends_chainT depthReq s A W _ _ (i + 1) _ _ _ _ (hh o.1 bl true ho)
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          exact ends_withTree _ _ _ _ fun tr0 =>
            ends_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
              ends_chainT depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs bl false hz)
        | first =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          exact ends_chainT depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs _ false hz)
        | aft =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          exact ends_chainT depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs _ false hz)

end EndsW

/-! ## The openings; the proof strings; one execution -/

section Prove

theorem lw_opensComp {T : Tok → Prop} {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (h : ∀ u, liveTT tr u → T u) :
    ∀ js : List ℕ, Lw T (fun _ _ => False) (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => .pure fun _ hu => hu.elim
  | j :: js => (lw_opensComp dec posAt o tr isRead f h js).bind fun f' => by
      show Lw _ _ (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => exact .pure fun _ hu => hu.elim
      | some p =>
        show Lw _ _ (if isRead p then _ else _)
        cases isRead p
        · exact .pure fun _ hu => hu.elim
        · exact (lw_openT tr j _ fun u hu => .inl (h u hu)).bind fun _ => .pure fun _ hu => hu.elim

theorem lw_opensOpt {T : Tok → Prop} {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → Option r.Pos) (depth : ℕ) (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (h : ∀ u, liveOT tr u → T u) :
    Lw T (fun _ _ => False) (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => exact .pure fun _ hu => hu.elim
  | some tr => exact lw_opensComp dec posAt o tr isRead f (fun u hu => h u ⟨tr, rfl, hu⟩) _

/-- The openings in the trees of one component are a `LiveW` whose value holds no live token, if
the tokens of each tree that meets a depth are taken as live (`opensTrees` stops at the shorter
list). -/
theorem lw_opensTrees {T : Tok → Prop} {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      (∀ x ∈ ds.zip trs, ∀ u, liveTT x.2 u → T u) →
      Lw T (fun _ _ => False) (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _, _ => .pure fun _ hu => hu.elim
  | _, _ :: _, [], _, _ => .pure fun _ hu => hu.elim
  | k, d :: ds, tr :: trs, f, h =>
    (lw_opensTrees dec posAt o isRead (k + 1) ds trs f
        fun x hx => h x (List.mem_cons_of_mem _ hx)).bind fun f' =>
      lw_opensComp dec (posAt k) o tr isRead f'
        (fun u hu => .inl (h (d, tr) List.mem_cons_self u hu)) _

/-- the same, if the tokens of all trees of the list are taken as live -/
theorem lw_opensTrees_all {T : Tok → Prop} {r : Round} (dec : DecidableEq r.Pos)
    (posAt : ℕ → ℕ → Option r.Pos) (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) (ds : List ℕ)
    (trs : List TTree) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : ∀ u, liveOTs trs u → T u) :
    Lw T (fun _ _ => False) (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) :=
  lw_opensTrees dec posAt o isRead k ds trs f
    fun x hx u hu => h u ⟨x.2, (List.of_mem_zip hx).2, hu⟩

theorem liveOT_headD (l : List (Option TTree)) (u : Tok) (h : liveOT (l.headD none) u) :
    liveTs l u := by
  cases l with
  | nil => obtain ⟨_, e, _⟩ := h; exact nomatch e
  | cons a t => exact ⟨a, by simp, h⟩

theorem liveTs_tail (l : List (Option TTree)) (u : Tok) (h : liveTs l.tail u) : liveTs l u := by
  obtain ⟨x, hx, hu⟩ := h
  exact ⟨x, List.mem_of_mem_tail hx, hu⟩

theorem lw_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s) (tjs t0s : List (Option TTree))
        (isRead : OPos s → Bool) (T : Tok → Prop),
      (∀ u, liveTs tjs u → T u) → (∀ u, liveTs t0s u → T u) →
      Lw T (fun _ _ => False) (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _, _, _, _ => .pure fun _ hu => hu.elim
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _, _, hj, h0 =>
      (lw_opensOpt _ _ _ _ _ _ _ fun u hu => h0 u (liveOT_headD _ u hu)).bind fun _ =>
          (lw_opensOpt _ _ _ _ _ _ _ fun u hu => .inl (hj u (liveOT_headD _ u hu))).bind fun _ =>
        (lw_opensB s A W τ tjs.tail t0s.tail _ _
            (fun u hu => .inl (.inl (hj u (liveTs_tail _ u hu))))
            fun u hu => .inl (.inl (h0 u (liveTs_tail _ u hu)))).bind
          fun _ => .pure fun _ hu => hu.elim

theorem lw_opensExtB {T : Tok → Prop} {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) (h : ∀ tr ∈ trees, ∀ u, liveTH tr u → T u) :
    ∀ ps : List E.Pos, Lw T (fun _ _ => False) (opensExtB (K := K) (L := L) we y trees isRead ps)
  | [] => .pure fun _ hu => hu.elim
  | p :: ps => (lw_opensExtB we y trees isRead h ps).bind fun f => by
      show Lw _ _
        (if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f)
      cases isRead p
      · exact .pure fun _ hu => hu.elim
      · refine (lw_openE _ _ _ fun u hu => .inl ?_).bind fun _ => .pure fun _ hu => hu.elim
        rw [List.getD_eq_getElem?_getD] at hu
        cases hj : trees[we.which p]? with
        | none => rw [hj] at hu; obtain ⟨_, e, _⟩ := hu; exact nomatch e
        | some tr => rw [hj] at hu; exact h tr (List.mem_of_getElem? hj) u hu

theorem mem_rootToks :
    ∀ (tjs t0s : List (Option TTree)) (u : Tok),
      u ∈ rootToks tjs t0s → (liveTs tjs u ∨ liveTs t0s u) ∨ u = 0
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | tj :: tjs, t0 :: t0s, u, h => by
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact (rootOT_or tj u h).imp (fun x => .inl ⟨tj, by simp, x⟩) id
      · exact (rootOT_or t0 u h).imp (fun x => .inr ⟨t0, by simp, x⟩) id
    · rcases mem_rootToks tjs t0s u h with (⟨x, hx, hu⟩ | ⟨x, hx, hu⟩) | e
      · exact .inl (.inl ⟨x, List.mem_cons_of_mem _ hx, hu⟩)
      · exact .inl (.inr ⟨x, List.mem_cons_of_mem _ hx, hu⟩)
      · exact .inr e

theorem take_drop_app (w x : List Bits) (n m : ℕ) (h : n + m ≤ w.length) :
    ((w ++ x).drop n).take m = (w.drop n).take m := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem getD_app (w x : List Bits) (i : ℕ) (h : i < w.length) :
    (w ++ x).getD i [] = w.getD i [] := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem headD_app (w x : List Bits) (h : 0 < w.length) : (w ++ x).headD [] = w.headD [] := by
  cases w with
  | nil => exact absurd h (by simp)
  | cons a t => rfl

variable (hag : OnlyFb ag) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- Under the hypotheses below: the proof string of a slot (`finishSlot`) is a `LiveW`; its one
reveal (in this sense: the `Step.reveal` in the body of `finishSlot`; `openT`, `openE` are further
ones) names the tails of the failed attempts too; nothing of their strings is used. -/
theorem lw_finishSlot {T : Tok → Prop} (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (hT : ∀ tr ∈ trees, ∀ u, liveTH tr u → T u)
    (h0 : ∀ u, liveA0 a0 u → T u) (ha : ∀ u, liveAcc acc u → T u) (hne : acc.toks ≠ []) :
    Lw T (fun _ _ => False) (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · exact .pure fun _ hu => hu.elim
  · have hl : 0 < acc.toks.length := List.length_pos_of_ne_nil hne
    refine LiveW.revealMore
      (ts := acc.toks.headD 0 ::
          (rootToks acc.trees a0.trees ++ (a0.req.map fun rq => pathOf rq.levels j).getD [] ++
            (a0.req.map TTree.root).toList ++
            (a0.req.map fun rq => ancOf rq.levels j).getD [] ++ acc.toks ++ a0.toks))
      (more := acc.dead ++ a0.dead) (fun u hu => ?_) (fun v x y hv => ?_) fun vs => ?_
    · rcases List.mem_cons.1 hu with e | hu
      · exact (headD_or acc.toks).imp
          (fun h => ha u (.inr (.inr (.inl (e ▸ h))))) fun h => e.trans h
      · simp only [List.mem_append] at hu
        rcases hu with ((((hu | hu) | hu) | hu) | hu) | hu
        · exact (mem_rootToks _ _ u hu).imp
            (fun h => h.elim (fun h => ha u (.inr (.inr (.inr h)))) fun h => h0 u (.inr (.inl h)))
            id
        · cases hr : a0.req with
          | none => rw [hr] at hu; exact nomatch hu
          | some rq => rw [hr] at hu; exact (mem_pathOf _ _ u hu).imp (fun h => h0 u (.inr (.inr ⟨rq, hr, .inl h⟩))) id
        · exact (rootOT_or a0.req u hu).imp (fun h => h0 u (.inr (.inr h))) id
        · cases hr : a0.req with
          | none => rw [hr] at hu; exact nomatch hu
          | some rq => rw [hr] at hu; exact (mem_ancOf _ _ u hu).imp (fun h => h0 u (.inr (.inr ⟨rq, hr, .inl h⟩))) id
        · exact .inl (ha u (.inr (.inr (.inl hu))))
        · exact .inl (h0 u (.inl hu))
    · simp only [List.length_cons, List.length_append] at hv
      rw [headD_app v x (by omega), headD_app v y (by omega), take_drop_app v x _ _ (by omega),
        take_drop_app v y _ _ (by omega), take_drop_app v x _ _ (by omega),
        take_drop_app v y _ _ (by omega), getD_app v x _ (by omega), getD_app v y _ (by omega)]
    · exact (lw_opensB _ _ _ _ _ _ _ _ (fun u hu => ha u (.inr (.inr (.inr hu))))
        fun u hu => h0 u (.inr (.inl hu))).bind fun f =>
          (lw_opensExtB _ _ _ _ (fun tr htr u hu => .inl (hT tr htr u hu)) _).bind
            fun g => .pure fun _ hu => hu.elim

/-- the proof strings of all slots. Of an empty slot nothing is asked: nothing is done for it. -/
theorem lw_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (T : Tok → Prop),
      (∀ tr ∈ trees, ∀ u, liveTH tr u → T u) → (∀ u, liveA0 a0 u → T u) →
      (∀ acc ∈ zs, acc.x ≠ none → ∀ u, liveAcc acc u → T u) →
      (∀ acc ∈ zs, acc.x ≠ none → acc.toks ≠ []) →
      Lw T (fun _ _ => False) (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [], _, _, _, _, _ => .pure fun _ hu => hu.elim
  | j, acc :: zs, T, hT, h0, ha, hne => LiveW.bind (TP := fun _ _ => False) (by
      cases hx : acc.x with
      | none => exact .pure fun _ hu => hu.elim
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show Lw T _ (if fl j then _ else _)
        cases fl j
        · exact .pure fun _ hu => hu.elim
        · exact lw_finishSlot Q H wq wp trees w c0 a0 j x cj acc hT h0 (ha acc (by simp) (by rw [hx]; simp)) (hne acc (by simp) (by rw [hx]; simp))) fun _ =>
      (lw_finishAll fl c0 a0 (j + 1) zs _ (fun tr htr u hu => .inl (hT tr htr u hu))
          (fun u hu => .inl (h0 u hu)) (fun x hx hn u hu => .inl (ha x (by simp [hx]) hn u hu))
          fun x hx hn => hne x (by simp [hx]) hn).bind
        fun _ => .pure fun _ hu => hu.elim

theorem lw_initSlot {T : Tok → Prop} (c0 : H.Coin0) (x : Option Y) :
    Lw T (fun z u => liveAcc z.2 u) (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) :=
  (lw_drawT wp.coin).bind fun _ => .fresh _ fun salt => .pureZ ⟨salt, .inr rfl⟩ fun u hu => by
    rcases hu with e | e | e | ⟨_, h, _⟩
    · exact .inl (.inr e)
    · exact .inr e
    · exact .inl (.inr (List.mem_singleton.1 e))
    · exact nomatch h

theorem ends_initSlot (c0 : H.Coin0) (x : Option Y) :
    Ends (fun z => z.2.toks ≠ []) (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) :=
  Ends.bind (ends_true _) fun _ _ => fun salt => by
    show [salt] ≠ []
    simp

include hag in
/-- For every ag with `OnlyFb`, `FitsSh`, under hT: one execution of the compiled prover is a
`LiveW ag`; in particular, started on a store that holds all tokens taken as live, after two answers
that ag relates it never uses the new tail. It needs a slot, or a live token. -/
theorem lw_proveB {T : Tok → Prop} (hF : FitsSh ag t Q.loc.shape Q.ann wq.sh embP)
    (hT : ∀ tr ∈ trees, ∀ u, liveTH tr u → T u) (fl : ℕ → Bool)
    (xs : List (Option Y)) (h1 : xs ≠ [] ∨ ∃ u, T u) :
    Lw T (fun _ _ => False) (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) := by
  unfold proveB
  refine (lw_drawT wp.coin0).bind fun c0 => ?_
  refine LiveW.bindG (G := fun zs => zs.length = xs.length ∧ ∀ z ∈ zs, z.2.toks ≠ [])
    (lw_eachM (T0 := fun _ => False) (lσ := fun _ _ => False) (lτ := fun z u => liveAcc z.2 u)
      (fun _ _ x _ => lw_initSlot sFS Q H wp w c0 x) xs _ (fun _ h => h.elim) fun _ _ _ h => h.elim)
    ?_ fun zs hzs => ?_
  · exact ends_eachM (fun x => ends_initSlot sFS Q H wp w c0 x) xs
  · refine LiveW.bindG (G := fun out => ∀ acc ∈ out.1, acc.toks ≠ [])
      (lw_chainT hag sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ _ hF ?_
        (fun z hz u hu => .inr ⟨z, hz, hu⟩) (fun u hu => ?_) fun _ hu => hu.elim)
      (ends_chainT sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hzs.2) fun out ho => ?_
    · rcases h1 with h1 | ⟨u, hu⟩
      · cases zs with
        | nil => exact absurd (List.length_eq_zero_iff.1 hzs.1.symm) h1
        | cons z zs => exact ⟨z.2.tk, .inr ⟨z, by simp, .inl rfl⟩⟩
      · exact ⟨u, .inl (.inl hu)⟩
    · rcases hu with h | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact nomatch h
      · exact nomatch h
      · exact nomatch h
    · exact lw_finishAll Q H wq wp trees w fl c0 out.2 0 out.1 _
        (fun tr htr u hu => .inl (.inl (.inl (hT tr htr u hu)))) (fun u hu => .inr (.inr hu))
        (fun acc ha _ u hu => .inr (.inl ⟨acc, ha, hu⟩)) fun acc ha _ => ho acc ha

end Prove

end Compile.Batch.Dead
