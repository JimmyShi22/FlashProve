-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Chain.lean: THE CHAIN OF A COMPILED RUN AS A TOKEN PROGRAM: it keeps the rules, and
what it adds to the list of evaluations.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

By recursion on the rounds (safe_chainT), along the text of chainT (Johnson/TokenSide/Chain.lean),
which has four arms, each a lemma of its own that is handed the statement on the rounds behind
(ChainGoal; safe_roundOne serves the first two arms, safe_roundJoin the third): one Fiat-Shamir
query over the slot's own component; one over the shared component; the joining round; no format. In
each arm: the round's trees (Johnson/TokenRel/Trees.lean), along which the invariant stays
(CI.trees); the marked evaluations, each of which adds its tail to the closed list (ClV.mark,
ClV.hit, safe_climbT); the invariant of the next phase (act_one); the rounds behind, by recursion;
then the runs are laid together and the counts are added (mChain_step, mChain_join). A search that
runs out ends the chain with no value: then nothing is owed but the rules, the counts, and that each
evaluation that was added is charged to a new token, the first salt or a token of the phase (OldOr).
If the chain has a value, beside ChainEnd: its tokens are new; each evaluation that it has added is
a leaf that is charged to none of the chain's tokens, or no leaf and charged to one of them (Cls);
each kept tree has LeafAt (KeptAt).
Follows the pattern of Compile/Batch/DisciplineChain.lean, DisciplineJoin.lean and
DisciplineChainAll.lean, at one slot.

-/
import Johnson.TokenRel.Act

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {bl bf : ℕ}
  {sd : (t : Tag) → FbIn lam L t → Prop}

/-- of an evaluation: it is charged to a token from n on, or to one in Cc -/
def OldOr (Cc : Tok → Prop) (n : ℕ) (e : Ev (typedOracleFamily lam K L)) : Prop := n ≤ e.charged ∨ Cc e.charged

/-- What is shown of the chain over the rounds s: from every round number, phase, list V and state
with the invariant. -/
def ChainGoal (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop) (t : Tag) (cms : List (Dig lam))
    (x : Option X) (ℓ : ℕ) (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L)
    (cap : ℕ → ℕ) (sFS : ℕ) (sv : Bits) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : Prop :=
  ∀ (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
      (i : ℕ) (ph : PhT) (σ : Strat s Unit) (V : List Tok) (n : ℕ) (d : DSt (typedOracleFamily lam K L)),
    n ≤ d.vals.length → TidyO (rulesT K L lam bl bf sd) d → CI d t salt sFS V ph →
    d.val salt = sv →
    SafeO (rulesT K L lam bl bf sd) (chainT t cms x ℓ pre salt cd cap s A W embS embP i ph σ) d
      fun out d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (PhTok salt ph) (PhTok salt ph) noTok (eRun s A W)
        (mChain t s A W cap cd.path.length i ph) d d' ∧
      Adds (OldOr (PhTok salt ph) d.vals.length) d d' ∧
      ∀ z, out = Res.ok z → ChainEnd n d' salt V z ∧ (∀ u ∈ z.toks, d.vals.length ≤ u) ∧
        Adds (Cls d.vals.length (V ++ z.toks)) d d' ∧
        KeptAt d' (fun i b => pre i b sv) s i z.kept

/-! ### The list of the joining round's tokens -/

theorem mem_join_perm {V r2 dead : List Tok} {c dk tl : Tok} (u : Tok) :
    u ∈ V ++ (c :: dk :: (r2 ++ tl :: dead)) ↔ u ∈ (tl :: dead) ++ (r2 ++ dk :: c :: V) := by
  simp only [List.mem_append, List.mem_cons]
  tauto

theorem mem_join_ph {V r2 dead : List Tok} {c dk tl u : Tok} (hu : u ∈ phToks (.shr tl c)) :
    u ∈ V ++ (c :: dk :: (r2 ++ tl :: dead)) := by
  simp only [phToks, List.mem_cons, List.not_mem_nil, or_false] at hu
  simp only [List.mem_append, List.mem_cons]
  tauto

theorem mem_join_path {r2 dead : List Tok} {c dk tl u : Tok} (hu : u = dk ∨ u ∈ r2) :
    u ∈ c :: dk :: (r2 ++ tl :: dead) := by
  simp only [List.mem_append, List.mem_cons]
  tauto

section Arms
variable (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ) (pre : ℕ → Bool → Bits → Bits)
  (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) (sFS : ℕ) (sv : Bits) {r : Round} {s : Shape}
  (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (eS : (p : OPos s) → OSym s p → Body L) (eP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
  (k : r.Chal → Strat s Unit) (emb : (p : r.Pos) → r.Sym p → Body L) (orc : r.Orc) (i : ℕ)
  (V : List Tok) (n : ℕ) (d : DSt (typedOracleFamily lam K L))

/-- **A round with one Fiat-Shamir query**, over the slot's own component (b = true) or the shared
one. -/
theorem safe_roundOne (hbl : bl ≤ ℓ) (hbS : bf ≤ sFS) (hbL : bf ≤ lam)
    (ih : ChainGoal bl bf sd t cms x ℓ pre salt cd cap sFS sv s A W) (hn : n ≤ d.vals.length)
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hsv : d.val salt = sv)
    (ph : PhT) (hci : CI d t salt sFS V ph) (b : Bool) {P : Type}
    (gr : Option (GrW r.Chal P)) (ds : List ℕ) (posAt : ℕ → ℕ → Option r.Pos)
    {cms' : List (Dig lam)} {x' : Option X} {tk : Tok} {us : List Tok}
    {hd₀ : List Bits → Bits → Head lam X}
    {inj : ∀ (xl : Option X) (vs : List Bits), Function.Injective fun v => (hd₀ vs v).withLate xl}
    {next : Tok → PhT} (heq : actT cms' x' salt a.kind ph = some (.one tk us hd₀ inj b next))
    (hd' : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd' vs))
    (f : P → PlainPart (shapeOf L t) (annOf L t)) (α₀ : P)
    (kp : Hit lam K P → List (TreeT lam L) → r.Msg × List (TreeT lam L) × List (TreeT lam L))
    (hk1 : ∀ q Ts T, T ∈ (kp q Ts).2.1 → b = false ∧ T ∈ Ts)
    (hk2 : ∀ q Ts T, T ∈ (kp q Ts).2.2 → b = true ∧ T ∈ Ts)
    (hnl : nLv ds ≤ nLv w.depthJ + nLv w.depth0)
    (hb : (b = true ∧ a.kind = .lo) ∨ (b = false ∧ a.kind = .sh) →
      gr.isSome = TokenSide.hasTest w) :
    SafeO (rulesT K L lam bl bf sd)
      ((treesT (K := K) ℓ [salt] (fun vs => pre i b (vs.headD [])) cd.pad posAt emb orc 0 ds).bind
        fun Ts =>
        (fsT gr (cap i) w.chal (fun n α => fbT (K := K) t n i tk us hd' hinj
          (Ts.map TreeT.root) (f α)) α₀).bind <| onFsT i fun q =>
          (chainT t cms x ℓ pre salt cd cap s A W eS eP (i + 1) (next q.tl)
            (k (w.chal q.bl))).bind fun r' =>
          .pure (r'.map (consT (w.chal q.bl) (kp q Ts) none (q.tl :: q.dead)))) d
      fun out d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (PhTok salt ph) (PhTok salt ph) noTok (eRun (r :: s) (a, A) (w, W))
        (mChain t (r :: s) (a, A) (w, W) cap cd.path.length i ph) d d' ∧
      Adds (OldOr (PhTok salt ph) d.vals.length) d d' ∧
      ∀ z, out = Res.ok z → ChainEnd n d' salt V z ∧ (∀ u ∈ z.toks, d.vals.length ≤ u) ∧
        Adds (Cls d.vals.length (V ++ z.toks)) d d' ∧
        KeptAt d' (fun i b => pre i b sv) (r :: s) i z.kept := by
  have hs : salt < d.vals.length := (hci.deps salt hci.salt_mem).1
  have hus1 : ∀ u ∈ [salt], u < d.vals.length := fun u hu => by
    rw [List.mem_singleton.mp hu]
    exact hs
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_treesT hbl [salt] _ cd.pad posAt emb orc
    (pre i b sv) ds 0 d hd hus1 (by show pre i b (d.val salt) = _; rw [hsv])))
  rintro Ts d₁ ⟨hd₁, hr₁, hk₁, ha₁, hT₁⟩
  have hci₁ := hci.trees hr₁ hk₁
  have ha := act_one hbS hbL hci₁ heq
  obtain ⟨nb, hnb, hlive⟩ := ha.live
  have htkV : tk ∈ V := PhTok.mem hci₁ ha.tk_ph
  have husV : ∀ u ∈ us, u ∈ V := fun u hu => hci₁.ph_mem u (ha.us_ph u hu)
  have hb' : gr.isSome = TokenSide.hasTest w := hb ha.own_eq
  have hj : ∀ v, jOf (next v) s A ≤ jOf ph (r :: s) (a, A) := fun v => by
    rcases ha.jn with ⟨hk', e⟩ | e
    · rw [e, jOf_lo hk']
    · rw [e]
      exact Nat.zero_le _
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_fsT gr (cap i) w.chal t i tk us hd' hinj _ f α₀
    V hnb hd₁ (fun u hu => (hci₁.deps u (husV u hu)).1) ha.htu husV hlive (hci₁.deps tk htkV).2))
  rintro o d₂ ⟨hd₂, hr₂, ha₂, hq⟩
  have h01 : d.vals.length ≤ d₁.vals.length := hr₁.length_le
  have h12 : d₁.vals.length ≤ d₂.vals.length := hr₂.length_le
  -- the runs so far, and any run behind them, as one
  have key : ∀ (Cc₃ : Tok → Prop) (ph' : PhT) (d₃ : DSt (typedOracleFamily lam K L)),
      (∀ u, Cc₃ u → PhTok salt ph u ∨ d₁.vals.length ≤ u) →
      jOf ph' s A ≤ jOf ph (r :: s) (a, A) →
      RunO Cc₃ Cc₃ noTok (eRun s A W) (mChain t s A W cap cd.path.length (i + 1) ph') d₂ d₃ →
      Adds (OldOr Cc₃ d₂.vals.length) d₂ d₃ →
      RunO (PhTok salt ph) (PhTok salt ph) noTok (eRun (r :: s) (a, A) (w, W))
        (mChain t (r :: s) (a, A) (w, W) cap cd.path.length i ph) d d₃ ∧
      Charges (PhTok salt ph) d₁ d₃ ∧ Adds (OldOr (PhTok salt ph) d₁.vals.length) d₁ d₃ ∧
      Adds (OldOr (PhTok salt ph) d.vals.length) d d₃ := fun Cc₃ ph' d₃ hC hj' hr₃ ha₃ => by
    have R13 := run_seq (run_cc (Cc := PhTok salt ph) (Ch := PhTok salt ph) hr₂
      (fun u hu => Or.inl (hu ▸ ha.tk_ph))
      (fun u hu => Or.inl (hu.elim (fun h => h ▸ ha.tk_ph) fun h => Or.inr (ha.us_ph u h))))
      hr₃ hC hC
    have R03 := run_seq (run_cc (Cc := PhTok salt ph) (Ch := PhTok salt ph) hr₁
      (fun _ h => h.elim) (fun u hu => Or.inl (Or.inl (List.mem_singleton.mp hu))))
      R13 (fun _ h => Or.inl h) (fun _ h => Or.inl h)
    have A13 : Adds (OldOr (PhTok salt ph) d₁.vals.length) d₁ d₃ :=
      (ha₂.mono fun e _ h => Or.inr (h.2 ▸ ha.tk_ph)).trans (ha₃.mono fun e _ h =>
        h.elim (fun h => Or.inl (h12.trans h)) fun h => (hC _ h).symm)
    refine ⟨R03.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
      (fun o => ?_) (fun o => mChain_step t a A w W cap _ i ph ph' _ _ hnl hb' hj' o),
      R13.charges, A13, (ha₁.mono fun e _ h => Or.inl h.2).trans
        (A13.mono fun e _ h => h.imp_left fun h => h01.trans h)⟩
    show cnt1 (S := typedOracleFamily lam K L) OracleName.node (nLv ds) o + (0 + eRun s A W o) ≤ _
    rw [Nat.zero_add]
    exact eRun_step a A w W _ hnl o
  cases o with
  | none =>
      obtain ⟨R, _, _, A03⟩ := key noTok (next 0) d₂ (fun _ h => h.elim) (hj 0) (Run.refl d₂)
        (Adds.refl _ d₂)
      exact ⟨hd₂, R, A03, fun _ h => nomatch h⟩
  | some q =>
      have hq := hq q rfl
      have hts : ∀ u ∈ q.tl :: q.dead, d₁.vals.length ≤ u := fun u hu => by
        rcases List.mem_cons.mp hu with rfl | h
        · exact hq.new
        · exact (hq.dead u h).1
      have hci₂ : CI d₂ t salt sFS (V ++ (q.tl :: q.dead)) (next q.tl) :=
        { salt_mem := List.mem_append_left _ hci.salt_mem
          ph_mem := fun u hu => (ha.next_toks _ u hu).elim
            (fun h => h ▸ List.mem_append_right _ List.mem_cons_self)
            (fun h => List.mem_append_left _ (hci.ph_mem u h))
          deps := (ClV.hit hci₁.deps hr₂.charges hq).perm fun u => by
            simp only [List.mem_append]
            exact Or.comm
          ph_ok := ha.next_ok _ _ d₂ q.tl hr₂.grows hq.unt hq.len hq.new }
      refine SafeO.bind _ _ d₂ (SafeO.mono ?_ _ d₂ (ih eS eP (i + 1) (next q.tl) _
        (V ++ (q.tl :: q.dead)) n d₂ (hn.trans (h01.trans h12)) hd₂ hci₂
        (by rw [val_of_prefix (hr₁.grows.vals.trans hr₂.grows.vals) hs]; exact hsv)))
      rintro r' d₃ ⟨hd₃, hr₃, ha₃, hz⟩
      obtain ⟨R, C13, A13, A03⟩ := key (PhTok salt (next q.tl)) (next q.tl) d₃ (fun u hu => by
        rcases hu with rfl | hu
        · exact Or.inl (Or.inl rfl)
        · rcases ha.next_toks _ u hu with rfl | h
          · exact Or.inr hq.new
          · exact Or.inl (Or.inr h)) (hj _) hr₃ ha₃
      refine ⟨hd₃, R, A03, fun z' hz' => ?_⟩
      cases r' with
      | noFormat => exact nomatch hz'
      | ranOut _ => exact nomatch hz'
      | ok z =>
          obtain ⟨hE, hloc, hcls, hK⟩ := hz z rfl
          have e := Res.ok.inj hz'
          subst e
          have hold : ∀ u, PhTok salt ph u → u < d.vals.length := fun u hc =>
            (hci.deps u (PhTok.mem hci hc)).1
          have hloc' : ∀ u ∈ (q.tl :: q.dead) ++ z.toks, d₁.vals.length ≤ u := fun u hu =>
            (List.mem_append.mp hu).elim (hts u) fun h => h12.trans (hloc u h)
          have hleaf : ∀ T ∈ Ts, LeafAt d₃ T (pre i b sv) := fun T hT =>
            LeafAt.adds (hT₁ T hT).2.2 (fun u hu => TreeOKT.lt (hT₁ T hT).1 hu) C13.vals A13
              fun e he hc => he.elim
                (fun h => absurd (TreeOKT.lt (hT₁ T hT).1 hc) (Nat.not_lt.mpr h))
                (fun h => absurd ((hT₁ T hT).2.1 _ hc) (Nat.not_le.mpr (hold _ h)))
          refine ⟨⟨?_, ?_, fun T hT => ?_, hE.kept⟩, fun u hu => h01.trans (hloc' u hu), ?_,
            fun T hT => ?_, fun T hT => ?_, hK⟩
          · show ∀ u ∈ V ++ ((q.tl :: q.dead) ++ z.toks), u < d₃.vals.length ∧
              Deps d₃ u (V ++ ((q.tl :: q.dead) ++ z.toks))
            rw [← List.append_assoc]
            exact hE.deps
          · exact fun u hu => hn.trans (h01.trans (hloc' u hu))
          · have hT' := hT₁ T ((List.mem_append.mp hT).elim (fun h => (hk1 q Ts T h).2)
              fun h => (hk2 q Ts T h).2)
            exact ⟨TreeOKT.keeps hT'.1 C13 fun u hu hc =>
                absurd (hT'.2.1 u hu) (Nat.not_le.mpr (hold u hc)),
              fun u hu => hn.trans (hT'.2.1 u hu)⟩
          · show Adds (Cls d.vals.length (V ++ ((q.tl :: q.dead) ++ z.toks))) d d₃
            exact ((ha₁.mono fun e he h => Or.inl ⟨h.1, h.2, fun hm => by
                rcases List.mem_append.mp hm with hm | hm
                · exact absurd h.2 (Nat.not_le.mpr (hci.deps _ hm).1)
                · exact absurd (hloc' _ hm) (Nat.not_le.mpr (hd₁.charged_lt e he))⟩).trans
              (ha₂.mono fun e _ h => Or.inr ⟨h.1, h.2 ▸ List.mem_append_left _ htkV⟩)).trans
              (hcls.mono fun e _ h => by
                rw [← List.append_assoc]
                exact h.imp_left fun h => ⟨h.1, (h01.trans h12).trans h.2.1, h.2.2⟩)
          · have h := hk1 q Ts T hT
            have h' := hleaf T h.2
            rw [h.1] at h'
            exact h'
          · have h := hk2 q Ts T hT
            have h' := hleaf T h.2
            rw [h.1] at h'
            exact h'

/-- **The joining round.** -/
theorem safe_roundJoin (hbl : bl ≤ ℓ) (hbS : bf ≤ sFS) (hbL : bf ≤ lam)
    (ih : ChainGoal bl bf sd t cms x ℓ pre salt cd cap sFS sv s A W) (hn : n ≤ d.vals.length)
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hsv : d.val salt = sv)
    (tk : Tok) (hci : CI d t salt sFS V (.loc tk)) (hk : a.kind = .sh)
    (plJ : PlainPart (shapeOf L t) (annOf L t)) (f : a.P0 → PlainPart (shapeOf L t) (annOf L t)) (α₀ : a.P0)
    (msg : Hit lam K a.P0 → r.Msg) :
    SafeO (rulesT K L lam bl bf sd)
      ((treesT (K := K) ℓ [salt] (fun vs => pre i true (vs.headD [])) cd.pad w.posAtJ emb orc 0
        w.depthJ).bind fun TJ =>
      (treesT (K := K) ℓ [salt] (fun vs => pre i false (vs.headD [])) cd.pad w.posAt0 emb orc 0
        w.depth0).bind fun T0 =>
      (gT (K := K) t i tk (TJ.map TreeT.root) plJ).bind fun c =>
      (rleafT (K := K) (L := L) c cd.rsalt).bind fun dk =>
      (climbT (K := K) (L := L) cd.path cd.slot dk).bind fun rq =>
      (fsT w.gr0 (cap i) w.chal (fun n α => fbT (K := K) t n i rq.1 []
          (fun _ v => .f4 cms v) (fun _ => f4_inj cms) (T0.map TreeT.root) (f α)) α₀).bind <|
        onFsT i fun q =>
        (chainT t cms x ℓ pre salt cd cap s A W eS eP (i + 1) (.shr q.tl c)
          (k (w.chal q.bl))).bind fun r' =>
        .pure (r'.map (consT (w.chal q.bl) (msg q, T0, TJ) (some rq.1)
          (c :: dk :: (rq.2 ++ q.tl :: q.dead))))) d
      fun out d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (PhTok salt (.loc tk)) (PhTok salt (.loc tk)) noTok (eRun (r :: s) (a, A) (w, W))
        (mChain t (r :: s) (a, A) (w, W) cap cd.path.length i (.loc tk)) d d' ∧
      Adds (OldOr (PhTok salt (.loc tk)) d.vals.length) d d' ∧
      ∀ z, out = Res.ok z → ChainEnd n d' salt V z ∧ (∀ u ∈ z.toks, d.vals.length ≤ u) ∧
        Adds (Cls d.vals.length (V ++ z.toks)) d d' ∧
        KeptAt d' (fun i b => pre i b sv) (r :: s) i z.kept := by
  have hs : salt < d.vals.length := (hci.deps salt hci.salt_mem).1
  have hus1 : ∀ u ∈ [salt], u < d.vals.length := fun u hu => by
    rw [List.mem_singleton.mp hu]
    exact hs
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_treesT hbl [salt] _
    cd.pad w.posAtJ emb orc (pre i true sv) w.depthJ 0 d hd hus1
    (by show pre i true (d.val salt) = _; rw [hsv])))
  rintro TJ d₁ ⟨hd₁, hr₁, hk₁, ha₁, hT₁⟩
  have h01 : d.vals.length ≤ d₁.vals.length := hr₁.length_le
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_treesT hbl [salt] _
    cd.pad w.posAt0 emb orc (pre i false sv) w.depth0 0 d₁ hd₁
    (fun u hu => lt_of_lt_of_le (hus1 u hu) h01)
    (by show pre i false (d₁.val salt) = _; rw [val_of_prefix hr₁.grows.vals hs, hsv])))
  rintro T0 d₂ ⟨hd₂, hr₂, hk₂, ha₂, hT₂⟩
  have h12 : d₁.vals.length ≤ d₂.vals.length := hr₂.length_le
  have hci₂ := (hci.trees hr₁ hk₁).trees hr₂ hk₂
  obtain ⟨_, hunt, hlen⟩ := hci₂.ph_ok
  have htkV : tk ∈ V := hci.ph_mem tk List.mem_cons_self
  have h02 : d.vals.length ≤ d₂.vals.length := h01.trans h12
  refine SafeO.bind _ _ d₂ (SafeO.mono ?_ _ d₂ (safe_gT t i tk _ _ hd₂ hunt hlen))
  rintro c d₃ hm₃
  have hV₃ : ClV d₃ (c :: V) :=
    ClV.mark hci₂.deps hm₃ htkV fun _ h => absurd h List.not_mem_nil
  refine SafeO.bind _ _ d₃ (SafeO.mono ?_ _ d₃
    (safe_rleafT c cd.rsalt hm₃.tidy hm₃.unt hm₃.len))
  rintro dk d₄ hm₄
  have hV₄ : ClV d₄ (dk :: c :: V) :=
    hV₃.mark hm₄ List.mem_cons_self fun _ h => absurd h List.not_mem_nil
  refine SafeO.bind _ _ d₄ (SafeO.mono ?_ _ d₄ (safe_climbT cd.path cd.slot dk (dk :: c :: V)
    d₄ hm₄.tidy hV₄ List.mem_cons_self hm₄.unt hm₄.len))
  rintro rq d₅ ⟨hd₅, hr₅, hV₅, hmem, hu₅, hl₅, hnew₅, ha₅⟩
  refine SafeO.bind _ _ d₅ (SafeO.mono ?_ _ d₅ (safe_fsT w.gr0 (cap i) w.chal t i rq.1 [] _ _ _
    _ _ (rq.2 ++ dk :: c :: V) hbL hd₅ (fun _ h => absurd h List.not_mem_nil)
    List.not_mem_nil (fun _ h => absurd h List.not_mem_nil) ⟨fun _ => hu₅.freeAt _, hl₅⟩
    (hu₅.deps _)))
  rintro o d₆ ⟨hd₆, hr₆, ha₆, hq⟩
  -- numbers
  have hc2 : d₂.vals.length ≤ c := le_of_eq hm₃.eq.symm
  have hc3 : c < d₃.vals.length := hm₃.unt.lt
  have hdk : d₃.vals.length ≤ dk := le_of_eq hm₄.eq.symm
  have h23 : d₂.vals.length ≤ d₃.vals.length := hc2.trans (Nat.le_of_lt hc3)
  have h34 : d₃.vals.length ≤ d₄.vals.length := hm₄.run.length_le
  have h45 : d₄.vals.length ≤ d₅.vals.length := hr₅.length_le
  have h56 : d₅.vals.length ≤ d₆.vals.length := hr₆.length_le
  have hrq2 : ∀ u ∈ rq.2, d₃.vals.length ≤ u := fun u hu => h34.trans (hnew₅ u hu)
  have hrq : d₃.vals.length ≤ rq.1 := by
    rcases hmem with h | h
    · rw [h]
      exact hdk
    · exact hrq2 _ h
  -- the runs so far, and any run behind them, as one
  have key : ∀ (Cc7 : Tok → Prop) (ph' : PhT) (d7 : DSt (typedOracleFamily lam K L)),
      (∀ u, Cc7 u → PhTok salt (.loc tk) u ∨ d₂.vals.length ≤ u) → jOf ph' s A = 0 →
      RunO Cc7 Cc7 noTok (eRun s A W) (mChain t s A W cap cd.path.length (i + 1) ph') d₆ d7 →
      Adds (OldOr Cc7 d₆.vals.length) d₆ d7 →
      RunO (PhTok salt (.loc tk)) (PhTok salt (.loc tk)) noTok (eRun (r :: s) (a, A) (w, W))
        (mChain t (r :: s) (a, A) (w, W) cap cd.path.length i (.loc tk)) d d7 ∧
      Charges (PhTok salt (.loc tk)) d₂ d7 ∧
      Adds (OldOr (PhTok salt (.loc tk)) d₂.vals.length) d₂ d7 ∧
      Adds (OldOr (PhTok salt (.loc tk)) d.vals.length) d d7 :=
      fun Cc7 ph' d7 hC hj' hr7 ha7 => by
    have htk : ∀ u, u = tk → PhTok salt (.loc tk) u ∨ d₂.vals.length ≤ u := fun u hu =>
      Or.inl (Or.inr (by rw [hu]; exact List.mem_cons_self))
    have R23 := run_cc (Cc := PhTok salt (.loc tk)) (Ch := PhTok salt (.loc tk)) hm₃.run0
      htk htk
    have hcc : ∀ u, u = c → PhTok salt (.loc tk) u ∨ d₂.vals.length ≤ u := fun u hu =>
      Or.inr (hu ▸ hc2)
    have R24 := run_seq R23 hm₄.run0 hcc hcc
    have hdd : ∀ u, u = dk → PhTok salt (.loc tk) u ∨ d₂.vals.length ≤ u := fun u hu =>
      Or.inr (hu ▸ h23.trans hdk)
    have R25 := run_seq R24 hr₅ hdd hdd
    have hrr : ∀ u, u = rq.1 → PhTok salt (.loc tk) u ∨ d₂.vals.length ≤ u := fun u hu =>
      Or.inr (hu ▸ h23.trans hrq)
    have R26 := run_seq R25 hr₆ hrr
      (fun u hu => hu.elim (hrr u) fun h => absurd h List.not_mem_nil)
    have R27 := run_seq R26 hr7 hC hC
    have R17 := run_seq (run_cc (Cc := PhTok salt (.loc tk)) (Ch := PhTok salt (.loc tk)) hr₂
      (fun _ h => h.elim) (fun u hu => Or.inl (Or.inl (List.mem_singleton.mp hu))))
      R27 (fun _ h => Or.inl h) (fun _ h => Or.inl h)
    have R07 := run_seq (run_cc (Cc := PhTok salt (.loc tk)) (Ch := PhTok salt (.loc tk)) hr₁
      (fun _ h => h.elim) (fun u hu => Or.inl (Or.inl (List.mem_singleton.mp hu))))
      R17 (fun _ h => Or.inl h) (fun _ h => Or.inl h)
    have A27 : Adds (OldOr (PhTok salt (.loc tk)) d₂.vals.length) d₂ d7 :=
      ((((hm₃.adds.mono fun e _ h => (htk _ h.2).symm).trans
        (hm₄.adds.mono fun e _ h => (hcc _ h.2).symm)).trans
        (ha₅.mono fun e _ h => Or.inl (h.2.elim (fun h => h ▸ h23.trans hdk)
          fun h => h23.trans (hrq2 _ h)))).trans
        (ha₆.mono fun e _ h => (hrr _ h.2).symm)).trans
        (ha7.mono fun e _ h => h.elim
          (fun h => Or.inl ((h23.trans (h34.trans (h45.trans h56))).trans h))
          fun h => (hC _ h).symm)
    exact ⟨R07.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
      (fun o => eRun_join a A w W o)
      (fun o => mChain_join t a A w W cap _ i tk ph' hk hj' o), R27.charges, A27,
      ((ha₁.mono fun e _ h => Or.inl h.2).trans
        (ha₂.mono fun e _ h => Or.inl (h01.trans h.2))).trans
        (A27.mono fun e _ h => h.imp_left fun h => h02.trans h)⟩
  cases o with
  | none =>
      obtain ⟨R, _, _, A07⟩ := key noTok (.aft 0 0) d₆ (fun _ h => h.elim) rfl (Run.refl d₆)
        (Adds.refl _ d₆)
      exact ⟨hd₆, R, A07, fun _ h => nomatch h⟩
  | some q =>
      have hq := hq q rfl
      have hV₆ := ClV.hit hV₅ hr₆.charges hq
      have hcq : c < q.tl := lt_of_lt_of_le hc3 ((h34.trans h45).trans hq.new)
      have hN : ∀ u ∈ c :: dk :: (rq.2 ++ q.tl :: q.dead), d₂.vals.length ≤ u := fun u h => by
        simp only [List.mem_append, List.mem_cons] at h
        rcases h with rfl | rfl | h | rfl | h
        · exact hc2
        · exact h23.trans hdk
        · exact h23.trans (hrq2 u h)
        · exact hc2.trans (Nat.le_of_lt hcq)
        · exact (h23.trans (h34.trans h45)).trans (hq.dead u h).1
      have hci₆ : CI d₆ t salt sFS (V ++ (c :: dk :: (rq.2 ++ q.tl :: q.dead)))
          (.shr q.tl c) :=
        { salt_mem := List.mem_append_left _ hci.salt_mem
          ph_mem := fun u hu => mem_join_ph hu
          deps := hV₆.perm mem_join_perm
          ph_ok := ⟨(lt_of_lt_of_le hs (h02.trans (hc2.trans (Nat.le_of_lt hcq)))).ne',
            (lt_of_lt_of_le hs (h02.trans hc2)).ne', hcq.ne, hq.unt, hq.len,
            fun m => (((hm₄.free _ _ (by cases m <;> exact fun h => nomatch h)
                (hm₃.unt.freeAt (oName t m))).grows hr₅.grows
                (fun h => absurd (h ▸ hdk) (Nat.not_le.mpr hc3)) (fun h => h)).grows hr₆.grows
                (fun h => h.elim (fun h => absurd (h ▸ hrq) (Nat.not_le.mpr hc3))
                  fun h => absurd h List.not_mem_nil) (fun h => h)),
            ((hm₃.len.grows hm₄.run.grows).grows hr₅.grows).grows hr₆.grows⟩ }
      have h26 : d₂.vals.length ≤ d₆.vals.length := h23.trans (h34.trans (h45.trans h56))
      have hv06 : d.vals <+: d₆.vals :=
        ((((hr₁.grows.vals.trans hr₂.grows.vals).trans hm₃.run.grows.vals).trans
          hm₄.run.grows.vals).trans hr₅.grows.vals).trans hr₆.grows.vals
      refine SafeO.bind _ _ d₆ (SafeO.mono ?_ _ d₆ (ih eS eP (i + 1) (.shr q.tl c) _
        (V ++ (c :: dk :: (rq.2 ++ q.tl :: q.dead))) n d₆
        (hn.trans (h02.trans h26)) hd₆ hci₆ (by rw [val_of_prefix hv06 hs]; exact hsv)))
      rintro r' d7 ⟨hd7, hr7, ha7, hz⟩
      obtain ⟨R, C27, A27, A07⟩ := key (PhTok salt (.shr q.tl c)) (.shr q.tl c) d7
        (fun u hu => by
          rcases hu with rfl | hu
          · exact Or.inl (Or.inl rfl)
          · simp only [phToks, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact Or.inr (hc2.trans (Nat.le_of_lt hcq))
            · exact Or.inr hc2) rfl hr7 ha7
      refine ⟨hd7, R, A07, fun z' hz' => ?_⟩
      cases r' with
      | noFormat => exact nomatch hz'
      | ranOut _ => exact nomatch hz'
      | ok z =>
          obtain ⟨hE, hloc, hcls, hK⟩ := hz z rfl
          have e := Res.ok.inj hz'
          subst e
          have hold : ∀ u, PhTok salt (.loc tk) u → u < d.vals.length := fun u hc =>
            (hci.deps u (PhTok.mem hci hc)).1
          have hloc' : ∀ u ∈ (c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks,
              d₂.vals.length ≤ u := fun u hu =>
            (List.mem_append.mp hu).elim (hN u) fun h => h26.trans (hloc u h)
          have hno : ∀ (T : TreeT lam L), TreeOKT d₂ [salt] T → TreeNewT d.vals.length T →
              ∀ e : Ev (typedOracleFamily lam K L), OldOr (PhTok salt (.loc tk)) d₂.vals.length e →
                ¬ TreeTokT T e.charged := fun T h1 h2 e he hc => he.elim
            (fun h => absurd (TreeOKT.lt h1 hc) (Nat.not_lt.mpr h))
            (fun h => absurd (h2 _ hc) (Nat.not_le.mpr (hold _ h)))
          have hTJ₂ : ∀ T ∈ TJ, TreeOKT d₂ [salt] T ∧ LeafAt d₂ T (pre i true sv) :=
            fun T hT => ⟨TreeOKT.keeps (hT₁ T hT).1 hr₂.charges fun _ _ h => h,
              LeafAt.adds (hT₁ T hT).2.2 (fun u hu => TreeOKT.lt (hT₁ T hT).1 hu)
                hr₂.grows.vals ha₂ fun e he hc =>
                  absurd (TreeOKT.lt (hT₁ T hT).1 hc) (Nat.not_lt.mpr he.2)⟩
          refine ⟨⟨?_, ?_, fun T hT => ?_, hE.kept⟩, fun u hu => h02.trans (hloc' u hu), ?_,
            ?_, ?_, hK⟩
          · show ∀ u ∈ V ++ ((c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks),
              u < d7.vals.length ∧
              Deps d7 u (V ++ ((c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks))
            rw [← List.append_assoc]
            exact hE.deps
          · exact fun u hu => hn.trans (h02.trans (hloc' u hu))
          · rcases List.mem_append.mp hT with hT | hT
            · have hT' := hT₂ T hT
              exact ⟨TreeOKT.keeps hT'.1 C27 fun u hu hc =>
                  absurd (h01.trans (hT'.2.1 u hu)) (Nat.not_le.mpr (hold u hc)),
                fun u hu => hn.trans (h01.trans (hT'.2.1 u hu))⟩
            · have hT' := hT₁ T hT
              exact ⟨TreeOKT.keeps (hTJ₂ T hT).1 C27 fun u hu hc =>
                  absurd (hT'.2.1 u hu) (Nat.not_le.mpr (hold u hc)),
                fun u hu => hn.trans (hT'.2.1 u hu)⟩
          · show Adds (Cls d.vals.length
              (V ++ ((c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks))) d d7
            have hin : ∀ u ∈ c :: dk :: (rq.2 ++ q.tl :: q.dead),
                u ∈ V ++ ((c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks) := fun u hu =>
              List.mem_append_right _ (List.mem_append_left _ hu)
            have hleafNo : ∀ u, d.vals.length ≤ u → u < d₂.vals.length →
                u ∉ V ++ ((c :: dk :: (rq.2 ++ q.tl :: q.dead)) ++ z.toks) :=
              fun u h1 h2 hm => by
                rcases List.mem_append.mp hm with hm | hm
                · exact absurd h1 (Nat.not_le.mpr (hci.deps _ hm).1)
                · exact absurd (hloc' _ hm) (Nat.not_le.mpr h2)
            exact ((((((ha₁.mono fun e he h => Or.inl ⟨h.1, h.2, hleafNo _ h.2
                (lt_of_lt_of_le (hd₁.charged_lt e he) h12)⟩).trans
              (ha₂.mono fun e he h => Or.inl ⟨h.1, h01.trans h.2,
                hleafNo _ (h01.trans h.2) (hd₂.charged_lt e he)⟩)).trans
              (hm₃.adds.mono fun e _ h => Or.inr ⟨(fun hc => nomatch h.1.symm.trans hc),
                h.2 ▸ List.mem_append_left _ htkV⟩)).trans
              (hm₄.adds.mono fun e _ h => Or.inr ⟨(fun hc => nomatch h.1.symm.trans hc),
                h.2 ▸ hin c List.mem_cons_self⟩)).trans
              (ha₅.mono fun e _ h => Or.inr ⟨h.1, hin _ (mem_join_path h.2)⟩)).trans
              (ha₆.mono fun e _ h => Or.inr ⟨h.1, hin _ (h.2 ▸ mem_join_path hmem)⟩)).trans
              (hcls.mono fun e _ h => by
                rw [← List.append_assoc]
                exact h.imp_left fun h => ⟨h.1, (h02.trans h26).trans h.2.1, h.2.2⟩)
          · exact fun T hT => LeafAt.adds (hT₂ T hT).2.2
              (fun u hu => TreeOKT.lt (hT₂ T hT).1 hu) C27.vals A27
              (hno T (hT₂ T hT).1 fun u hu => h01.trans ((hT₂ T hT).2.1 u hu))
          · exact fun T hT => LeafAt.adds (hTJ₂ T hT).2
              (fun u hu => TreeOKT.lt (hTJ₂ T hT).1 hu) C27.vals A27
              (hno T (hTJ₂ T hT).1 (hT₁ T hT).2.1)

end Arms

/-- **The chain.** -/
theorem safe_chainT (t : Tag) (cms : List (Dig lam)) (x : Option X) (ℓ : ℕ)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) (sFS : ℕ)
    (sv : Bits) (hbl : bl ≤ ℓ) (hbS : bf ≤ sFS) (hbL : bf ≤ lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      ChainGoal bl bf sd t cms x ℓ pre salt cd cap sFS sv s A W
  | [], _, _ => by
      intro _ _ _ ph _ V n d _ hd hci _
      refine ⟨hd, Run.refl d, Adds.refl _ d, fun z hz => ?_⟩
      have e := Res.ok.inj hz
      subst e
      refine ⟨⟨?_, fun _ h => absurd h List.not_mem_nil, trivial⟩,
        fun _ h => absurd h List.not_mem_nil, Adds.refl _ d, trivial⟩
      show ∀ u ∈ V ++ [], u < d.vals.length ∧ Deps d u (V ++ [])
      rw [List.append_nil]
      exact hci.deps
  | _ :: s, (a, A), (w, W) => by
      intro embS embP i ph σ V n d hn hd hci hsv
      obtain ⟨m, k⟩ := σ
      have ih := safe_chainT t cms x ℓ pre salt cd cap sFS sv hbl hbS hbL s A W
      rw [chainT]
      split
      · rename_i tk us hd' inj next heq
        exact safe_roundOne t cms x ℓ pre salt cd cap sFS sv a A w W _ _ k _ m.1 i V n d hbl hbS hbL
          ih hn hd hsv ph hci true w.grJ w.depthJ w.posAtJ heq _ _ _ _
          (fun q TJ => ((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [], TJ))
          (fun _ _ _ h => absurd h List.not_mem_nil) (fun _ _ _ h => ⟨rfl, h⟩)
          (Nat.le_add_right _ _) fun h => by
            rcases h with ⟨_, hk⟩ | ⟨h, _⟩
            · exact (hasTest_lo hk).symm
            · exact absurd h (by simp)
      · rename_i tk us hd' inj next heq
        exact safe_roundOne t cms x ℓ pre salt cd cap sFS sv a A w W _ _ k _ m.1 i V n d hbl hbS hbL
          ih hn hd hsv ph hci false w.gr0 w.depth0 w.posAt0 heq _ _ _ _
          (fun q T0 => ((m.1, a.plain.symm (q.pl, (a.plain m.2).2)), T0, []))
          (fun _ _ _ h => ⟨rfl, h⟩) (fun _ _ _ h => absurd h List.not_mem_nil)
          (Nat.le_add_left _ _) fun h => by
            rcases h with ⟨h, _⟩ | ⟨_, hk⟩
            · exact absurd h (by simp)
            · exact (hasTest_sh hk).symm
      · rename_i tk heq
        obtain ⟨hk, rfl⟩ := act_join heq
        exact safe_roundJoin t cms x ℓ pre salt cd cap sFS sv a A w W _ _ k _ m.1 i V n d hbl hbS
          hbL ih hn hd hsv tk hci hk _ _ _ fun q => (m.1, a.plain.symm (q.pl, (a.plain m.2).2))
      · exact ⟨hd, Run.refl d, Adds.refl _ d, fun _ h => nomatch h⟩

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safe_chainT
