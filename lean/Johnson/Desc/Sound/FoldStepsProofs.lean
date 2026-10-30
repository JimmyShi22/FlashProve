-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldStepsProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/FoldSteps.lean, each under its name with a small first letter. THE FORM OVER
Block.lean. By unfolding Block.lean's texts
(`foldBlocks`, `claimsIn`, `afterIn`, `Link.runBehind`, `Link.blocksInOrder`) and induction on a list;
`claimsInBy` through `claimsIn_of_claimsInBy` (Johnson/Desc/BlockLaws.lean).

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

theorem stepsOfLeaves : StepsOfLeaves := fun _ _ _ _ _ h => h

theorem foldSteps : FoldSteps := by
  intro S Cl R hR ft bs
  induction bs with
  | nil =>
    intro s rs cols out _ H
    have e : (s, rs, cols) = out := Except.ok.inj H
    rw [← e]
    exact hR.refl s
  | cons b l ih =>
    intro s rs cols out hb H
    obtain ⟨s', k, hst, H'⟩ := foldConsOk H
    obtain ⟨gs, hd⟩ := stepOk hst
    exact hR.trans _ _ _ (hb b List.mem_cons_self _ _ _ _ hd)
      (ih s' _ _ out (fun c hc => hb c (List.mem_cons_of_mem _ hc)) H')

/-- As `foldConsOk`, with the test on the stretch's length. -/
theorem foldConsOk' {S Cl : Type} {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (H : foldBlocks ft (b :: l) s rs cols = .ok out) :
    ∃ s' k, (rs.take b.rounds.length).length = b.rounds.length ∧
      b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) ∧
      foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok out := by
  simp only [foldBlocks, List.splitAt_eq] at H
  split at H
  next => exact nomatch H
  next hl =>
    split at H
    next => exact nomatch H
    next s' k hst => exact ⟨s', k, Decidable.not_not.1 hl, hst, H⟩

/-- The converse. -/
theorem foldConsMk {S Cl : Type} {ft : Nat} {b : Block S Cl} {l : List (Block S Cl)} {s s' : S}
    {k : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hl : (rs.take b.rounds.length).length = b.rounds.length)
    (hst : b.step ft s (rs.take b.rounds.length) cols = .ok (s', k))
    (H : foldBlocks ft l s' (rs.drop b.rounds.length) (cols.drop k) = .ok out) :
    foldBlocks ft (b :: l) s rs cols = .ok out := by
  simp only [foldBlocks, List.splitAt_eq]
  rw [if_neg (fun h => h hl)]
  simp only [hst]
  exact H

theorem behindCons {S Cl : Type} (b : Block S Cl) (l : List (Block S Cl)) (rs : List Fmt.RoundView) :
    behindOf l (rs.drop b.rounds.length) = behindOf (b :: l) rs := by
  simp [behindOf, List.drop_drop]

theorem behindApp {S Cl : Type} (l₁ l₂ : List (Block S Cl)) (rs : List Fmt.RoundView) :
    behindOf l₂ (behindOf l₁ rs) = behindOf (l₁ ++ l₂) rs := by
  unfold behindOf
  rw [List.drop_drop, List.flatMap_append, List.length_append]

theorem foldAt : FoldAt := by
  intro S Cl R hR ft pre rest
  induction pre with
  | nil =>
    intro s rs cols out _ H
    have e : behindOf ([] : List (Block S Cl)) rs = rs := by simp [behindOf]
    exact ⟨s, cols, hR.refl s, by rw [e]; rfl, by rw [e]; exact H⟩
  | cons b l ih =>
    intro s rs cols out hb H
    obtain ⟨s', k, hl, hst, H'⟩ := foldConsOk' (l := l ++ rest) H
    obtain ⟨gs, hd⟩ := stepOk hst
    obtain ⟨m, cols', hm, Hp, Hm⟩ :=
      ih s' _ _ out (fun c hc => hb c (List.mem_cons_of_mem _ hc)) H'
    rw [behindCons] at Hp Hm
    exact ⟨m, cols', hR.trans _ _ _ (hb b List.mem_cons_self _ _ _ _ hd) hm,
      foldConsMk hl hst Hp, Hm⟩

theorem foldJoin : FoldJoin := by
  intro S Cl ft pre rest
  induction pre with
  | nil =>
    intro s m rs rs' cols cols' out Hp Hr
    have e : (s, rs, cols) = (m, rs', cols') := Except.ok.inj Hp
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸
      (by simpa using e : s = m ∧ rs = rs' ∧ cols = cols')
    exact Hr
  | cons b l ih =>
    intro s m rs rs' cols cols' out Hp Hr
    obtain ⟨s', k, hl, hst, H'⟩ := foldConsOk' Hp
    exact foldConsMk (l := l ++ rest) hl hst (ih s' m _ rs' _ cols' out H' Hr)

section
variable {S Cl : Type}

/-- One step of `claimsIn`. -/
def claimStep (bs : List (Block S Cl)) (acc : Except String (List Cl × S)) (o : Nat × String) :
    Except String (List Cl × S) :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)).bind fun run =>
      match run x.1.length x.2 with
      | .ok y => .ok (x.1 ++ y.1, y.2)
      | .error e => .error (o.2 ++ ": " ++ e)

theorem claimFoldError (bs : List (Block S Cl)) (m : String) :
    ∀ order : List (Nat × String), order.foldl (claimStep bs) (.error m) = .error m
  | [] => rfl
  | _ :: os => claimFoldError bs m os

theorem namedOk {α : Type} {name : String} {o : Option α} {a : α} (h : named name o = .ok a) :
    o = some a := by
  cases o with
  | none => exact nomatch h
  | some x => exact congrArg some (Except.ok.inj h)

theorem claimStepOk {bs : List (Block S Cl)} {x x' : List Cl × S} {o : Nat × String}
    (h : claimStep bs (.ok x) o = .ok x') :
    ∃ b run ycl ys, bs[o.1]? = some b ∧ b.claims.lookup o.2 = some run ∧
      run x.1.length x.2 = .ok (ycl, ys) ∧ x' = (x.1 ++ ycl, ys) := by
  obtain ⟨run, hn, h⟩ := bindOk
    (x := named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)) h
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.1 (namedOk hn)
  have h' : (match run x.1.length x.2 with
    | .ok y => (.ok (x.1 ++ y.1, y.2) : Except String (List Cl × S))
    | .error e => .error (o.2 ++ ": " ++ e)) = .ok x' := h
  split at h'
  · rename_i y hy
    exact ⟨b, run, y.1, y.2, hb, hl, hy, (Except.ok.inj h').symm⟩
  · exact nomatch h'

theorem claimsFold {R : S → S → Prop} (hR : Pre R) {bs : List (Block S Cl)}
    (hb : ∀ b ∈ bs, b.RunsStep R) :
    ∀ (order : List (Nat × String)) (x : List Cl × S) (cls : List Cl) (e : S),
      order.foldl (claimStep bs) (.ok x) = .ok (cls, e) →
      R x.2 e ∧ (∀ c ∈ x.1, c ∈ cls) ∧ ∀ o ∈ order, RunCalled R bs o x.2 e cls
  | [], x, cls, e, h => by
    have e' : x = (cls, e) := Except.ok.inj h
    subst e'
    exact ⟨hR.refl _, fun _ h => h, fun _ h => nomatch h⟩
  | o :: os, x, cls, e, h => by
    have h' : os.foldl (claimStep bs) (claimStep bs (.ok x) o) = .ok (cls, e) := h
    cases hs : claimStep bs (.ok x) o with
    | error m =>
      rw [hs, claimFoldError] at h'
      exact nomatch h'
    | ok x' =>
      rw [hs] at h'
      obtain ⟨b, run, ycl, ys, hbb, hl, hy, ex⟩ := claimStepOk hs
      obtain ⟨r₁, r₂, r₃⟩ := claimsFold hR hb os x' cls e h'
      subst ex
      have hstep : R x.2 ys :=
        hb b (List.mem_of_getElem? hbb) (o.2, run) (memOfLookup _ _ _ hl) _ _ _ _ hy
      refine ⟨hR.trans _ _ _ hstep r₁, fun c hc => r₂ c (List.mem_append_left _ hc),
        fun o' ho' => ?_⟩
      rcases List.mem_cons.1 ho' with rfl | ho'
      · exact ⟨b, run, _, x.2, ycl, ys, hbb, hl, hy, hR.refl _, r₁,
          fun c hc => r₂ c (List.mem_append_right _ hc)⟩
      · obtain ⟨b', run', n, v, cl, v', q₁, q₂, q₃, q₄, q₅, q₆⟩ := r₃ o' ho'
        exact ⟨b', run', n, v, cl, v', q₁, q₂, q₃, hR.trans _ _ _ hstep q₄, q₅, q₆⟩

/-- One step of `afterIn`. -/
def afterStep (bs : List (Block S Cl)) (acc : Except String S) (o : Nat × String) :
    Except String S :=
  acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)

theorem afterFoldError (bs : List (Block S Cl)) (m : String) :
    ∀ order : List (Nat × String), order.foldl (afterStep bs) (.error m) = .error m
  | [] => rfl
  | _ :: os => afterFoldError bs m os

theorem afterFold {R : S → S → Prop} (hR : Pre R) {bs : List (Block S Cl)}
    (hb : ∀ b ∈ bs, b.AfterStep R) :
    ∀ (order : List (Nat × String)) (x e : S),
      order.foldl (afterStep bs) (.ok x) = .ok e → R x e
  | [], x, e, h => by
    have e' : x = e := Except.ok.inj h
    subst e'
    exact hR.refl _
  | o :: os, x, e, h => by
    have h' : os.foldl (afterStep bs) (afterStep bs (.ok x) o) = .ok e := h
    cases hs : afterStep bs (.ok x) o with
    | error m =>
      rw [hs, afterFoldError] at h'
      exact nomatch h'
    | ok x' =>
      rw [hs] at h'
      obtain ⟨run, hn, hk⟩ := bindOk
        (x := named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)) hs
      obtain ⟨b, hbb, hl⟩ := Option.bind_eq_some_iff.1 (namedOk hn)
      have hk' : (match run x with
        | .ok y => (.ok y : Except String S)
        | .error e => .error (o.2 ++ ": " ++ e)) = .ok x' := hk
      split at hk'
      · rename_i y hy
        have ey : y = x' := Except.ok.inj hk'
        subst ey
        exact hR.trans _ _ _
          (hb b (List.mem_of_getElem? hbb) (o.2, run) (memOfLookup _ _ _ hl) _ _ hy)
          (afterFold hR hb os y e h')
      · exact nomatch hk'

end

theorem claimsTrace : ClaimsTrace := by
  intro S Cl R hR bs order s e cls hb h
  obtain ⟨r₁, -, r₃⟩ := claimsFold hR hb order ([], s) cls e h
  exact ⟨r₁, r₃⟩

theorem afterSteps : AfterSteps := fun _ _ _ hR _ order s e hb h => afterFold hR hb order s e h

theorem flatIs : FlatIs := fun _ _ _ => rfl

theorem callsAtOfCalls : CallsAtOfCalls := fun _ _ _ _ _ h f => h f

/-- A block without a round in front does not move a later block's stretch. -/
theorem shownAtQuiet {S Cl : Type} (a : Block S Cl) (h₁ : List (Block S Cl)) (b : Block S Cl)
    (rs : List Fmt.RoundView) (ha : a.rounds = []) : shownAt (a :: h₁) b rs = shownAt h₁ b rs := by
  unfold shownAt
  rw [List.flatMap_cons, ha, List.nil_append]

/-- Where a fold over b :: l goes on from the rounds behind pre: b's decision went on at its
stretch. -/
theorem decidedAt {S Cl : Type} {ft : Nat} (pre : List (Block S Cl)) {b : Block S Cl}
    {l : List (Block S Cl)} {t : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {out : S × List Fmt.RoundView × List OpenedColumn}
    (H : foldBlocks ft (b :: l) t (behindOf pre rs) cols = .ok out) :
    ∃ t₁ k gs, b.decide t (shownAt pre b rs) gs = .ok t₁ ∧
      foldBlocks ft [b] t (behindOf pre rs) cols =
        .ok (t₁, behindOf (pre ++ [b]) rs, cols.drop k) ∧
      foldBlocks ft l t₁ (behindOf (pre ++ [b]) rs) (cols.drop k) = .ok out := by
  obtain ⟨t₁, k, hl, hst, H'⟩ := foldConsOk' H
  obtain ⟨gs, hd⟩ := stepOk hst
  have e : (behindOf pre rs).drop b.rounds.length = behindOf (pre ++ [b]) rs := by
    rw [← behindApp]
    simp [behindOf]
  rw [e] at H'
  exact ⟨t₁, k, gs, hd, foldConsMk hl hst (by rw [e]; rfl), H'⟩

/-- The trivial relation. -/
theorem preTrue {S : Type} : Pre (fun _ _ : S => True) :=
  ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩

/-- The core of both traces: from the fold over laid :: (h₁ ++ b :: h₂) ++ batched :: rest. -/
theorem traceCore {S Cl : Type} {R : S → S → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop} (hR : Pre R) (L : Link S Cl)
    (h₁ h₂ rest : List (Block S Cl)) (b : Block S Cl) (hc : L.hear = h₁ ++ b :: h₂)
    (hs : ∀ c ∈ h₂, c.Steps R) (hr : ∀ c ∈ L.hear, c.RunsStep R)
    (hcall : CallsAt R Q L.batched (claimsInBy L.each L.hear L.order))
    (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft ((L.laid :: h₁) ++ b :: (h₂ ++ L.batched :: rest)) s rs cols = .ok out) :
    ∃ t t₁ u₀ z u e cls c', Traced R Q L h₁ b ft s rs cols t t₁ u₀ z u e cls ∧
      foldBlocks ft (L.laid :: L.hear ++ [L.batched]) s rs cols =
        .ok (z, behindOf (L.laid :: L.hear ++ [L.batched]) rs, c') ∧
      foldBlocks ft rest z (behindOf (L.laid :: L.hear ++ [L.batched]) rs) c' = .ok out := by
  obtain ⟨t, c₀, -, P₁, H₁⟩ := foldAt S Cl (fun _ _ => True) preTrue ft (L.laid :: h₁) _ s rs cols
    out (fun _ _ _ _ _ _ _ => trivial) H
  obtain ⟨t₁, k, gs₁, hd₀, Pb, H₂⟩ := decidedAt (L.laid :: h₁) H₁
  have hd : b.decide t (shownAt h₁ b rs) gs₁ = .ok t₁ := shownAtQuiet L.laid h₁ b rs rfl ▸ hd₀
  obtain ⟨u₀, c₂, hu, P₂, H₃⟩ := foldAt S Cl R hR ft h₂ _ t₁ _ _ out hs H₂
  have eh : (L.laid :: h₁ ++ [b]) ++ h₂ = L.laid :: L.hear := by
    rw [hc]
    simp
  have eb : behindOf h₂ (behindOf (L.laid :: h₁ ++ [b]) rs) = behindOf (L.laid :: L.hear) rs := by
    rw [behindApp, eh]
  rw [eb] at P₂ H₃
  have Ph : foldBlocks ft (L.laid :: L.hear) s rs cols =
      .ok (u₀, behindOf (L.laid :: L.hear) rs, c₂) := by
    have k := foldJoin S Cl ft (L.laid :: h₁ ++ [b]) h₂ s t₁ rs _ cols _ _
      (foldJoin S Cl ft (L.laid :: h₁) [b] s t rs _ cols _ _ P₁ Pb) P₂
    rw [eh] at k
    exact k
  obtain ⟨z, k', gsB, hdB₀, PB, H₄⟩ := decidedAt (L.laid :: L.hear) H₃
  have hdB : L.batched.decide u₀ (shownAt L.hear L.batched rs) gsB = .ok z :=
    shownAtQuiet L.laid L.hear L.batched rs rfl ▸ hdB₀
  obtain ⟨u, cls, e, hu', hf, hz, hq⟩ := hcall _ _ _ _ hdB
  obtain ⟨hue, htr⟩ := claimsTrace S Cl R hR L.hear L.order u e cls hr
    (claimsIn_of_claimsInBy L.each L.hear L.order u (cls, e) hf)
  have Pz := foldJoin S Cl ft _ _ s u₀ rs _ cols _ _ Ph PB
  refine ⟨t, t₁, u₀, z, u, e, cls, _, ⟨⟨c₀, P₁⟩, ⟨gs₁, hd⟩,
    ⟨_, foldJoin S Cl ft (L.laid :: h₁) [b] s t rs _ cols _ _ P₁ Pb⟩, ⟨c₂, Ph⟩, hu, ⟨gsB, hdB⟩,
    ⟨_, Pz⟩, hu', hf, hue, hz, hq, fun name hn => ?_⟩, Pz, H₄⟩
  obtain ⟨b', run, n, v, cl, v', q₁, q₂, q₃, q₄, q₅, q₆⟩ := htr _ hn
  have q₁' : (h₁ ++ b :: h₂)[h₁.length]? = some b' := hc ▸ q₁
  have ebb : b = b' := by simpa using q₁'
  subst ebb
  exact ⟨run, n, v, cl, v', q₂, q₃, hR.trans _ _ _ (hR.trans _ _ _ hu hu') q₄, q₅, q₆⟩

theorem linkTraceAt : LinkTraceAt := by
  intro S Cl R Q hR L h₁ h₂ b hc hs hr hcall ft s rs cols out H
  have hflat : L.blocksInOrder = (L.laid :: h₁) ++ b ::
      (h₂ ++ L.batched :: (L.behind :: (L.close ++ [L.cleared]))) := by
    rw [flatIs, hc]
    simp
  rw [hflat] at H
  obtain ⟨t, t₁, u₀, z, u, e, cls, _, hT, -, -⟩ :=
    traceCore hR L h₁ h₂ _ b hc hs hr hcall ft s rs cols out H
  exact ⟨t, t₁, u₀, z, u, e, cls, hT⟩

theorem linkTraceCloseAt : LinkTraceCloseAt := by
  intro S Cl R Q hR L h₁ h₂ c₁ c₂ b d hc hcl hs hr hcall ha hs₁ ft s rs cols out H
  have hflat : L.blocksInOrder = (L.laid :: h₁) ++ b ::
      (h₂ ++ L.batched :: (L.behind :: (c₁ ++ d :: (c₂ ++ [L.cleared])))) := by
    rw [flatIs, hc, hcl]
    simp
  rw [hflat] at H
  obtain ⟨t, t₁, u₀, z, u, e, cls, c', hT, Pz, H₄⟩ :=
    traceCore hR L h₁ h₂ _ b hc hs hr hcall ft s rs cols out H
  have hsB : ∀ c ∈ L.behind :: c₁, c.Steps R := by
    intro c hcm
    rcases List.mem_cons.1 hcm with rfl | hcm
    · intro x _ _ x' hx
      have hx' : L.runBehind x = .ok x' := hx
      unfold Link.runBehind at hx'
      split at hx'
      · exact afterSteps S Cl R hR L.hear L.orderAfter x x' ha hx'
      · exact nomatch hx'
    · exact hs₁ c hcm
  obtain ⟨w, c₃, hw, Pw, H₆⟩ := foldAt S Cl R hR ft (L.behind :: c₁) (d :: (c₂ ++ [L.cleared])) z _
    _ out hsB H₄
  have eu : (L.laid :: L.hear ++ [L.batched]) ++ (L.behind :: c₁) = L.upTo c₁ := by
    simp [Link.upTo]
  have eb : behindOf (L.behind :: c₁) (behindOf (L.laid :: L.hear ++ [L.batched]) rs) =
      behindOf (L.upTo c₁) rs := by
    rw [behindApp, eu]
  rw [eb] at Pw H₆
  obtain ⟨w₁, _, gs₄, hd₄, Pd, -⟩ := decidedAt (L.upTo c₁) H₆
  have k := foldJoin S Cl ft (L.laid :: L.hear ++ [L.batched]) (L.behind :: c₁) s z rs _ cols _ _ Pz
    Pw
  rw [eu] at k
  exact ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, hw, ⟨c₃, k⟩, ⟨gs₄, hd₄⟩,
    ⟨_, foldJoin S Cl ft (L.upTo c₁) [d] s w rs _ cols _ _ k Pd⟩⟩

theorem carriesPre : CarriesPre := by
  intro S Φ Γ fork heard later sized lr lt
  refine ⟨fun s => ⟨fun _ h => h, fun F hF hs => ⟨F, hF, lr F, hs⟩⟩, fun a b c h₁ h₂ => ?_⟩
  refine ⟨fun g hg => h₂.1 g (h₁.1 g hg), fun F hF hs => ?_⟩
  obtain ⟨F', hF', l₁, s₁⟩ := h₁.2 F hF hs
  obtain ⟨F'', hF'', l₂, s₂⟩ := h₂.2 F' hF' s₁
  exact ⟨F'', hF'', lt _ _ _ l₁ l₂, s₂⟩

/-- From a trace at `Carries`, and `Carries` from e to a record x: what is concluded at x. -/
theorem ranUpTo {S Cl Φ Γ : Type} {fork : S → Option Φ} {heard : S → Option Γ}
    {later : Φ → Φ → Prop} {sized : Φ → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (hP : Pre (Carries fork heard later sized)) {L : Link S Cl} {h₁ h₂ : List (Block S Cl)}
    {b : Block S Cl} (hc : L.hear = h₁ ++ b :: h₂)
    (hr : ∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) {ft : Nat} {s : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {t t₁ u₀ z u e : S} {cls : List Cl}
    (hT : Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls) (x : S)
    (hx : Carries fork heard later sized e x) :
    RanUpTo fork heard later sized L h₁ b t₁ x cls := by
  intro g F' hg hF hsz
  have htx := hP.trans _ _ _ hT.toBatch (hP.trans _ _ _ hT.toCall (hP.trans _ _ _ hT.along hx))
  obtain ⟨Hh, hH, lH, sH⟩ := htx.2 F' hF hsz
  refine ⟨htx.1 g hg, Hh, hH, lH, sH, fun name hn => ?_⟩
  obtain ⟨run, n, v, cl, v', q₂, q₃, q₄, q₅, q₆⟩ := hT.runs name hn
  obtain ⟨Fv, hFv, lv, sv⟩ := q₄.2 F' hF hsz
  have hbm : b ∈ L.hear := by
    rw [hc]
    simp
  have hvv : Carries fork heard later sized v v' :=
    hr b hbm (name, run) (memOfLookup _ _ _ q₂) n v cl v' q₃
  obtain ⟨G, hG, -, sG⟩ := hvv.2 Fv hFv sv
  obtain ⟨H', hH', lH', -⟩ := (hP.trans _ _ _ q₅ hx).2 G hG sG
  have eH : H' = Hh := Option.some.inj (hH'.symm.trans hH)
  exact ⟨run, v, cl, G, q₂, ⟨q₄.1 g hg, ⟨Fv, hFv, lv, sv⟩, ⟨n, v', q₃, hG⟩⟩, eH ▸ lH', q₆⟩

theorem ranAtOfLinkAt : RanAtOfLinkAt := by
  intro S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ b hc hs hr hcall ft s rs cols out H
  have hP := carriesPre S Φ Γ fork heard later sized lr lt
  obtain ⟨t, t₁, u₀, z, u, e, cls, hT⟩ :=
    linkTraceAt S Cl _ Q hP L h₁ h₂ b hc hs hr hcall ft s rs cols out H
  exact ⟨t, t₁, u₀, z, u, e, cls, hT, ranUpTo hP hc hr hT e (hP.refl e)⟩

theorem ranAtToSettlingAt : RanAtToSettlingAt := by
  intro S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ c₁ c₂ b d hc hcl hs hr hcall ha hs₁ ft s rs
    cols out H
  have hP := carriesPre S Φ Γ fork heard later sized lr lt
  obtain ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, hzw, Pw, hd, Pw₁⟩ :=
    linkTraceCloseAt S Cl _ Q hP L h₁ h₂ c₁ c₂ b d hc hcl hs hr hcall ha hs₁ ft s rs cols out H
  exact ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, Pw, hd, Pw₁,
    ranUpTo hP hc hr hT w (hP.trans _ _ _ hT.fromCall hzw)⟩

/-! ## Four more statements, from these -/

theorem linkTrace : LinkTrace := fun S Cl R Q hR L h₁ h₂ b hc hs hr hcall =>
  linkTraceAt S Cl R Q hR L h₁ h₂ b hc hs hr (callsAtOfCalls _ _ _ _ _ hcall _)

theorem linkTraceClose : LinkTraceClose := by
  intro S Cl R Q hR L h₁ h₂ c₁ c₂ b d hc hcl hs hr hcall ha hs₁ ft s rs cols out H
  obtain ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, hzw, Pw, hd, -⟩ :=
    linkTraceCloseAt S Cl R Q hR L h₁ h₂ c₁ c₂ b d hc hcl hs hr (callsAtOfCalls _ _ _ _ _ hcall _)
      ha hs₁ ft s rs cols out H
  exact ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, hzw, Pw, hd⟩

theorem ranAtOfLink : RanAtOfLink :=
  fun S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ b hc hs hr hcall =>
    ranAtOfLinkAt S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ b hc hs hr
      (callsAtOfCalls _ _ _ _ _ hcall _)

theorem ranAtToSettling : RanAtToSettling := by
  intro S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ c₁ c₂ b d hc hcl hs hr hcall ha hs₁ ft s rs
    cols out H
  obtain ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, Pw, hd, -, hU⟩ :=
    ranAtToSettlingAt S Cl Φ Γ fork heard later sized Q lr lt L h₁ h₂ c₁ c₂ b d hc hcl hs hr
      (callsAtOfCalls _ _ _ _ _ hcall _) ha hs₁ ft s rs cols out H
  exact ⟨t, t₁, u₀, z, u, e, cls, w, w₁, hT, Pw, hd, hU⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.linkTraceAt
#print axioms VerifiableInference.Desc.linkTraceCloseAt
#print axioms VerifiableInference.Desc.ranAtOfLinkAt
#print axioms VerifiableInference.Desc.ranAtToSettlingAt
#print axioms VerifiableInference.Desc.foldSteps
#print axioms VerifiableInference.Desc.foldAt
#print axioms VerifiableInference.Desc.foldJoin
#print axioms VerifiableInference.Desc.claimsTrace
#print axioms VerifiableInference.Desc.afterSteps
#print axioms VerifiableInference.Desc.linkTrace
#print axioms VerifiableInference.Desc.linkTraceClose
#print axioms VerifiableInference.Desc.carriesPre
#print axioms VerifiableInference.Desc.ranAtOfLink
#print axioms VerifiableInference.Desc.ranAtToSettling
