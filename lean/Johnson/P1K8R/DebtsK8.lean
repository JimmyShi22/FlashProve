-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/DebtsK8.lean: THE SMALLNESS TEST: ITS MARK AND ITS TWO FALLS IN THE FORMS `MarkDebt`
AND `FallDebt` (Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean). Definitions and lemmas; NONE OF
THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. An assembly: no new argument.

l < 25; o := 1 at the head's segment, else 0; K := 14 l + 9, or 347: the batching's number; b: the
member at K. ft, the chain's first tree, is a letter throughout.
  **`dead_markDebt`**, **`dead_markDebt_blocks`**   `MarkDebt` of `deadMark link o sz` at its stated
      share's value, at whatever P, at Run.ck .two and Run.ckP .two
  **`front_fallDebt`**, **`front_fallDebt_blocks`**   in the goals' scope: `FallDebt` of
      `k8FrontFall l o columns tau` at b, the members behind it, its stated share's value, and every
      Q that gives `liveOf columns tau` of the state in front
  `step_ft`   general: a block whose one declared round states no item and opens nothing: a yes of
      its step at first tree ft is a yes at first tree 0, at the round without a message, at no
      columns, with the same return
  `symbolsLive_eq`   `symbolsLive` (Johnson/Desc/K8/Honest/SymbolsFew.lean) is `allLive`
      (Johnson/Desc/ProofFile/Honest/K8/FrontCount.lean), which `liveOf` holds: so where `deadMark`
      has been silent it is paid as `liveOf` is
  `shareNo nU t`   `k8Share nU` speaks at t; **`share_event`**: the wide event of `k8ShareFall l o
      nU share` at b and the members behind it, at one drawn value, gives: b's own step returns a
      state at which `k8Share nU` speaks (`behindT`, Johnson/P1K8R/CountAtStep.lean)
  **`share_fallDebt_of`**   the kit a letter: tests: a list of tests on a state, each with a number;
      IF wherever `k8Share nU` speaks one of them says yes, and Q gives, for each, that the measure
      of the round's messages at which b's step returns a state at which it says yes is at most its
      number: THEN `FallDebt` of `k8ShareFall l o nU share` at the numbers' sum
  `secondNo`   `k8Second` speaks; **`share_split`**: where `k8Share nU` speaks, one of six tests
      says yes (`linkedNo`: Johnson/Desc/K8/Honest/LinkedFew.lean)
  `FoldEnd`, `ShareNeeds`   what Q must give of the state in front, by name: it is the end of the
      verifier's fold over the members in front, from the chain's start; whatever data it holds pass
      four pairs of tests with code, with numbers over the data's
  **`share_fallDebt`**, **`share_fallDebt_blocks`**   IF THE PUBLIC TEST `rowsFitB` SAYS YES AT ALL
      25 SEGMENTS (`RowsAsked Z`): IF (second) wherever Q holds the measure of the messages at which
      b's step returns a state at which `k8Second` speaks is at most qS: `FallDebt` of `k8ShareFall`
      at the sum of six numbers, at every Q that gives `ShareNeeds`
Limits. THE LAST TWO ARE A FORM, NOT A DEBT PAID. share IS A FREE LETTER: NO STATED SHARE OF
`k8ShareFall` IS HELD. ONE OF THE SIX NUMBERS (qS for `k8Second`) IS A LETTER UNDER A PREMISE THAT
NOTHING HERE PAYS: at qS = 1 it is met for nothing. `ShareNeeds`' tests on public numbers, and those
on challenges drawn in front (`planesLive`, `digitsLive`, `readsLive`, `symbolsLive`), are paid
nowhere here. `RowsAsked Z` is a premise. `deadMark`'s test does not read the challenges in front.
No number is evaluated.
-/
import Johnson.P1K8R.FrontFallHeld
import Johnson.P1K8R.CountAtStep
import Johnson.Desc.K8.Honest.SymbolsFew
import Johnson.Desc.K8.Honest.LinkedFew
import Johnson.Desc.ProofFile.Honest.Law.CoverSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open ProofFile.Honest (Odds Mark Held Fall MarkDebt FallDebt localFall chainFall frontsOf fallOf
  markDebt_of_held fallDebt_of_heldOn pr_any_le)
open ProofFile.Honest.K8 (k8Share k8First k8Second k8FrontFall k8ShareFall frontFallShare batchPlace
  quietPlace frontsOf_step frontsOf_zero frontsOf_place)
open _root_.Run.PQ (CK)
open Iop
open scoped ENNReal

/-- **The mark's sentence: at typed challenges.** -/
theorem dead_markDebt (link o : Nat) (sz : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (sz.columns * sz.tau)]) (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ck .two) (deadMark link o sz) [d] P (deadMark link o sz).share.val :=
  markDebt_of_held _ _ _ P fun fr _ => dead_mark_held link o sz d h fr

/-- **The mark's sentence: at strings of hash blocks.** -/
theorem dead_markDebt_blocks (link o : Nat) (sz : Size) (d : RDT)
    (h : Fmt.dsOf d.entry d.kind = [.trits (sz.columns * sz.tau)]) (hlog : d.entry.logN ≤ 64)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (deadMark link o sz) [d] P (deadMark link o sz).share.val :=
  markDebt_of_held _ _ _ P fun fr _ => dead_mark_held_blocks link o sz d h hlog fr

/-- The first tree's number is not read where nothing is opened. -/
theorem step_ft {T Cl : Type} {ft : ℕ} {b : Block T Cl} {d : Fmt.DeclaredRound} (hb : b.rounds = [d])
    (hi : d.items = []) (hs : d.stored = []) (ho : d.opens = []) {s t : T} {r : Fmt.RoundView}
    {cols : List Desc.OpenedColumn} {m : ℕ} (h : b.step ft s [r] cols = .ok (t, m)) :
    b.step 0 s [⟨[], r.drawn⟩] [] = .ok (t, m) := by
  have h' := step_plain hb hi hs ho h
  obtain ⟨h1, h2, h3, h4⟩ := (Sound.step_ok_iff ft b s t [⟨[], r.drawn⟩] [] m).1 h'
  have hg : groupsOf 0 b.rounds (([⟨[], r.drawn⟩] : List Fmt.RoundView).map (·.drawn)) =
      groupsOf ft b.rounds (([⟨[], r.drawn⟩] : List Fmt.RoundView).map (·.drawn)) := by
    rw [hb]
    simp [groupsOf, hs, ho]
  refine (Sound.step_ok_iff 0 b s t [⟨[], r.drawn⟩] [] m).2 ⟨h1, ?_, ?_, ?_⟩
  · rw [hg]
    exact h2
  · rw [hg]
    exact h3
  · unfold Sound.groupsAt at h4 ⊢
    rw [hg]
    exact h4

/-- The test on the drawn matrix that `selfSymbols`' count asks is the one whose failing is the
mark's event: two texts of one function. -/
theorem symbolsLive_eq (tl : HTailF2) : symbolsLive tl = ProofFile.Honest.K8.allLive tl := rfl

/-- `k8Share nU` speaks. -/
def shareNo (nU : Array Nat) (t : S) : Bool := (k8Share nU t).isSome

/-- `k8Second` speaks at the state. -/
def secondNo (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => (k8Second q.1 q.2).isSome
  | none => false

/-- **Where `k8Share nU` speaks, one of six tests says yes.** -/
theorem share_split (nU : Array Nat) (t : S) (h : shareNo nU t = true) :
    zeroUnitAt nU t = true ∨ digitsNo t = true ∨ linkedNo t = true ∨ planesNo t = true ∨
      symbolsNo t = true ∨ secondNo t = true := by
  unfold shareNo k8Share at h
  unfold zeroUnitAt digitsNo linkedNo planesNo symbolsNo secondNo
  cases hq : tlForkP.get? t with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    simp only [Option.bind_some] at h ⊢
    cases h1 : selfUnits q.1 nU q.2 with
    | false => exact Or.inl (by unfold zeroUnit; rw [h1]; rfl)
    | true =>
      cases h2 : selfDigits q.1 q.2 with
      | false => exact Or.inr (Or.inl rfl)
      | true =>
        cases h3 : selfLinked q.1 q.2 with
        | false => exact Or.inr (Or.inr (Or.inl rfl))
        | true =>
          cases h4 : selfPlanes q.1 q.2 with
          | false => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | true =>
            cases h5 : selfSymbols q.1 q.2 with
            | false => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            | true =>
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
              have hf : k8First q.1 nU q.2 = none := by
                simp [k8First, h1, h2, h3, h4, h5]
              rw [hf] at h
              simpa using h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The members from the batching on. -/
theorem drop_batch {l : ℕ} (b : Block S Claim)
    (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) :
    c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9)) =
      b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1) := by
  obtain ⟨hK, hbe⟩ := List.getElem?_eq_some_iff.1 hb
  rw [List.drop_eq_getElem_cons hK, hbe]

/-- No member behind the batching has the batching's place. -/
theorem behind_not_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (d : Block S Claim) (hd : d ∈ c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) :
    batchPlace l (if l = 24 then 1 else 0) ≠ d.place := by
  intro e
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hd
  rw [List.getElem?_drop] at hi
  have := batch_place hS hR O hl (n := 14 * l + (if l = 24 then 11 else 9) + 1 + i)
    (by rw [hi]; exact congrArg some e.symm)
  omega

/-- **The first fall's sentence: at typed challenges.** -/
theorem front_fallDebt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (d₂ : RDT)
    (h₂ : OneElem d₂.entry d₂.kind) (ft columns tau : ℕ) (Q : List Fmt.Drawn → S → Prop)
    (hQ : ∀ fr s', Q fr s' → liveOf columns tau s') :
    FallDebt (_root_.Run.ck .two) (k8FrontFall l (if l = 24 then 1 else 0) columns tau) ft b
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d₂] [] Q
      (frontFallShare columns tau).val :=
  fallDebt_of_heldOn _ _ ft b _ [d₂] (batch_round hS hR O hl b hb).symm
    (fun d hd => behind_not_batch hS hR O hl d ((List.takeWhile_prefix _).subset hd))
    (liveOf columns tau) (front_fall_heldOn l _ columns tau d₂ h₂) Q hQ

/-- **The first fall's sentence: at strings of hash blocks.** -/
theorem front_fallDebt_blocks (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (d₂ : RDT)
    (h₂ : OneElem d₂.entry d₂.kind) (hl₂ : d₂.entry.logN ≤ 64) (ft columns tau : ℕ)
    (Q : List Fmt.Drawn → S → Prop) (hQ : ∀ fr s', Q fr s' → liveOf columns tau s') :
    FallDebt (_root_.Run.ckP .two) (k8FrontFall l (if l = 24 then 1 else 0) columns tau) ft b
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d₂] [] Q
      (frontFallShare columns tau).val :=
  fallDebt_of_heldOn _ _ ft b _ [d₂] (batch_round hS hR O hl b hb).symm
    (fun d hd => behind_not_batch hS hR O hl d ((List.takeWhile_prefix _).subset hd))
    (liveOf columns tau) (front_fall_heldOn_blocks l _ columns tau d₂ h₂ hl₂) Q hQ

/-- **The second fall's wide event: the batching's own step returns a state at which `k8Share`
speaks.** -/
theorem share_event (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b)
    (nU : Array Nat) (share : Odds) (ft : ℕ) (s' : S) (dr : Fmt.Drawn)
    (h : localFall [k8ShareFall l (if l = 24 then 1 else 0) nU share] ft
      (b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) s' [dr]) :
    behindT b (shareNo nU) s' [dr] = true := by
  obtain ⟨rs, cols, hrs, hc⟩ := h
  obtain ⟨⟨a, w⟩, hcw⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨i, e, hi, hpl, hfall⟩ := chainFall_at _ ft _ s' _ a w hcw
  obtain ⟨r, rfl, hrd⟩ : ∃ r, rs = [r] ∧ r.drawn = dr := by
    cases rs with
    | nil => simp at hrs
    | cons r t =>
      cases t with
      | nil => exact ⟨r, rfl, by simpa using hrs⟩
      | cons _ _ => simp at hrs
  have hb1 := batch_round hS hR O hl b hb
  have hplace := frontsOf_place ft _ _ _ _ i e hi
  obtain ⟨f, hf, hfp, hft⟩ := ProofFile.Honest.K8.fallOf_mem _ a _ _ w hfall
  obtain rfl := List.mem_singleton.1 hf
  rw [← drop_batch b hb, List.getElem?_drop, hpl, ← hfp] at hplace
  have hi1 : i = 1 := by
    have := quiet_place hS hR O hl hplace
    omega
  subst hi1
  obtain ⟨e₀, b₀, cols', m, g1, g2, -, g4⟩ := frontsOf_step ft _ _ _ _ 0 e hi
  obtain rfl : b = b₀ := Option.some.inj g2
  have hs0 := frontsOf_zero ft _ _ _ _ e₀ g1
  rw [hs0, hb1] at g4
  have g4' : b.step ft s' [r] cols' = .ok (e.2.1, m) := g4
  obtain ⟨-, p, -, -, -, hp, -⟩ := (IM.k9_of hS hR O).2 l hl
  have hd := batch_decl hS hR O hl b hb p hp
  have g5 := step_ft hd (batch_items p) rfl rfl g4'
  rw [behindT_one, ← hrd, g5]
  show (k8Share nU e.2.1).isSome = true
  have hft' : k8Share nU e.2.1 = some w := hft
  rw [hft']
  rfl

/-- **THE JOINT: tests that cover `k8Share`, each with its number, pay the second fall's
sentence.** -/
theorem share_fallDebt_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    (b : Block S Claim) (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) (Ck : CK)
    (d : RDT) (nU : Array Nat) (share : Odds) (ft : ℕ) (tests : List ((S → Bool) × ℝ≥0∞))
    (hsplit : ∀ t, shareNo nU t = true → ∃ x ∈ tests, x.1 t = true)
    (Q : List Fmt.Drawn → S → Prop)
    (hQ : ∀ fr s', Q fr s' → ∀ x ∈ tests,
      Iop.prRho {ρ : Iop.Rho (uLT Ck [d]) | behindT b x.1 s' (drawnT Ck [d] ρ) = true} ≤ x.2) :
    FallDebt Ck (k8ShareFall l (if l = 24 then 1 else 0) nU share) ft b
      (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q (tests.map (·.2)).sum := by
  intro fr s' hq
  refine le_trans (Prob.pr_mono _ ?_) (pr_any_le Ck [d]
    (fun (x : (S → Bool) × ℝ≥0∞) ρ => behindT b x.1 s' (drawnT Ck [d] ρ) = true) (·.2) tests
    (hQ fr s' hq))
  intro ρ hρ
  obtain ⟨a, u⟩ := ρ
  have hρ' : localFall [k8ShareFall l (if l = 24 then 1 else 0) nU share] ft
      (b :: c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) s'
      [Ck.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)] := hρ
  have hev := share_event hS hR O hl b hb nU share ft s' _ hρ'
  rw [behindT_one] at hev
  cases hst : b.step 0 s' [⟨[], Ck.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)⟩] []
    with
  | error x =>
    rw [hst] at hev
    cases hev
  | ok y =>
    obtain ⟨t, m⟩ := y
    rw [hst] at hev
    obtain ⟨x, hx, hxt⟩ := hsplit t hev
    refine ⟨x, hx, ?_⟩
    show behindT b x.1 s' [Ck.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) a)] = true
    rw [behindT_one, hst]
    exact hxt

/-- The state is the end of the verifier's fold over the members in front of the batching, from the
chain's start. -/
def FoldEnd (Z : ProofFile.Pub) (c : Chain S Claim) (l : ℕ) (s' : S) : Prop :=
  ∃ (zp : ProofFile.InstPub) (rs r : List Fmt.RoundView) (cs c' : List Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 11 else 9))) (ProofFile.startS Z zp) rs cs =
      .ok (s', r, c')

/-- **What Q must give of the state in front of the batching**, by name. n₂, n₃, n₄, n₅: numbers
over the data's. -/
structure ShareNeeds (Z : ProofFile.Pub) (c : Chain S Claim) (l n₂ n₃ n₄ n₅ : ℕ) (s' : S) : Prop where
  fold : FoldEnd Z c l s'
  planes : ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    (planesLaid tl && planesLive tl) = true ∧ 3 * tl.bzColumns ≤ n₂
  digits : ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    (digitsLaid tl F' && digitsLive tl) = true ∧ 2 * (tl.zzBlocks * tl.mz) ≤ n₃
  linked : ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    (tiesLaid tl && readsLive tl) = true ∧ linkedCount tl ≤ n₄
  symbols : ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    (symbolsLaid tl && symbolsLive tl) = true ∧ symCount tl ≤ n₅

/-- **The second fall's sentence: at typed challenges.** -/
theorem share_fallDebt (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (n₂ n₃ n₄ n₅ : ℕ) (qS : ℝ≥0∞)
          (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          behindT b secondNo s' (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤ qS) →
        (∀ fr s', Q fr s' → ShareNeeds Z c l n₂ n₃ n₄ n₅ s') →
        FallDebt (_root_.Run.ck .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((n₃ * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((n₄ * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((n₂ * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((n₅ * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (qS + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, hU⟩ := units_of_fold hE hS hR O hl
  obtain ⟨b₂, p₂, hb₂, hp₂, hPl⟩ := count_of_fold planes_from hE hS hR O hl
  obtain ⟨b₃, p₃, hb₃, hp₃, hDg⟩ := count_of_fold digits_from hE hS hR O hl
  obtain ⟨b₄, p₄, hb₄, hp₄, hLi⟩ := count_of_fold linked_from hE hS hR O hl
  obtain ⟨b₅, p₅, hb₅, hp₅, hSy⟩ := count_of_fold symbols_from hE hS hR O hl
  obtain rfl : b = b₂ := Option.some.inj (hb.symm.trans hb₂)
  obtain rfl : b = b₃ := Option.some.inj (hb.symm.trans hb₃)
  obtain rfl : b = b₄ := Option.some.inj (hb.symm.trans hb₄)
  obtain rfl : b = b₅ := Option.some.inj (hb.symm.trans hb₅)
  obtain rfl : p = p₂ := Option.some.inj (hp.symm.trans hp₂)
  obtain rfl : p = p₃ := Option.some.inj (hp.symm.trans hp₃)
  obtain rfl : p = p₄ := Option.some.inj (hp.symm.trans hp₄)
  obtain rfl : p = p₅ := Option.some.inj (hp.symm.trans hp₅)
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 ft share n₂ n₃ n₄ n₅ qS Q hSc hQ
  refine share_fallDebt_of hS hR O hl b hb (_root_.Run.ck .two) d _ share ft
    [(zeroUnitAt (ProofFile.k8NU Bs.G₀ X), _), (digitsNo, _), (linkedNo, _), (planesNo, _),
      (symbolsNo, _), (secondNo, qS)] ?_ Q ?_
  · intro t ht
    rcases share_split _ t ht with h | h | h | h | h | h
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), h⟩
  · intro fr s' hq x hx
    obtain ⟨hfe, n1, n2, n4, n3⟩ := hQ fr s' hq
    obtain ⟨zp, rs, r, cs, c', hfold⟩ := hfe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [behindT_units]
      exact hU d he h5 h6 zp s' rs r cs c' hfold
    · exact hDg d he h5 h6 zp s' n₃ rs r cs c' hfold n2
    · exact hLi d he h5 h6 zp s' n₄ rs r cs c' hfold n4
    · exact hPl d he h5 h6 zp s' n₂ rs r cs c' hfold n1
    · exact hSy d he h5 h6 zp s' n₅ rs r cs c' hfold n3
    · exact hSc fr s' hq

/-- **The second fall's sentence: at strings of hash blocks.** -/
theorem share_fallDebt_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (n₂ n₃ n₄ n₅ : ℕ) (qS : ℝ≥0∞)
          (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          behindT b secondNo s' (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤ qS) →
        (∀ fr s', Q fr s' → ShareNeeds Z c l n₂ n₃ n₄ n₅ s') →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((n₃ * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((n₄ * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((n₂ * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((n₅ * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + (qS + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, hU⟩ := units_of_fold_blocks hE hS hR O hl
  obtain ⟨b₂, p₂, hb₂, hp₂, hPl⟩ := count_of_fold_blocks planes_from hE hS hR O hl
  obtain ⟨b₃, p₃, hb₃, hp₃, hDg⟩ := count_of_fold_blocks digits_from hE hS hR O hl
  obtain ⟨b₄, p₄, hb₄, hp₄, hLi⟩ := count_of_fold_blocks linked_from hE hS hR O hl
  obtain ⟨b₅, p₅, hb₅, hp₅, hSy⟩ := count_of_fold_blocks symbols_from hE hS hR O hl
  obtain rfl : b = b₂ := Option.some.inj (hb.symm.trans hb₂)
  obtain rfl : b = b₃ := Option.some.inj (hb.symm.trans hb₃)
  obtain rfl : b = b₄ := Option.some.inj (hb.symm.trans hb₄)
  obtain rfl : b = b₅ := Option.some.inj (hb.symm.trans hb₅)
  obtain rfl : p = p₂ := Option.some.inj (hp.symm.trans hp₂)
  obtain rfl : p = p₃ := Option.some.inj (hp.symm.trans hp₃)
  obtain rfl : p = p₄ := Option.some.inj (hp.symm.trans hp₄)
  obtain rfl : p = p₅ := Option.some.inj (hp.symm.trans hp₅)
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro d he h5 h6 ft share n₂ n₃ n₄ n₅ qS Q hSc hQ
  refine share_fallDebt_of hS hR O hl b hb (_root_.Run.ckP .two) d _ share ft
    [(zeroUnitAt (ProofFile.k8NU Bs.G₀ X), _), (digitsNo, _), (linkedNo, _), (planesNo, _),
      (symbolsNo, _), (secondNo, qS)] ?_ Q ?_
  · intro t ht
    rcases share_split _ t ht with h | h | h | h | h | h
    · exact ⟨_, List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), h⟩
  · intro fr s' hq x hx
    obtain ⟨hfe, n1, n2, n4, n3⟩ := hQ fr s' hq
    obtain ⟨zp, rs, r, cs, c', hfold⟩ := hfe
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [behindT_units]
      exact hU d he h5 h6 zp s' rs r cs c' hfold
    · exact hDg d he h5 h6 zp s' n₃ rs r cs c' hfold n2
    · exact hLi d he h5 h6 zp s' n₄ rs r cs c' hfold n4
    · exact hPl d he h5 h6 zp s' n₂ rs r cs c' hfold n1
    · exact hSy d he h5 h6 zp s' n₅ rs r cs c' hfold n3
    · exact hSc fr s' hq

end

end P1K8

#print axioms P1K8.dead_markDebt
#print axioms P1K8.dead_markDebt_blocks
#print axioms P1K8.step_ft
#print axioms P1K8.symbolsLive_eq
#print axioms P1K8.shareNo
#print axioms P1K8.secondNo
#print axioms P1K8.share_split
#print axioms P1K8.drop_batch
#print axioms P1K8.behind_not_batch
#print axioms P1K8.front_fallDebt
#print axioms P1K8.front_fallDebt_blocks
#print axioms P1K8.share_event
#print axioms P1K8.share_fallDebt_of
#print axioms P1K8.FoldEnd
#print axioms P1K8.ShareNeeds
#print axioms P1K8.share_fallDebt
#print axioms P1K8.share_fallDebt_blocks
