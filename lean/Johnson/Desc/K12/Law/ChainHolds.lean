-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ChainHolds.lean: the condition of the proximity test (the kind K12) at a place:
what the library's laws that take a chain's blocks off ask at the place's own chain, every premise
named and sorted by who pays.

Definitions, statements and proofs. The laws are `Chain.Holds`: `FoldSem`, `CsSem`, `BaseSem`
(OnBytes/Slice/ChainSem.lean). The chain is `chainFrom` over the place's declared rounds
(Johnson/Desc/K12/Law/ChainOf.lean).
Main names:
  `holds_third`: paid outright, with no fact on codes owed: `pubOk p K = true`, `spendOk p = true`
    and radii below a third of the stages' distances (`thirdRad` is such a choice, by `third_lt`)
    give `Chain.Holds` of the place's standard chain. By the library's `foldSem_of`, `csSem_of`,
    `baseSem_of` with its numbers below a third.
  `Letters.at`, `CodesAt`, `OkOn`, `holds_on`, `okOn_chainFrom`: the chain at four functions for the
    list and the counts, and what the three laws ask of the codes there.
  `K12Condition`: the condition, a structure of four fields. pub: `pubOk p K = true`, public, a
    run's. spend: `spendOk p = true`, public, a run's. codes: `CodesAt`: at each stage but the last
    the radius below the distance, `SumPar.ErrOK` of the fold's four numbers and `LdCode.ListAt` of
    the next stage's tables at the next radius; at the last `BaseCodes`. small: `Err.Below c.err
    εs`: the stages' numbers of positions and the bits of work weigh here and nowhere else.
  `K12Condition.gives`: the condition gives the place's chain c with c.rds the declared rounds as
    written, `stagesOf c` the place's stages, `c.Holds`, `Err.Below c.err εs`, and, by the library's
    `chain_many_list`: where the first claim has no witness at the first radius, the prover has lost
    towards a no of any verdict on the chain's rounds whose yes gives `c.Acc` with all tests of work
    passed.
Limits: (1) This file shows `K12Condition` of no place: codes and small are premises; at εs := ⊤
small says nothing. (2) `holds_third` bounds no error: below a third of the distance the base case's
count is large; it shows that the blocks' premises on the place can be met, not that any numbers are
good. (3) That a yes gives `c.Acc` is the conclusion of the law of the kind under its own premises
on the reading; that all tests of work are passed is shown nowhere in this folder. (4) The incoming
joint, that the claim q and the word y are what the chain in front hands over, is not here. (5) The
yes of `pubOk` and of `spendOk` are runs' words. (6) Where the first fold sends its own mask, the
last conjunct of `gives` cannot be paid as typed: it takes the word z of fresh mask rows as a letter
outside the game, and there z is read off the chain's own first message.
Johnson/Desc/K12/Law/OwnMask.lean has the form in which z is a function of that message. (7) The
verdict is on the chain's rounds alone; the block's verdict also reads the batching's round and the
record, and q hangs on the batching's element, which is drawn before the chain begins and behind y.
(8) `CodesAt [] := True` is never met: pub gives a stage. Nothing on hiding. No soundness of a
release is claimed.

-/
import Johnson.Desc.K12.Law.ChainSpend
import OnBytes.Slice.ManyHolds
import OnBytes.Slice.ManyErr
import OnBytes.Slice.ManyCloses

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK
open scoped ENNReal

/-- Every radius is below a third of its stage's distance (and so the next below a half of the
next's). -/
def Third : {s : Sg} → Chain s → Prop
  | _, .last s e _ _ _ _ _ => 3 * e < s.d
  | _, .step s s' _ _ e _ _ _ _ _ _ _ _ _ next => 3 * e < s.d ∧ 2 * next.rad < s'.d ∧ Third next

theorem SpendPub.sized : ∀ {s : Sg} (c : Chain s), SpendPub c → s.Sized
  | _, .last _ _ _ _ _ _ _, h => h.2
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, h => h.2.1

/-- A chain with Chain.Pub, SpendPub, radii below a third and the library's counts for lists of one
member has each block taken off. By the library's three block laws and its numbers below a third of
the distance. -/
theorem holds_of {K : Codes} : ∀ {s : Sg} (c : Chain s) (cu : IoppStage) (restI : List IoppStage),
    c.Pub K cu restI → SpendPub c → Third c → c.Plain → c.Holds := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro cu restI hP hS hT hE
    obtain ⟨nB, hB⟩ := hP.2.draws
    have hE' : εb = baseErr s e (e + 1) 1 dL dB := hE
    subst hE'
    exact baseSem_of s e (e + 1) 1 dL dB (baseCodes_third hS.2 hT) hS.1 hB
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro cu restI hP hS hT hE
    obtain ⟨nx, later, _, hp, _, _, hN⟩ := hP
    obtain ⟨hF, hs, hSn⟩ := hS
    obtain ⟨h3, h2, hTn⟩ := hT
    obtain ⟨e1, e2, hEn⟩ := hE
    subst e1 e2
    have hn0 : n0 = s.Z.l := hp.n0
    subst hn0
    exact ⟨foldSem_of s s.Z.l s.d e _ _ _ _ (Sg.codesOK hs (by omega)) (foldNums_third hs h3) dE dT
        hF,
      csSem_of hf e next.rad 1 (Sg.fit_cMid hs).laws (Sg.list_cIn (SpendPub.sized next hSn) h2) dS
          dC
        hp.rounds, ih nx later hN hSn hTn hEn⟩

/-! ## The place's chain at the greatest radii below a third -/

/-- The greatest radius below a third of the stage's distance. -/
def thirdRad (s : Sg) : ℕ := (s.d - 1) / 3

theorem d_pos (s : Sg) : 0 < s.d := by
  unfold Sg.d Sg.dC Sg.dZ
  exact lt_min (Nat.succ_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos _))

theorem third_lt (s : Sg) : 3 * thirdRad s < s.d := by
  have := d_pos s
  unfold thirdRad
  omega

theorem rad_chainFrom (X : Letters) : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage) (l : List WR)
    (c : Chain (sgOf a)), chainFrom X rest a l = some c → c.rad = X.rad (sgOf a)
  | [], a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · cases hc; rfl
    · cases hc
  | b :: rest, a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · split at hc
      · split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom X rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            split <;> rfl
        · cases hc
      · cases hc
    · cases hc

theorem std_chainFrom (rad : Sg → ℕ) (h3 : ∀ s, 3 * rad s < s.d) : ∀ (rest : List Fmt.M1.Stage)
    (a : Fmt.M1.Stage)
    (l : List WR) (c : Chain (sgOf a)), chainFrom (.std rad) rest a l = some c → Third c ∧ c.Plain
  | [], a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      exact ⟨h3 _, rfl⟩
    · cases hc
  | b :: rest, a, l, c, hc => by
    unfold chainFrom at hc
    split at hc
    · split at hc
      · split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom (.std rad) rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            obtain ⟨i1, i2⟩ := std_chainFrom rad h3 rest b l'' next hn
            have hr : 2 * next.rad < (sgOf b).d := by
              rw [rad_chainFrom _ rest b l'' next hn]
              have := h3 (sgOf b)
              show 2 * rad (sgOf b) < _
              omega
            split
            · exact ⟨⟨h3 _, hr, i1⟩, rfl, rfl, i2⟩
            · exact ⟨⟨h3 _, hr, i1⟩, rfl, rfl, i2⟩
        · cases hc
      · cases hc
    · cases hc

/-- At a place: pubOk's and spendOk's yes give the place's standard chain, at any radii below a
third of the stages' distances, with each block taken off (Chain.Holds). -/
theorem holds_third (rad : Sg → ℕ) (h3 : ∀ s, 3 * rad s < s.d) (p : P12) (K : Codes)
    (hp : pubOk p K = true) (hs : spendOk p = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.std rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧ stagesOf c = p.nums.stages ∧
      c.rad = rad (sgOf a) ∧ c.Holds := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩ := pub_of_ok (.std rad) p K hp
  obtain ⟨cu, restI, f1, f2⟩ : ∃ cu restI, stageAt p 0 a = some cu ∧ stagesAt p 1 rest = some restI
      := by
    unfold pubOk pubL at hp
    rw [e1, e2] at hp
    exact walk_forms p K rest 0 a l hp
  obtain ⟨t1, t2⟩ := std_chainFrom rad h3 rest a l c e3
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, rad_chainFrom _ rest a l c e3,
    holds_of c cu restI (e6 a rest cu restI e1 f1 f2) (spend_of_ok _ p hs a rest w0 l c e1 e2 e3) t1
        t2⟩

/-! ## At any radii: the facts on codes as named premises -/

/-- The letters of four functions of a stage and a radius (a list's size; the counts for the main
rows, the carried and the fresh mask rows) and a radius for each stage: the error counts that the
library's three block laws are stated at. -/
noncomputable def Letters.at (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) : Letters where
  rad := rad
  εb := fun s dL dB => baseErr s (rad s) (mC s (rad s) + mS s (rad s)) (L s (rad s)) dL dB
  εf := fun s dE dT => foldErr s dE dT (fun _ => L s (rad s)) (fun _ => mC s (rad s))
    (fun _ => mS s (rad s)) (fun _ => mW s (rad s))
  εc := fun s s' hf dS dC => csErr hf (rad s) (L s' (rad s')) dS dC

/-- The facts on codes that the three block laws ask, stage by stage, at the place's stages. No fact
on a place's rounds is among them. -/
def CodesAt (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) : List Fmt.M1.Stage → Prop
  | [] => True
  | [a] => BaseCodes (sgOf a) (rad (sgOf a))
      (mC (sgOf a) (rad (sgOf a)) + mS (sgOf a) (rad (sgOf a)))
      (L (sgOf a) (rad (sgOf a)))
  | a :: b :: rest =>
    rad (sgOf a) < (sgOf a).d ∧
    ((sgOf a).par 0).ErrOK (rad (sgOf a)) (fun _ => L (sgOf a) (rad (sgOf a)))
      (fun _ => mC (sgOf a) (rad (sgOf a))) (fun _ => mS (sgOf a) (rad (sgOf a)))
      (fun _ => mW (sgOf a) (rad (sgOf a))) ∧
    (sgOf b).cIn.ListAt (rad (sgOf b)) (L (sgOf b) (rad (sgOf b))) ∧
    CodesAt L mC mS mW rad (b :: rest)

/-- The same on a chain, with «the chain's counts are the letters'». -/
def OkOn (L mC mS mW : Sg → ℕ → ℕ) : {s : Sg} → Chain s → Prop
  | _, .last s e dL dB _ _ εb =>
    εb = baseErr s e (mC s e + mS s e) (L s e) dL dB ∧ BaseCodes s e (mC s e + mS s e) (L s e)
  | _, .step s s' hf _ e dE dT dS dC _ _ _ εf εc next =>
    εf = foldErr s dE dT (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e) (fun _ => mW s e) ∧
    εc = csErr hf e (L s' next.rad) dS dC ∧ e < s.d ∧
    (s.par 0).ErrOK e (fun _ => L s e) (fun _ => mC s e) (fun _ => mS s e) (fun _ => mW s e) ∧
    s'.cIn.ListAt next.rad (L s' next.rad) ∧ OkOn L mC mS mW next

/-- Chain.Pub, SpendPub and the facts on codes give Chain.Holds. -/
theorem holds_on {K : Codes} (L mC mS mW : Sg → ℕ → ℕ) : ∀ {s : Sg} (c : Chain s) (cu : IoppStage)
    (restI : List IoppStage), c.Pub K cu restI → SpendPub c → OkOn L mC mS mW c → c.Holds := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro cu restI hP hS hO
    obtain ⟨nB, hB⟩ := hP.2.draws
    obtain ⟨hE, hc⟩ := hO
    subst hE
    exact baseSem_of s e _ _ dL dB hc hS.1 hB
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro cu restI hP hS hO
    obtain ⟨nx, later, _, hp, _, _, hN⟩ := hP
    obtain ⟨hF, hs, hSn⟩ := hS
    obtain ⟨e1, e2, he, hE, hl, hOn⟩ := hO
    subst e1 e2
    have hn0 : n0 = s.Z.l := hp.n0
    subst hn0
    exact ⟨foldSem_of s s.Z.l s.d e _ _ _ _ (Sg.codesOK hs he) hE dE dT hF,
      csSem_of hf e next.rad _ (Sg.fit_cMid hs).laws hl dS dC hp.rounds, ih nx later hN hSn hOn⟩

theorem okOn_chainFrom (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) : ∀ (rest : List Fmt.M1.Stage)
    (a : Fmt.M1.Stage)
    (l : List WR) (c : Chain (sgOf a)), chainFrom (.at L mC mS mW rad) rest a l = some c →
    CodesAt L mC mS mW rad (a :: rest) → OkOn L mC mS mW c
  | [], a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · cases hc
      exact ⟨rfl, h⟩
    · cases hc
  | b :: rest, a, l, c, hc, h => by
    unfold chainFrom at hc
    split at hc
    · split at hc
      · split at hc
        · rename_i dS dC l'' hd
          cases hn : chainFrom (.at L mC mS mW rad) rest b l'' with
          | none => rw [hn] at hc; cases hc
          | some next =>
            rw [hn] at hc
            have hc' := Option.some.inj hc
            subst hc'
            obtain ⟨h1, h2, h3, h4⟩ := h
            have ih := okOn_chainFrom L mC mS mW rad rest b l'' next hn h4
            have hr : next.rad = rad (sgOf b) := rad_chainFrom _ rest b l'' next hn
            split
            · exact ⟨rfl, by rw [hr]; rfl, h1, h2, by rw [hr]; exact h3, ih⟩
            · exact ⟨rfl, by rw [hr]; rfl, h1, h2, by rw [hr]; exact h3, ih⟩
        · cases hc
      · cases hc
    · cases hc

/-- **The condition of the kind K12 at a place**, every premise named and sorted by who pays. L mC
mS mW rad: the letters. K: the record's codes in front of the test. εs: the bound on each round's
share of bad challenge values. -/
structure K12Condition (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (p : P12) (K : Codes) (εs : ℝ≥0∞) :
    Prop where
  /-- Public, a run's: every clause of Chain.Pub and CsFit at the place's declared rounds, stages
      and
K -/
  pub : pubOk p K = true
  /-- Public, a run's: FoldRounds · the base case's first round · Sized -/
  spend : spendOk p = true
  /-- The codes': radii below the distances · ErrOK · ListAt · BaseCodes at the place's stages -/
  codes : CodesAt L mC mS mW rad p.nums.stages
  /-- The numbers': each error count of the place's chain is at most εs as a share of its round's
challenge values. The stages' numbers of positions t and the bits of work weigh here and nowhere
else -/
  small : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR)
      (c : Chain (sgOf a)),
    p.nums.stages = a :: rest → writtenOf p.nums = some (w0 :: l) →
    chainFrom (.at L mC mS mW rad) rest a l = some c → Err.Below c.err εs

/-- What the condition buys: the place's chain over its declared rounds, each block taken off, every
count small; and so, by the library's chain_many_list: where the first claim q on the word y has no
witness at the first radius, the prover has lost towards a no of any verdict on the chain's rounds
whose yes gives the chain's yes in the field with all tests of work passed. -/
theorem K12Condition.gives {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {p : P12} {K : Codes}
    {εs : ℝ≥0∞}
    (h : K12Condition L mC mS mW rad p K εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom (.at L mC mS mW rad) rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧ c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (q : GE × ((sgOf a).cIn.J → GE)) (y : (sgOf a).cIn.Word) (z : (sgOf a).cFr.Word)
        (g : (sgOf a).cIn.Word), (∀ w, ¬ (sgOf a).RIn c.rad (q, y) w) →
        ∀ acc : Tr (PQ.uL (ckP .two) c.rds) → Bool,
          (∀ b, acc (c.trL b) = true → c.Acc q y z g b ∧
            PQ.passSL (ckP .two) c.rds (PQ.rhoSL (ckP .two) c.rds (c.trL b)) = true) →
          Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ => acc τ = false := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩ := pub_of_ok (.at L mC mS mW rad) p K h.pub
  obtain ⟨cu, restI, f1, f2⟩ : ∃ cu restI, stageAt p 0 a = some cu ∧ stagesAt p 1 rest = some restI
      := by
    have hp := h.pub
    unfold pubOk pubL at hp
    rw [e1, e2] at hp
    exact walk_forms p K rest 0 a l hp
  have hH : c.Holds := holds_on L mC mS mW c cu restI (e6 a rest cu restI e1 f1 f2)
    (spend_of_ok _ p h.spend a rest w0 l c e1 e2 e3)
    (okOn_chainFrom L mC mS mW rad rest a l c e3 (e1 ▸ h.codes))
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, rad_chainFrom _ rest a l c e3, hH,
    h.small a rest w0 l c e1 e2 e3, fun q y z g hno acc hacc => chain_many_list c hH q y z g hno acc
        hacc⟩

end H2K.Pub
